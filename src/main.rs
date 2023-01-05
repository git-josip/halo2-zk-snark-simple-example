extern crate core;

use halo2_proofs::circuit::{AssignedCell, Chip, Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::pasta::{EqAffine, Fp};
use halo2_proofs::plonk::{Advice, Circuit, Column, ConstraintSystem, create_proof, Error, Fixed, Instance, keygen_pk, keygen_vk, Selector, SingleVerifier, verify_proof};
use halo2_proofs::poly::commitment::Params;
use halo2_proofs::poly::Rotation;
use halo2_proofs::transcript::{Blake2bRead, Blake2bWrite, Challenge255};
use rand::rngs::OsRng;

//   column_a   column_b  column_mul column_sum
//      a           b        m          s
//      ___________________________________
//      x           x        1          0         multiply columns a*b = X*x = x^2, and store result in first column of next row.
//      x^2         x        1          0         multiply columns a*b = x^2 * x = x^3,  and store result in first column of next row.
//      x^3         x        0          1         sum columns a+b = x^3 + x,  and store result in first column of next row.
//      x^3 + x     5        0          1         sum columns a+b = x^3 + x + 5,  and store result in first column of next row.
//  =  x^3 + x + 5

trait Ops {
    type Num;

    fn load_private(&self, layouter: impl Layouter<Fp>, v: Option<Fp>) -> Result<Self::Num, Error>;
    fn load_constant(&self, layouter: impl Layouter<Fp>, v: Fp) -> Result<Self::Num, Error>;

    fn mul(&self, layouter: impl Layouter<Fp>, a: Self::Num, b: Self::Num) -> Result<Self::Num, Error>;
    fn add(&self, layouter: impl Layouter<Fp>, a: Self::Num, b: Self::Num) -> Result<Self::Num, Error>;

    fn expose_public(&self, layouter: impl Layouter<Fp>, num: Self::Num, row: usize) -> Result<(), Error>;
}

struct MyChip {
    config: MyConfig,
}

impl MyChip {
    fn configure(meta: &mut ConstraintSystem<Fp>, advice_col: [Column<Advice>; 2], instance_col: Column<Instance>, constant_col: Column<Fixed>) -> MyConfig {
        meta.enable_constant(constant_col);
        meta.enable_equality(instance_col);

        for adv in advice_col.iter() {
            meta.enable_equality(*adv);
        }

        let s_mul = meta.selector();
        let s_add = meta.selector();

        meta.create_gate("mul/add", |meta| {
            let lhs = meta.query_advice(advice_col[0], Rotation::cur());
            let rhs = meta.query_advice(advice_col[1], Rotation::cur());
            let out = meta.query_advice(advice_col[0], Rotation::next());

            let s_mul = meta.query_selector(s_mul);
            let s_add = meta.query_selector(s_add);

            vec![s_mul * (lhs.clone() * rhs.clone() - out.clone()), s_add * (lhs + rhs - out)]
        });


        MyConfig {
            advice: advice_col,
            instance: instance_col,
            s_mul,
            s_add
        }
    }
}

impl Chip<Fp> for MyChip {
    type Config = MyConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl Ops for MyChip {
    type Num = AssignedCell<Fp, Fp>;

    fn load_private(&self, mut layouter: impl Layouter<Fp>, v: Option<Fp>) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(|| "load private", | mut region| {
            region.assign_advice(|| "private value", config.advice[0], 0, || Value::known(v.ok_or(Error::Synthesis).unwrap()))
        })
    }

    fn load_constant(&self, mut layouter: impl Layouter<Fp>, v: Fp) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(|| "load constant", | mut region| {
            region.assign_advice_from_constant(|| "constant", config.advice[0], 0, v)
        })
    }

    fn mul(&self, mut layouter: impl Layouter<Fp>, a: Self::Num, b: Self::Num) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "mul",
            |mut region| {
                // We only want to use a single multiplication gate in this region,
                // so we enable it at region offset 0; this means it will constrain
                // cells at offsets 0 and 1.
                config.s_mul.enable(&mut region, 0)?;

                // The inputs we've been given could be located anywhere in the circuit,
                // but we can only rely on relative offsets inside this region. So we
                // assign new cells inside the region and constrain them to have the

                // same values as the inputs.
                a.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
                b.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;

                // Now we can assign the multiplication result, which is to be assigned
                // into the output position.
                let value = a.value().and_then(|a| b.value().map(|b| *a * *b));

                // Finally, we do the assignment to the output, returning a
                // variable to be used in another part of the circuit.
                region
                    .assign_advice(|| "lhs * rhs", config.advice[0], 1, || value)
            },
        )
    }

    fn add(&self, mut layouter: impl Layouter<Fp>, a: Self::Num, b: Self::Num) -> Result<Self::Num, Error> {
        let config = self.config();

        layouter.assign_region(
            || "add",
            |mut region| {
                // We only want to use a single multiplication gate in this region,
                // so we enable it at region offset 0; this means it will constrain
                // cells at offsets 0 and 1.
                config.s_add.enable(&mut region, 0)?;

                // The inputs we've been given could be located anywhere in the circuit,
                // but we can only rely on relative offsets inside this region. So we
                // assign new cells inside the region and constrain them to have the

                // same values as the inputs.
                a.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
                b.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;

                // Now we can assign the multiplication result, which is to be assigned
                // into the output position.
                let value = a.value().and_then(|a| b.value().map(|b| *a + *b));

                // Finally, we do the assignment to the output, returning a
                // variable to be used in another part of the circuit.
                region
                    .assign_advice(|| "lhs + rhs", config.advice[0], 1, || value)
            },
        )
    }

    fn expose_public(&self, mut layouter: impl Layouter<Fp>, num: Self::Num, row: usize) -> Result<(), Error> {
        let config = self.config();

        layouter.constrain_instance(num.cell(), config.instance, row)
    }
}

impl MyChip {
    fn new(config: MyConfig) -> Self {
        MyChip {
            config,
        }
    }
}

#[derive(Clone, Debug)]
struct MyConfig {
    advice: [Column<Advice>; 2],
    instance: Column<Instance>,
    s_mul: Selector,
    s_add: Selector
}

#[derive(Default)]
struct MyCircuit {
    constant: Fp,
    x: Option<Fp>
}

impl Circuit<Fp> for MyCircuit {
    type Config = MyConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fp>) -> MyConfig {
        // We create the two advice columns that MyChip uses for I/O of private inputs
        let advice = [meta.advice_column(), meta.advice_column()];

        // We also need an instance column to store public inputs.
        let instance = meta.instance_column();

        // Create a fixed column to load constants.
        let constant = meta.fixed_column();


        MyChip::configure(meta, advice, instance, constant)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<Fp>) -> Result<(), Error> {
        let chip = MyChip::new(config);

        let x = chip.load_private(layouter.namespace(|| "load x"), self.x)?;
        let constant = chip.load_constant(layouter.namespace(|| "load constant"), self.constant)?;

        let x2 = chip.mul(layouter.namespace(|| "x2"), x.clone(), x.clone())?;
        let x3 = chip.mul(layouter.namespace(|| "x3"), x2, x.clone())?;

        let x3_x = chip.add(layouter.namespace(|| "x3 + x"), x3, x)?;
        let x3_x_constant = chip.add(layouter.namespace(|| "x3 + x + c"), x3_x, constant)?;

        chip.expose_public(layouter.namespace(|| "x3 + x + c"), x3_x_constant, 0)
    }
}

//with MockProver
// fn main() {
//     let x = Fp::from(3);
//     let constant = Fp::from(5);
//     let result = Fp::from(35);
//
//     let circuit = MyCircuit {
//         constant,
//         x: Some(x)
//     };
//
//     let public_inputs = vec![result];
//
//     let prover = halo2_proofs::dev::MockProver::run(4, &circuit, vec![public_inputs]).unwrap();
//     assert_eq!(prover.verify(), Ok(()));
//
//     // Create the area you want to draw on.
//     // Use SVGBackend if you want to render to .svg instead.
//     use plotters::prelude::*;
//     let root = BitMapBackend::new("layout.png", (1024, 768)).into_drawing_area();
//     root.fill(&WHITE).unwrap();
//     let root = root
//         .titled("Example Circuit Layout", ("sans-serif", 60))
//         .unwrap();
//
//     halo2_proofs::dev::CircuitLayout::default()
//         // You can optionally render only a section of the circuit.
//         .view_width(0..2)
//         .view_height(0..16)
//         // You can hide labels, which can be useful with smaller areas.
//         .show_labels(false)
//         // Render the circuit onto your area!
//         // The first argument is the size parameter for the circuit.
//         .render(5, &circuit, &root)
//         .unwrap();
// }


// without mock HALO2 proof
fn main() {
    let x = Fp::from(3);
    let constant = Fp::from(5);
    let result = Fp::from(35);

    let circuit = MyCircuit {
        constant,
        x: Some(x)
    };

    let public_input = vec![result];


    // Initialize the polynomial commitment parameters
    const K: u32 = 5;
    let params: Params<EqAffine> = Params::new(K);
    let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &circuit).expect("keygen_pk should not fail");


    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    // Create a proof
    create_proof(
        &params,
        &pk,
        &[circuit],
        &[&[&[result]]],
        OsRng,
        &mut transcript,
    ).unwrap();


    let proof: Vec<u8> = transcript.finalize();

    println!("Proof len: {}", proof.len());

    std::fs::write("./plonk_api_proof.bin", &proof[..])
        .expect("should succeed to write new proof");

    // Check that a hardcoded proof is satisfied
    let proof =
        std::fs::read("./plonk_api_proof.bin").expect("should succeed to read proof");
    let strategy = SingleVerifier::new(&params);
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);

    // happy path
    assert!(
        verify_proof(
            &params,
        pk.get_vk(),
            strategy,
            &[&[&public_input[..]]],
            &mut transcript,
        )
            .is_ok());


    // unhappy path
    let public_input_invalid = vec![Fp::from(36)];
    assert!(
        verify_proof(
            &params,
            pk.get_vk(),
            SingleVerifier::new(&params),
            &[&[&public_input_invalid[..]]],
            &mut transcript,
        )
            .is_err());

}
