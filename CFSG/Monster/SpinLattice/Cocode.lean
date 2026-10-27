module

public import CFSG.Monster.SpinLattice.Lambda
public import CFSG.Monster.Spin.Pairing

public section

namespace CFSG.Monster.SpinLattice

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin

@[expose] noncomputable def lamCocode : Cocode →ₗ[ZMod 2] L2 := C.liftQ lamVecLin le_ker_lamVecLin

theorem lamCocode_mk (x : Fin 24 → ZMod 2) : lamCocode (Submodule.Quotient.mk x) = lamVec x := rfl

@[expose] def lamX (a : C) : L2 := lamCodeCls a.2

@[expose] noncomputable def lamT (a : C) : L2 := lamX a + lamCocode (thetaD a)

private theorem add_self' (x : L2) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem lamCocode_Acocode (a b : C) : lamCocode (Acocode a b) = lamVec ((a : Fin 24 → ZMod 2) * b) :=
  rfl

theorem lamX_add (a b : C) :
    lamX (a + b) = lamX a + lamX b + lamVec ((a : Fin 24 → ZMod 2) * b) := by
  have h := lamCodeCls_add a.2 b.2
  rw [lamX, lamX, lamX, h, add_assoc, add_self', add_zero]

theorem lamT_add (a b : C) : lamT (a + b) = lamT a + lamT b := by
  rw [lamT, lamT, lamT, thetaD_add, map_add, map_add, lamCocode_Acocode, lamX_add]
  have h := add_self' (lamVec ((a : Fin 24 → ZMod 2) * b))
  calc lamX a + lamX b + lamVec (↑a * ↑b) +
        (lamCocode (thetaD a) + lamCocode (thetaD b) + lamVec (↑a * ↑b)) =
      lamX a + lamCocode (thetaD a) + (lamX b + lamCocode (thetaD b)) +
        (lamVec (↑a * ↑b) + lamVec (↑a * ↑b)) := by abel
    _ = _ := by rw [h, add_zero]

theorem qL_lamCocode (δ : Cocode) : qL (lamCocode δ) = 0 := by
  induction δ using Submodule.Quotient.induction_on with | H x => exact qL_lamVec x

theorem bL_lamCocode_lamCocode (δ ε : Cocode) :
    QuadraticMap.polarBilin qL (lamCocode δ) (lamCocode ε) = 0 := by
  induction δ using Submodule.Quotient.induction_on with | H x => ?_
  induction ε using Submodule.Quotient.induction_on with | H y => exact bL_lamVec_lamVec x y

theorem bL_lamX_lamCocode (a : C) (δ : Cocode) :
    QuadraticMap.polarBilin qL (lamX a) (lamCocode δ) = pair a δ := by
  induction δ using Submodule.Quotient.induction_on with | H x =>
    exact bL_lamCodeCls_lamVec a.2 x

theorem qL_lamX (a : C) : qL (lamX a) = P a := qL_lamCodeCls a.2

theorem bL_lamX_lamX (a b : C) : QuadraticMap.polarBilin qL (lamX a) (lamX b) = K a b :=
  bL_lamCodeCls_lamCodeCls a.2 b.2

private theorem polarBilin_symm' (x y : L2) :
    QuadraticMap.polarBilin qL x y = QuadraticMap.polarBilin qL y x := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]

private theorem qL_add (x y : L2) : qL (x + y) = qL x + qL y + QuadraticMap.polarBilin qL x y := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  ring

theorem qL_lamT (a : C) : qL (lamT a) = 0 := by
  rw [lamT, qL_add, qL_lamX, qL_lamCocode, bL_lamX_lamCocode, pair_self_thetaD, add_zero]
  generalize P (a : Fin 24 → ZMod 2) = x
  revert x
  decide

theorem bL_lamT_lamT (a b : C) : QuadraticMap.polarBilin qL (lamT a) (lamT b) = 0 := by
  rw [lamT, lamT, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
    bL_lamX_lamX, bL_lamX_lamCocode, polarBilin_symm' (lamCocode _) (lamX b),
    bL_lamX_lamCocode, bL_lamCocode_lamCocode, pair_thetaD, pair_thetaD, add_zero]
  have h := θ_add_θ_swap a b
  rw [← h]
  generalize θ a b = x
  generalize θ b a = y
  revert x y
  decide

theorem bL_lamT_lamCocode (a : C) (δ : Cocode) :
    QuadraticMap.polarBilin qL (lamT a) (lamCocode δ) = pair a δ := by
  rw [lamT, map_add, LinearMap.add_apply, bL_lamX_lamCocode, bL_lamCocode_lamCocode, add_zero]

@[expose] noncomputable def lamTHom : C →+ L2 where
  toFun := lamT
  map_zero' := by
    have h := lamT_add 0 0
    rw [add_zero] at h
    exact left_eq_add.1 h
  map_add' := lamT_add

@[expose] noncomputable def phi0 : C × Cocode →ₗ[ZMod 2] L2 :=
  (AddMonoidHom.toZModLinearMap 2 lamTHom).coprod lamCocode

theorem phi0_apply (a : C) (δ : Cocode) : phi0 (a, δ) = lamT a + lamCocode δ := rfl

theorem qL_phi0 (a : C) (δ : Cocode) : qL (phi0 (a, δ)) = pair a δ := by
  rw [phi0_apply, qL_add, qL_lamT, qL_lamCocode, bL_lamT_lamCocode, zero_add, zero_add]

theorem bL_phi0 (a b : C) (δ ε : Cocode) :
    QuadraticMap.polarBilin qL (phi0 (a, δ)) (phi0 (b, ε)) = pair a ε + pair b δ := by
  rw [phi0_apply, phi0_apply, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
    bL_lamT_lamT, bL_lamT_lamCocode, polarBilin_symm' (lamCocode δ) (lamT b),
    bL_lamT_lamCocode, bL_lamCocode_lamCocode, zero_add, add_zero, add_comm]

theorem phi0_injective : Function.Injective phi0 := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨a, δ⟩ h
  have h1 : ∀ ε : Cocode, pair a ε = 0 := by
    intro ε
    have := bL_phi0 a 0 δ ε
    rw [h, map_zero, LinearMap.zero_apply, pair_zero_left, add_zero] at this
    exact this.symm
  have h2 : ∀ u : C, pair u δ = 0 := by
    intro u
    have := bL_phi0 a u δ 0
    rw [h, map_zero, LinearMap.zero_apply, pair_zero_right, zero_add] at this
    exact this.symm
  rw [eq_zero_of_forall_pair_left h1, eq_zero_of_forall_pair h2]
  rfl

theorem phi0_bijective : Function.Bijective phi0 := by
  have : Module.Finite ℤ (codeLatticeSubgroup (C := C) allOnes_mem_C) :=
    Module.Finite.of_basis (Classical.choice (nonempty_basis_codeLattice allOnes_mem_C
      weight_mod_four' mem_C_iff_forall_dotProduct))
  refine ⟨phi0_injective, ?_⟩
  have hdim : Module.finrank (ZMod 2) (C × Cocode) = Module.finrank (ZMod 2) L2 := by
    rw [Module.finrank_prod, finrank_cocode, finrank_codeLatticeModTwo allOnes_mem_C
      weight_mod_four' mem_C_iff_forall_dotProduct, finrank_C]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 phi0_injective

@[expose] noncomputable def phi0Equiv : (C × Cocode) ≃ₗ[ZMod 2] L2 :=
  LinearEquiv.ofBijective phi0 phi0_bijective

theorem phi0_thetaD (a : C) : phi0 (a, thetaD a) = lamX a := by
  rw [phi0_apply, lamT, add_assoc, add_self', add_zero]

theorem lamVec_eq_sum (v : Fin 24 → ZMod 2) :
    lamVec v = ∑ i, v i • lamVec (Pi.single i 1) := by
  rw [← lamVecLin_apply]
  conv_lhs => rw [show v = ∑ i, v i • (Pi.single i (1 : ZMod 2) : Fin 24 → ZMod 2) by
    funext k; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum]
  simp only [map_smul, lamVecLin_apply]

end CFSG.Monster.SpinLattice
