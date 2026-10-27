module

public import CFSG.RankThree.Chevalley.SteinbergCEF4OrderThree

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 RootSpace

namespace F4Weyl

@[expose] def f4PhiSix : WeylGroup .F4 := f4Coxeter ^ 10

theorem weylMatrix_f4PhiSix : weylMatrix f4PhiSix = -f4OrderThreeMatrix := by
  rw [f4PhiSix, weylMatrix_pow, weylMatrix_f4Coxeter]
  decide

theorem f4PhiSix_smul (v : Fin Tag.F4.rank → ℤ) : f4PhiSix • v = -((f4Coxeter ^ 4) • v) := by
  rw [← weylMatrix_mulVec, ← weylMatrix_mulVec, weylMatrix_f4PhiSix, weylMatrix_f4OrderThree,
    Matrix.neg_mulVec]

theorem f4PhiSixMatrix_relation :
    weylMatrix f4PhiSix * weylMatrix f4PhiSix - weylMatrix f4PhiSix + 1 = 0 := by
  rw [weylMatrix_f4PhiSix]
  decide

theorem orderOf_f4PhiSix : orderOf f4PhiSix = 6 := by
  have hpow : ∀ k : ℕ, weylMatrix (f4PhiSix ^ k) = (-f4OrderThreeMatrix) ^ k := fun k => by
    rw [weylMatrix_pow, weylMatrix_f4PhiSix]
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨?_, fun m hm hm0 h => ?_⟩
  · apply weylMatrix_injective
    rw [hpow, weylMatrix_one]
    decide
  · have h1 := congrArg weylMatrix h
    rw [hpow, weylMatrix_one] at h1
    interval_cases m <;> revert h1 <;> decide

theorem weylAct_f4PhiSix (x : RootSpace .F4) :
    weylAct .F4 f4PhiSix x = -weylAct .F4 (f4Coxeter ^ 4) x := by
  have h : (weylAct .F4 f4PhiSix).toLinearEquiv.toLinearMap =
      -(weylAct .F4 (f4Coxeter ^ 4)).toLinearEquiv.toLinearMap := by
    refine (basis .F4).ext fun k => ?_
    simp only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, LinearMap.neg_apply,
      basis_apply, weylAct_ofLattice, f4PhiSix_smul, ofLattice_neg]
  exact congrArg (fun f : RootSpace .F4 →ₗ[ℝ] RootSpace .F4 => f x) h

theorem weylAct_conj_f4PhiSix (u : WeylGroup .F4) (x : RootSpace .F4) :
    weylAct .F4 (u * f4PhiSix * u⁻¹) x = -weylAct .F4 (u * f4Coxeter ^ 4 * u⁻¹) x := by
  rw [weylAct_mul_apply, weylAct_mul_apply, weylAct_f4PhiSix, map_neg, ← weylAct_mul_apply,
    ← weylAct_mul_apply]

theorem dualMatrix_f4PhiSix (R : Type*) [CommRing R] :
    dualMatrix R f4PhiSix = -dualMatrix R (f4Coxeter ^ 4) := by
  rw [dualMatrix, dualMatrix, weylMatrix_f4PhiSix, weylMatrix_f4OrderThree, Matrix.map_neg _
    Int.cast_neg, Matrix.transpose_neg]

@[expose] def f4PhiSixBasis : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  !![1, 0, 0, 1; 0, -1, 0, 1; 0, -2, 1, 2; 0, 0, 0, 1]

@[expose] def f4PhiSixCoord : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  !![1, 0, 0, -1; 0, -1, 0, 1; 0, -2, 1, 0; 0, 0, 0, 1]

theorem f4PhiSixCoord_mul : f4PhiSixCoord * f4PhiSixBasis = 1 := by decide

theorem mul_f4PhiSixCoord : f4PhiSixBasis * f4PhiSixCoord = 1 := by decide

theorem f4PhiSixBasis_eq :
    f4PhiSixBasis = Matrix.of fun (i j : Fin Tag.F4.rank) =>
      (![Pi.single (f4Index 0) 1, f4PhiSix • Pi.single (f4Index 0) 1,
        Pi.single (f4Index 2) 1, f4PhiSix • Pi.single (f4Index 2) 1] :
          Fin 4 → Fin Tag.F4.rank → ℤ) j i := by
  rw [← weylMatrix_mulVec, ← weylMatrix_mulVec, weylMatrix_f4PhiSix]
  decide

theorem det_f4PhiSixBasis : f4PhiSixBasis.det = -1 := by
  have h : detLaplace 4 f4PhiSixBasis = -1 := by decide
  exact (detLaplace_eq_det 4 f4PhiSixBasis).symm.trans h

@[expose] def negUnitPhiSix {p : ℕ} {q : ZMod p} (hq : q ^ 2 - q + 1 = 0) : (ZMod p)ˣ :=
  ⟨-q, q ^ 2, by linear_combination (-q - 1) * hq, by linear_combination (-q - 1) * hq⟩

theorem coe_negUnitPhiSix {p : ℕ} {q : ZMod p} (hq : q ^ 2 - q + 1 = 0) :
    ((negUnitPhiSix hq : (ZMod p)ˣ) : ZMod p) = -q :=
  rfl

theorem orderOf_negUnitPhiSix {p : ℕ} (hp3 : 3 < p) {q : ZMod p} (hq : q ^ 2 - q + 1 = 0) :
    orderOf (negUnitPhiSix hq) = 3 := by
  have three : (3 : ZMod p) ≠ 0 := by
    intro h
    have h1 : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h1
    exact absurd (Nat.le_of_dvd (by norm_num) h1) (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcube : (-q) ^ 3 = 1 := by linear_combination (-q - 1) * hq
  refine orderOf_eq_prime (Units.ext ?_) fun h => three ?_
  · rw [Units.val_pow_eq_pow_val, coe_negUnitPhiSix, Units.val_one]
    exact hcube
  · have h1 : -q = 1 := by
      have h2 := congrArg Units.val h
      rwa [coe_negUnitPhiSix, Units.val_one] at h2
    linear_combination hq + (q - 2) * h1

theorem F4_phiSix_charRootKernel {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {q : ZMod p}
    (hq : q ^ 2 - q + 1 = 0) {v : Fin Tag.F4.rank → ZMod p} (hv : v ≠ 0)
    (heig : (dualMatrix (ZMod p) f4PhiSix).mulVec v = q • v) :
    charRootKernel v = ∅ ∨
      ∃ (u : WeylGroup .F4) (i j : Fin Tag.F4.rank) (ε : ℤ),
        ((i = f4Index 0 ∧ j = f4Index 1) ∨ (i = f4Index 2 ∧ j = f4Index 3)) ∧
        (ε = 1 ∨ ε = -1) ∧
        (fun α => u • α) '' charRootKernel v = parabolicRoots .F4 {i, j} ∧
        ∀ x ∈ Submodule.span ℝ (ofLattice '' parabolicRoots .F4 {i, j}),
          weylAct .F4 (u * f4PhiSix * u⁻¹) x =
            -weylAct .F4 ((simple .F4 i * simple .F4 j) ^ ε) x := by
  have ha := orderOf_negUnitPhiSix hp3 hq
  have heig₃ : (dualMatrix (ZMod p) (f4Coxeter ^ 4)).mulVec v =
      ((negUnitPhiSix hq : (ZMod p)ˣ) : ZMod p) • v := by
    have h1 : (dualMatrix (ZMod p) (f4Coxeter ^ 4)).mulVec v = -(q • v) := by
      rw [← heig, dualMatrix_f4PhiSix, Matrix.neg_mulVec, neg_neg]
    rw [h1, coe_negUnitPhiSix]
    exact (neg_smul q v).symm
  rcases (F4_order_three_Weyl_lattice_and_surviving_A2_kernels.2.2.2.2.2 p hp hp3 _ ha v hv
    heig₃).1 with h | ⟨u, i, j, ε, hij, hε, hu, hact⟩
  · exact Or.inl h
  · refine Or.inr ⟨u, i, j, ε, hij, hε, hu, fun x hx => ?_⟩
    rw [weylAct_conj_f4PhiSix, hact x hx]

end F4Weyl

end CFSG.RankThree.Chevalley
