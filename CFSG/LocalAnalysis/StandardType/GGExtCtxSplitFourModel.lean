module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthNormal
public import CFSG.LocalAnalysis.StandardType.ZS.ClassReflClosure
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType.OFourMinusFive

open Subgroup CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def Qm : QuadraticForm (ZMod 5) (Fin 4 → ZMod 5) :=
  QuadraticMap.linMulLin (LinearMap.proj 0) (LinearMap.proj 1) +
    QuadraticMap.linMulLin (LinearMap.proj 2) (LinearMap.proj 2) +
    (3 : ZMod 5) • QuadraticMap.linMulLin (LinearMap.proj 3) (LinearMap.proj 3)

@[expose] noncomputable def ofMat (A B : Matrix (Fin 4) (Fin 4) (ZMod 5)) (h : A * B = 1)
    (h' : B * A = 1) : (Fin 4 → ZMod 5) ≃ₗ[ZMod 5] (Fin 4 → ZMod 5) :=
  LinearEquiv.ofLinear (Matrix.toLin' A) (Matrix.toLin' B)
    (by rw [← Matrix.toLin'_mul, h, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, h', Matrix.toLin'_one])

@[expose] noncomputable def uOne : (Fin 4 → ZMod 5) ≃ₗ[ZMod 5] (Fin 4 → ZMod 5) :=
  ofMat !![1, 4, 3, 0; 0, 1, 0, 0; 0, 1, 1, 0; 0, 0, 0, 1]
    !![1, 4, 2, 0; 0, 1, 0, 0; 0, 4, 1, 0; 0, 0, 0, 1] (by decide) (by decide)

@[expose] noncomputable def uTwo : (Fin 4 → ZMod 5) ≃ₗ[ZMod 5] (Fin 4 → ZMod 5) :=
  ofMat !![1, 2, 0, 4; 0, 1, 0, 0; 0, 0, 1, 0; 0, 1, 0, 1]
    !![1, 2, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 0, 4, 0, 1] (by decide) (by decide)

@[expose] noncomputable def dZero : (Fin 4 → ZMod 5) ≃ₗ[ZMod 5] (Fin 4 → ZMod 5) :=
  ofMat !![3, 0, 0, 0; 0, 2, 0, 0; 0, 0, 3, 1; 0, 0, 3, 3]
    !![2, 0, 0, 0; 0, 3, 0, 0; 0, 0, 3, 4; 0, 0, 2, 3] (by decide) (by decide)

theorem Qm_apply (v : Fin 4 → ZMod 5) : Qm v = v 0 * v 1 + v 2 ^ 2 + 3 * v 3 ^ 2 := by
  unfold Qm
  simp only [QuadraticMap.add_apply, QuadraticMap.smul_apply, QuadraticMap.linMulLin_apply,
    LinearMap.proj_apply, smul_eq_mul]
  ring

private theorem polar_Qm_apply (x y : Fin 4 → ZMod 5) :
    QuadraticMap.polar Qm x y =
      x 0 * y 1 + x 1 * y 0 + 2 * x 2 * y 2 + 6 * x 3 * y 3 := by
  simp only [QuadraticMap.polar, Qm_apply, Pi.add_apply]
  ring

theorem Qm_nondegenerate : (QuadraticMap.polarBilin Qm).Nondegenerate := by
  have hsymm : (QuadraticMap.polarBilin Qm).IsSymm :=
    ⟨fun x y => by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
      exact QuadraticMap.polar_comm Qm x y⟩
  rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft hsymm.isRefl]
  intro x h
  have key2 : ∀ a : ZMod 5, 2 * a = 0 → a = 0 := by decide
  have key6 : ∀ a : ZMod 5, 6 * a = 0 → a = 0 := by decide
  have h0 : x 0 = 0 := by
    have h' := h (Pi.single 1 1)
    simpa [polar_Qm_apply, Pi.single_apply] using h'
  have h1 : x 1 = 0 := by
    have h' := h (Pi.single 0 1)
    simpa [polar_Qm_apply, Pi.single_apply] using h'
  have h2 : x 2 = 0 := by
    have h' := h (Pi.single 2 1)
    exact key2 (x 2) (by simpa [polar_Qm_apply, Pi.single_apply] using h')
  have h3 : x 3 = 0 := by
    have h' := h (Pi.single 3 1)
    exact key6 (x 3) (by simpa [polar_Qm_apply, Pi.single_apply] using h')
  funext i
  fin_cases i <;> assumption

private def minusIe2 : (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) ≃ Fin 4 :=
  (Equiv.sumCongr (Equiv.refl (Fin (2 - 1))) finSumFinEquiv).trans finSumFinEquiv

private theorem minusIe2_symm_zero : minusIe2.symm 0 = Sum.inl 0 := by decide

private theorem minusIe2_symm_one : minusIe2.symm 1 = Sum.inr (Sum.inl 0) := by decide

private theorem minusIe2_symm_two : minusIe2.symm 2 = Sum.inr (Sum.inr 0) := by decide

private theorem minusIe2_symm_three : minusIe2.symm 3 = Sum.inr (Sum.inr 1) := by decide

private noncomputable def sigma :
    (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → ZMod 5) ≃ₗ[ZMod 5] (Fin 4 → ZMod 5) :=
  (LinearEquiv.funCongrLeft (ZMod 5) (ZMod 5) minusIe2).symm

private theorem sigma_apply (v : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → ZMod 5) (j : Fin 4) :
    sigma v j = v (minusIe2.symm j) := by
  simp [sigma]

private theorem Qm_sigma [Fact (Nat.Prime 5)]
    (v : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → ZMod 5) :
    Qm (sigma v) = CFSG.LieType.Universal.Spin.quadMinus 2 (ZMod 5) 0 3 v := by
  rw [Qm_apply, CFSG.LieType.Universal.Spin.quadMinus_apply, Fin.sum_univ_one]
  simp only [sigma_apply, minusIe2_symm_zero, minusIe2_symm_one, minusIe2_symm_two,
    minusIe2_symm_three]
  ring

private theorem Qm_hirr : ∀ s : ZMod 5, s ^ 2 + 0 * s + 3 ≠ 0 := by decide

theorem exists_isometry [Fact (Nat.Prime 5)] {T : Type} [AddCommGroup T] [Module (ZMod 5) T]
    [Module.Finite (ZMod 5) T] (hT : Module.finrank (ZMod 5) T = 4)
    {Q : QuadraticForm (ZMod 5) T} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    ∃ e : T ≃ₗ[ZMod 5] (Fin 4 → ZMod 5), ∀ t, Qm (e t) = Q t := by
  let sigmaIso :
      (CFSG.LieType.Universal.Spin.quadMinus 2 (ZMod 5) 0 3).IsometryEquiv Qm :=
    ⟨sigma, fun v => Qm_sigma v⟩
  obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_not_isPlusType hQ (n := 2)
    (by norm_num) (by rw [hT]) hminus (b := 0) (c := 3) Qm_hirr
  exact ⟨(e.trans sigmaIso).toLinearEquiv, fun t => (e.trans sigmaIso).map_app t⟩

private lemma ofMat_toLinearMap (A B : Matrix (Fin 4) (Fin 4) (ZMod 5))
    (h : A * B = 1) (h' : B * A = 1) :
    ((ofMat A B h h' : (Fin 4 → ZMod 5) ≃ₗ[ZMod 5] (Fin 4 → ZMod 5)) :
      (Fin 4 → ZMod 5) →ₗ[ZMod 5] (Fin 4 → ZMod 5)) = Matrix.toLin' A := rfl

private lemma ofMat_inv (A B : Matrix (Fin 4) (Fin 4) (ZMod 5)) (h : A * B = 1)
    (h' : B * A = 1) : (ofMat A B h h')⁻¹ = ofMat B A h' h := rfl

private lemma ofMat_apply (A B : Matrix (Fin 4) (Fin 4) (ZMod 5)) (h : A * B = 1)
    (h' : B * A = 1) (v : Fin 4 → ZMod 5) : ofMat A B h h' v = Matrix.mulVec A v := by
  simp [ofMat, Matrix.toLin'_apply]

private lemma coe_pow_toLinearMap (e : (Fin 4 → ZMod 5) ≃ₗ[ZMod 5] (Fin 4 → ZMod 5))
    (n : ℕ) :
    ((e ^ n : (Fin 4 → ZMod 5) ≃ₗ[ZMod 5] (Fin 4 → ZMod 5)) :
      (Fin 4 → ZMod 5) →ₗ[ZMod 5] (Fin 4 → ZMod 5)) =
      (e : (Fin 4 → ZMod 5) →ₗ[ZMod 5] (Fin 4 → ZMod 5)) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      nth_rewrite 1 [pow_succ]
      rw [LinearEquiv.coe_toLinearMap_mul, ih, pow_succ]

private lemma uOne_apply (v : Fin 4 → ZMod 5) :
    uOne v = ![v 0 + 4 * v 1 + 3 * v 2, v 1, v 1 + v 2, v 3] := by
  rw [uOne, ofMat_apply]
  funext k
  fin_cases k <;> simp [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four]

private lemma uTwo_apply (v : Fin 4 → ZMod 5) :
    uTwo v = ![v 0 + 2 * v 1 + 4 * v 3, v 1, v 2, v 1 + v 3] := by
  rw [uTwo, ofMat_apply]
  funext k
  fin_cases k <;> simp [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four]

private lemma uOne_apply_one (v : Fin 4 → ZMod 5) : (uOne v) 1 = v 1 := by
  rw [uOne_apply]; simp

private lemma uOne_apply_two (v : Fin 4 → ZMod 5) : (uOne v) 2 = v 1 + v 2 := by
  rw [uOne_apply]; simp

private lemma uOne_apply_three (v : Fin 4 → ZMod 5) : (uOne v) 3 = v 3 := by
  rw [uOne_apply]; simp

private lemma uTwo_apply_one (v : Fin 4 → ZMod 5) : (uTwo v) 1 = v 1 := by
  rw [uTwo_apply]; simp

private lemma uTwo_apply_two (v : Fin 4 → ZMod 5) : (uTwo v) 2 = v 2 := by
  rw [uTwo_apply]; simp

private lemma uTwo_apply_three (v : Fin 4 → ZMod 5) : (uTwo v) 3 = v 1 + v 3 := by
  rw [uTwo_apply]; simp

private lemma uOne_pow_apply (i : ℕ) : ∀ v : Fin 4 → ZMod 5,
    ((uOne ^ i) v) 1 = v 1 ∧ ((uOne ^ i) v) 2 = v 2 + (i : ZMod 5) * v 1 ∧
      ((uOne ^ i) v) 3 = v 3 := by
  induction i with
  | zero => intro v; simp
  | succ i ih =>
      intro v
      obtain ⟨h1, h2, h3⟩ := ih (uOne v)
      refine ⟨?_, ?_, ?_⟩
      · rw [pow_succ, LinearEquiv.mul_apply, h1, uOne_apply_one]
      · rw [pow_succ, LinearEquiv.mul_apply, h2, uOne_apply_two, uOne_apply_one]
        rw [Nat.cast_succ]
        ring
      · rw [pow_succ, LinearEquiv.mul_apply, h3, uOne_apply_three]

private lemma uTwo_pow_apply (j : ℕ) : ∀ v : Fin 4 → ZMod 5,
    ((uTwo ^ j) v) 1 = v 1 ∧ ((uTwo ^ j) v) 2 = v 2 ∧
      ((uTwo ^ j) v) 3 = v 3 + (j : ZMod 5) * v 1 := by
  induction j with
  | zero => intro v; simp
  | succ j ih =>
      intro v
      obtain ⟨h1, h2, h3⟩ := ih (uTwo v)
      refine ⟨?_, ?_, ?_⟩
      · rw [pow_succ, LinearEquiv.mul_apply, h1, uTwo_apply_one]
      · rw [pow_succ, LinearEquiv.mul_apply, h2, uTwo_apply_two]
      · rw [pow_succ, LinearEquiv.mul_apply, h3, uTwo_apply_three, uTwo_apply_one]
        rw [Nat.cast_succ]
        ring

theorem uOne_pow_five : uOne ^ 5 = 1 := by
  unfold uOne
  apply LinearEquiv.toLinearMap_injective
  simp only [coe_pow_toLinearMap, LinearEquiv.coe_toLinearMap_one, ofMat_toLinearMap,
    ← Matrix.toLin'_pow, ← Matrix.toLin'_one]
  exact congrArg Matrix.toLin' (by decide)

theorem uTwo_pow_five : uTwo ^ 5 = 1 := by
  unfold uTwo
  apply LinearEquiv.toLinearMap_injective
  simp only [coe_pow_toLinearMap, LinearEquiv.coe_toLinearMap_one, ofMat_toLinearMap,
    ← Matrix.toLin'_pow, ← Matrix.toLin'_one]
  exact congrArg Matrix.toLin' (by decide)

theorem uOne_mul_uTwo : uOne * uTwo = uTwo * uOne := by
  unfold uOne uTwo
  apply LinearEquiv.toLinearMap_injective
  simp only [LinearEquiv.coe_toLinearMap_mul, ofMat_toLinearMap, Module.End.mul_eq_comp,
    ← Matrix.toLin'_mul]
  exact congrArg Matrix.toLin' (by decide)

theorem dZero_pow_twelve : dZero ^ 12 = 1 := by
  unfold dZero
  apply LinearEquiv.toLinearMap_injective
  simp only [coe_pow_toLinearMap, LinearEquiv.coe_toLinearMap_one, ofMat_toLinearMap,
    ← Matrix.toLin'_pow, ← Matrix.toLin'_one]
  exact congrArg Matrix.toLin' (by decide)

theorem dZero_conj_uOne : dZero * uOne * dZero⁻¹ = uOne ^ 4 * uTwo ^ 4 := by
  unfold dZero uOne uTwo
  rw [ofMat_inv]
  apply LinearEquiv.toLinearMap_injective
  simp only [LinearEquiv.coe_toLinearMap_mul, coe_pow_toLinearMap, ofMat_toLinearMap,
    Module.End.mul_eq_comp, ← Matrix.toLin'_pow, ← Matrix.toLin'_mul]
  exact congrArg Matrix.toLin' (by decide)

theorem dZero_conj_uTwo : dZero * uTwo * dZero⁻¹ = uOne ^ 3 * uTwo ^ 4 := by
  unfold dZero uOne uTwo
  rw [ofMat_inv]
  apply LinearEquiv.toLinearMap_injective
  simp only [LinearEquiv.coe_toLinearMap_mul, coe_pow_toLinearMap, ofMat_toLinearMap,
    Module.End.mul_eq_comp, ← Matrix.toLin'_pow, ← Matrix.toLin'_mul]
  exact congrArg Matrix.toLin' (by decide)

theorem uPow_injective {i j i' j' : ℕ} (hi : i < 5) (hj : j < 5) (hi' : i' < 5) (hj' : j' < 5)
    (h : uOne ^ i * uTwo ^ j = uOne ^ i' * uTwo ^ j') : i = i' ∧ j = j' := by
  have hv : (uOne ^ i * uTwo ^ j) ![0, 1, 0, 0] =
      (uOne ^ i' * uTwo ^ j') ![0, 1, 0, 0] :=
    congrArg (fun e : (Fin 4 → ZMod 5) ≃ₗ[ZMod 5] (Fin 4 → ZMod 5) =>
      e ![0, 1, 0, 0]) h
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hv
  have h2 := congrFun hv (2 : Fin 4)
  rw [ (uOne_pow_apply i ((uTwo ^ j) ![0, 1, 0, 0])).2.1,
       (uOne_pow_apply i' ((uTwo ^ j') ![0, 1, 0, 0])).2.1,
       (uTwo_pow_apply j ![0, 1, 0, 0]).1,
       (uTwo_pow_apply j ![0, 1, 0, 0]).2.1,
       (uTwo_pow_apply j' ![0, 1, 0, 0]).1,
       (uTwo_pow_apply j' ![0, 1, 0, 0]).2.1 ] at h2
  have h2' : (i : ZMod 5) = (i' : ZMod 5) := by simpa using h2
  have h3 := congrFun hv (3 : Fin 4)
  rw [ (uOne_pow_apply i ((uTwo ^ j) ![0, 1, 0, 0])).2.2,
       (uOne_pow_apply i' ((uTwo ^ j') ![0, 1, 0, 0])).2.2,
       (uTwo_pow_apply j ![0, 1, 0, 0]).2.2,
       (uTwo_pow_apply j' ![0, 1, 0, 0]).2.2 ] at h3
  have h3' : (j : ZMod 5) = (j' : ZMod 5) := by simpa using h3
  have hi_eq : i = i' := by
    have hc := (ZMod.natCast_eq_natCast_iff' i i' 5).mp h2'
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at hc
  have hj_eq : j = j' := by
    have hc := (ZMod.natCast_eq_natCast_iff' j j' 5).mp h3'
    rwa [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at hc
  exact ⟨hi_eq, hj_eq⟩

private lemma reflect_smul [Fact (Nat.Prime 5)] (a : Fin 4 → ZMod 5) (k : ZMod 5)
    (hk : Qm a * k = 1) (x : Fin 4 → ZMod 5) :
    CFSG.ClassicalGroups.Orthogonal.reflect Qm a x =
      x - ((Qm (a + x) - Qm a - Qm x) * k) • a := by
  have ha : Qm a ≠ 0 := left_ne_zero_of_mul_eq_one hk
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply ha, div_eq_mul_inv,
    inv_eq_of_mul_eq_one_right hk]
  rfl

private lemma zmod5_one_ne_zero : (1 : ZMod 5) ≠ 0 := by decide

private lemma zmod5_two_ne_zero : (2 : ZMod 5) ≠ 0 := by decide

private lemma zmod5_three_ne_zero : (3 : ZMod 5) ≠ 0 := by decide

private lemma zmod5_four_ne_zero : (4 : ZMod 5) ≠ 0 := by decide

local macro "rk " "(" a:term ", " k:term ")" : term =>
  `(reflect_smul $a $k (by rw [Qm_apply]; decide +revert))

local macro "reflect_ext" "[" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  refine (Pi.basisFun (ZMod 5) (Fin 4)).ext' fun i => ?_
  fin_cases i <;>
  simp only [Pi.basisFun_apply, LinearEquiv.mul_apply, uOne, uTwo, dZero, ofMat,
    LinearEquiv.coe_ofLinearMap, Matrix.toLin'_apply, Qm_apply, $xs,*] <;>
  decide +revert))

private lemma uOne_eq_c1 [Fact (Nat.Prime 5)] :
    uOne = (CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 0, 1, 0] *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![1, 0, 1, 0]) := by
  reflect_ext [rk (![0, 0, 1, 0], 1), rk (![1, 0, 1, 0], 1)]

private lemma uTwo_eq_c1 [Fact (Nat.Prime 5)] :
    uTwo = (uOne * (CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 0, 2, 3] *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![2, 0, 2, 3])) := by
  reflect_ext [rk (![0, 0, 2, 3], 1), rk (![2, 0, 2, 3], 1)]

private lemma dZero_eq_c1 [Fact (Nat.Prime 5)] :
    dZero = (((CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 0, 1, 0] *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![1, 1, 0, 0]) *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![1, 3, 1, 3]) *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![1, 3, 4, 2]) := by
  reflect_ext [rk (![0, 0, 1, 0], 1), rk (![1, 1, 0, 0], 1),
    rk (![1, 3, 1, 3], 1), rk (![1, 3, 4, 2], 1)]

private lemma uTwo_eq_c2 [Fact (Nat.Prime 5)] :
    uTwo = (CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 0, 0, 2] *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![1, 0, 0, 2]) := by
  reflect_ext [rk (![0, 0, 0, 2], 3), rk (![1, 0, 0, 2], 3)]

private lemma uOne_eq_c2 [Fact (Nat.Prime 5)] :
    uOne = ((CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 0, 0, 2] *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![2, 0, 0, 2]) *
      (CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 0, 2, 1] *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![1, 0, 2, 1])) := by
  reflect_ext [rk (![0, 0, 0, 2], 3), rk (![2, 0, 0, 2], 3),
    rk (![0, 0, 2, 1], 3), rk (![1, 0, 2, 1], 3)]

private lemma dZero_eq_c2 [Fact (Nat.Prime 5)] :
    dZero = (((CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 0, 0, 2] *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![1, 1, 2, 2]) *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![1, 1, 3, 3]) *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![2, 1, 0, 0]) := by
  reflect_ext [rk (![0, 0, 0, 2], 3), rk (![1, 1, 2, 2], 3),
    rk (![1, 1, 3, 3], 3), rk (![2, 1, 0, 0], 3)]

private lemma uTwo_eq_c3 [Fact (Nat.Prime 5)] :
    uTwo = (CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 0, 0, 1] *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![2, 0, 0, 4]) := by
  reflect_ext [rk (![0, 0, 0, 1], 2), rk (![2, 0, 0, 4], 2)]

private lemma uOne_eq_c3 [Fact (Nat.Prime 5)] :
    uOne = ((CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 0, 0, 1] *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![1, 0, 0, 1]) *
      (CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 0, 1, 3] *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![2, 0, 4, 2])) := by
  reflect_ext [rk (![0, 0, 0, 1], 2), rk (![1, 0, 0, 1], 2),
    rk (![0, 0, 1, 3], 2), rk (![2, 0, 4, 2], 2)]

private lemma dZero_eq_c3 [Fact (Nat.Prime 5)] :
    dZero = (((CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 0, 0, 1] *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![1, 3, 0, 0]) *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![1, 4, 1, 1]) *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![1, 4, 4, 4]) := by
  reflect_ext [rk (![0, 0, 0, 1], 2), rk (![1, 3, 0, 0], 2),
    rk (![1, 4, 1, 1], 2), rk (![1, 4, 4, 4], 2)]

private lemma uOne_eq_c4 [Fact (Nat.Prime 5)] :
    uOne = (CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 0, 2, 0] *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![2, 0, 2, 0]) := by
  reflect_ext [rk (![0, 0, 2, 0], 4), rk (![2, 0, 2, 0], 4)]

private lemma uTwo_eq_c4 [Fact (Nat.Prime 5)] :
    uTwo = (uOne * (CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 0, 1, 4] *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![1, 0, 1, 4])) := by
  reflect_ext [rk (![0, 0, 1, 4], 4), rk (![1, 0, 1, 4], 4)]

private lemma dZero_eq_c4 [Fact (Nat.Prime 5)] :
    dZero = (((CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 0, 1, 1] *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![1, 2, 2, 4]) *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![1, 2, 3, 1]) *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![2, 2, 0, 0]) := by
  reflect_ext [rk (![0, 0, 1, 1], 4), rk (![1, 2, 2, 4], 4),
    rk (![1, 2, 3, 1], 4), rk (![2, 2, 0, 0], 4)]

private lemma classRefl_mem [Fact (Nat.Prime 5)] {c : ZMod 5} (hc : c ≠ 0)
    {a : Fin 4 → ZMod 5} (ha : Qm a = c) :
    CFSG.ClassicalGroups.Orthogonal.reflect Qm a ∈ closure (ClassRefl 5 Qm c) :=
  Subgroup.subset_closure
    ((mem_classRefl_iff (p := 5) (by norm_num) Qm_nondegenerate hc _).mpr ⟨a, ha, rfl⟩)

local macro "rm" : tactic => `(tactic|
  first
    | exact classRefl_mem zmod5_one_ne_zero (by rw [Qm_apply]; decide +revert)
    | exact classRefl_mem zmod5_two_ne_zero (by rw [Qm_apply]; decide +revert)
    | exact classRefl_mem zmod5_three_ne_zero (by rw [Qm_apply]; decide +revert)
    | exact classRefl_mem zmod5_four_ne_zero (by rw [Qm_apply]; decide +revert))

private lemma uOne_mem_one [Fact (Nat.Prime 5)] :
    uOne ∈ closure (ClassRefl 5 Qm (1 : ZMod 5)) := by
  rw [uOne_eq_c1]
  repeat (first | apply Subgroup.mul_mem | rm)

private lemma uTwo_mem_one [Fact (Nat.Prime 5)] :
    uTwo ∈ closure (ClassRefl 5 Qm (1 : ZMod 5)) := by
  rw [uTwo_eq_c1]
  apply Subgroup.mul_mem
  · exact uOne_mem_one
  · repeat (first | apply Subgroup.mul_mem | rm)

private lemma dZero_mem_one [Fact (Nat.Prime 5)] :
    dZero ∈ closure (ClassRefl 5 Qm (1 : ZMod 5)) := by
  rw [dZero_eq_c1]
  repeat (first | apply Subgroup.mul_mem | rm)

private lemma uOne_mem_two [Fact (Nat.Prime 5)] :
    uOne ∈ closure (ClassRefl 5 Qm (2 : ZMod 5)) := by
  rw [uOne_eq_c2]
  repeat (first | apply Subgroup.mul_mem | rm)

private lemma uTwo_mem_two [Fact (Nat.Prime 5)] :
    uTwo ∈ closure (ClassRefl 5 Qm (2 : ZMod 5)) := by
  rw [uTwo_eq_c2]
  repeat (first | apply Subgroup.mul_mem | rm)

private lemma dZero_mem_two [Fact (Nat.Prime 5)] :
    dZero ∈ closure (ClassRefl 5 Qm (2 : ZMod 5)) := by
  rw [dZero_eq_c2]
  repeat (first | apply Subgroup.mul_mem | rm)

private lemma uOne_mem_three [Fact (Nat.Prime 5)] :
    uOne ∈ closure (ClassRefl 5 Qm (3 : ZMod 5)) := by
  rw [uOne_eq_c3]
  repeat (first | apply Subgroup.mul_mem | rm)

private lemma uTwo_mem_three [Fact (Nat.Prime 5)] :
    uTwo ∈ closure (ClassRefl 5 Qm (3 : ZMod 5)) := by
  rw [uTwo_eq_c3]
  repeat (first | apply Subgroup.mul_mem | rm)

private lemma dZero_mem_three [Fact (Nat.Prime 5)] :
    dZero ∈ closure (ClassRefl 5 Qm (3 : ZMod 5)) := by
  rw [dZero_eq_c3]
  repeat (first | apply Subgroup.mul_mem | rm)

private lemma uOne_mem_four [Fact (Nat.Prime 5)] :
    uOne ∈ closure (ClassRefl 5 Qm (4 : ZMod 5)) := by
  rw [uOne_eq_c4]
  repeat (first | apply Subgroup.mul_mem | rm)

private lemma uTwo_mem_four [Fact (Nat.Prime 5)] :
    uTwo ∈ closure (ClassRefl 5 Qm (4 : ZMod 5)) := by
  rw [uTwo_eq_c4]
  apply Subgroup.mul_mem
  · exact uOne_mem_four
  · repeat (first | apply Subgroup.mul_mem | rm)

private lemma dZero_mem_four [Fact (Nat.Prime 5)] :
    dZero ∈ closure (ClassRefl 5 Qm (4 : ZMod 5)) := by
  rw [dZero_eq_c4]
  repeat (first | apply Subgroup.mul_mem | rm)

theorem mem_closure_classRefl [Fact (Nat.Prime 5)] {c : ZMod 5} (hc : c ≠ 0) :
    uOne ∈ closure (ClassRefl 5 Qm c) ∧ uTwo ∈ closure (ClassRefl 5 Qm c) ∧
      dZero ∈ closure (ClassRefl 5 Qm c) := by
  fin_cases c
  all_goals
    first
      | exact absurd rfl hc
      | exact ⟨uOne_mem_one, uTwo_mem_one, dZero_mem_one⟩
      | exact ⟨uOne_mem_two, uTwo_mem_two, dZero_mem_two⟩
      | exact ⟨uOne_mem_three, uTwo_mem_three, dZero_mem_three⟩
      | exact ⟨uOne_mem_four, uTwo_mem_four, dZero_mem_four⟩

private lemma cocycle_dZero_apply (v : Fin 4 → ZMod 5) :
    dZero v = ![3 * v 0, 2 * v 1, 3 * v 2 + v 3, 3 * v 2 + 3 * v 3] := by
  funext i
  fin_cases i <;>
    simp [dZero, ofMat, LinearEquiv.ofLinear_apply, Matrix.toLin'_apply,
      Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four]

private lemma cocycle_sumU1 (v : Fin 4 → ZMod 5) :
    (∑ k ∈ Finset.range 4, (uOne ^ k) v) =
      ![4 * v 0 + v 1 + 3 * v 2, 4 * v 1, v 1 + 4 * v 2, 4 * v 3] := by
  funext i
  fin_cases i <;>
    simp [Finset.sum_apply, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.sum_range_one, pow_zero, pow_one, pow_succ, LinearEquiv.mul_apply,
      LinearEquiv.coe_one, uOne_apply]
  all_goals ring_nf
  all_goals reduce_mod_char

private lemma cocycle_sumU1three (v : Fin 4 → ZMod 5) :
    (∑ k ∈ Finset.range 3, (uOne ^ k) v) =
      ![3 * v 0 + 4 * v 2, 3 * v 1, 3 * v 1 + 3 * v 2, 3 * v 3] := by
  funext i
  fin_cases i <;>
    simp [Finset.sum_apply, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.sum_range_one, pow_zero, pow_one, pow_succ, LinearEquiv.mul_apply,
      LinearEquiv.coe_one, uOne_apply]
  all_goals ring_nf
  all_goals reduce_mod_char

private lemma cocycle_sumU2 (v : Fin 4 → ZMod 5) :
    (∑ k ∈ Finset.range 4, (uTwo ^ k) v) =
      ![4 * v 0 + 3 * v 1 + 4 * v 3, 4 * v 1, 4 * v 2, v 1 + 4 * v 3] := by
  funext i
  fin_cases i <;>
    simp [Finset.sum_apply, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.sum_range_one, pow_zero, pow_one, pow_succ, LinearEquiv.mul_apply,
      LinearEquiv.coe_one, uTwo_apply]
  all_goals ring_nf
  all_goals reduce_mod_char

private lemma cocycle_uOne4_apply (v : Fin 4 → ZMod 5) :
    (uOne ^ 4) v = ![v 0 + 4 * v 1 + 2 * v 2, v 1, 4 * v 1 + v 2, v 3] := by
  funext i
  fin_cases i <;>
    simp [pow_zero, pow_one, pow_succ, LinearEquiv.mul_apply, LinearEquiv.coe_one,
      uOne_apply]
  all_goals ring_nf
  all_goals reduce_mod_char

private lemma cocycle_uOne3_apply (v : Fin 4 → ZMod 5) :
    (uOne ^ 3) v = ![v 0 + v 1 + 4 * v 2, v 1, 3 * v 1 + v 2, v 3] := by
  funext i
  fin_cases i <;>
    simp [pow_zero, pow_one, pow_succ, LinearEquiv.mul_apply, LinearEquiv.coe_one,
      uOne_apply]
  all_goals ring_nf
  all_goals reduce_mod_char

theorem cocycle_eq_zero (x y : Fin 4 → ZMod 5)
    (h₁ : ∑ k ∈ Finset.range 4, (uOne ^ k) x + (uOne ^ 4) (∑ k ∈ Finset.range 4, (uTwo ^ k) y) =
      dZero x)
    (h₂ : ∑ k ∈ Finset.range 3, (uOne ^ k) x + (uOne ^ 3) (∑ k ∈ Finset.range 4, (uTwo ^ k) y) =
      dZero y) :
    x = 0 ∧ y = 0 := by
  rw [cocycle_sumU1, cocycle_sumU2, cocycle_uOne4_apply, cocycle_dZero_apply] at h₁
  rw [cocycle_sumU1three, cocycle_sumU2, cocycle_uOne3_apply, cocycle_dZero_apply] at h₂
  have e10 : x 0 + x 1 + 3 * x 2 + 4 * y 0 + 4 * y 1 + 3 * y 2 + 4 * y 3 = 0 := by
    have this := congrFun h₁ 0
    simp at this
    linear_combination (norm := (ring_nf; try reduce_mod_char)) this
  have e11 : 2 * x 1 + 4 * y 1 = 0 := by
    have this := congrFun h₁ 1
    simp at this
    linear_combination (norm := (ring_nf; try reduce_mod_char)) this
  have e12 : x 1 + x 2 + 4 * x 3 + y 1 + 4 * y 2 = 0 := by
    have this := congrFun h₁ 2
    simp at this
    linear_combination (norm := (ring_nf; try reduce_mod_char)) this
  have e13 : 2 * x 2 + x 3 + y 1 + 4 * y 3 = 0 := by
    have this := congrFun h₁ 3
    simp at this
    linear_combination (norm := (ring_nf; try reduce_mod_char)) this
  have e20 : 3 * x 0 + 4 * x 2 + y 0 + 2 * y 1 + y 2 + 4 * y 3 = 0 := by
    have this := congrFun h₂ 0
    simp at this
    linear_combination (norm := (ring_nf; try reduce_mod_char)) this
  have e21 : 3 * x 1 + 2 * y 1 = 0 := by
    have this := congrFun h₂ 1
    simp at this
    linear_combination (norm := (ring_nf; try reduce_mod_char)) this
  have e22 : 3 * x 1 + 3 * x 2 + 2 * y 1 + y 2 + 4 * y 3 = 0 := by
    have this := congrFun h₂ 2
    simp at this
    linear_combination (norm := (ring_nf; try reduce_mod_char)) this
  have e23 : 3 * x 3 + y 1 + 2 * y 2 + y 3 = 0 := by
    have this := congrFun h₂ 3
    simp at this
    linear_combination (norm := (ring_nf; try reduce_mod_char)) this
  have blk1 : ∀ a b : ZMod 5, 2 * a + 4 * b = 0 → 3 * a + 2 * b = 0 →
      a = 0 ∧ b = 0 := by decide
  obtain ⟨hx1, hy1⟩ := blk1 (x 1) (y 1) e11 e21
  have blk2 : ∀ a b c d : ZMod 5, a + 4 * b + 4 * c = 0 → 2 * a + b + 4 * d = 0 →
      3 * a + c + 4 * d = 0 → 3 * b + 2 * c + d = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by decide
  have e12' : x 2 + 4 * x 3 + 4 * y 2 = 0 := by simpa [hx1, hy1] using e12
  have e13' : 2 * x 2 + x 3 + 4 * y 3 = 0 := by simpa [hy1] using e13
  have e22' : 3 * x 2 + y 2 + 4 * y 3 = 0 := by simpa [hx1, hy1] using e22
  have e23' : 3 * x 3 + 2 * y 2 + y 3 = 0 := by simpa [hy1] using e23
  obtain ⟨hx2, hx3, hy2, hy3⟩ := blk2 (x 2) (x 3) (y 2) (y 3) e12' e13' e22' e23'
  have blk3 : ∀ a b : ZMod 5, a + 4 * b = 0 → 3 * a + b = 0 → a = 0 ∧ b = 0 := by
    decide
  have e10' : x 0 + 4 * y 0 = 0 := by
    simpa [hx1, hy1, hx2, hy2, hx3, hy3] using e10
  have e20' : 3 * x 0 + y 0 = 0 := by
    simpa [hx1, hy1, hx2, hy2, hx3, hy3] using e20
  obtain ⟨hx0, hy0⟩ := blk3 (x 0) (y 0) e10' e20'
  refine ⟨?_, ?_⟩
  · funext i
    fin_cases i <;> simp [hx0, hx1, hx2, hx3]
  · funext i
    fin_cases i <;> simp [hy0, hy1, hy2, hy3]

open scoped Pointwise in
private lemma coe_sup_eq_mul_of_le_normalizer {G : Type*} [Group G] {H K : Subgroup G}
    (h : K ≤ Subgroup.normalizer (H : Set G)) :
    (↑(H ⊔ K) : Set G) = H * K :=
  Subgroup.coe_mul_of_right_le_normalizer_left H K h

theorem exists_splitData [Fact (Nat.Prime 5)] {T : Type} [AddCommGroup T] [Module (ZMod 5) T]
    [Module.Finite (ZMod 5) T] (hT : Module.finrank (ZMod 5) T = 4)
    {Q : QuadraticForm (ZMod 5) T} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) {c : ZMod 5} (hc : c ≠ 0) :
    ∃ u₁ u₂ d : T ≃ₗ[ZMod 5] T,
      u₁ ∈ closure (ClassRefl 5 Q c) ∧ u₂ ∈ closure (ClassRefl 5 Q c) ∧
      d ∈ closure (ClassRefl 5 Q c) ∧ d ^ 12 = 1 ∧
      d * u₁ * d⁻¹ = u₁ ^ 4 * u₂ ^ 4 ∧ d * u₂ * d⁻¹ = u₁ ^ 3 * u₂ ^ 4 ∧
      (∀ x y : T,
        ∑ k ∈ Finset.range 4, (u₁ ^ k) x + (u₁ ^ 4) (∑ k ∈ Finset.range 4, (u₂ ^ k) y) = d x →
        ∑ k ∈ Finset.range 3, (u₁ ^ k) x + (u₁ ^ 3) (∑ k ∈ Finset.range 4, (u₂ ^ k) y) = d y →
        x = 0 ∧ y = 0) ∧
      ¬ 5 ∣ (closure ({u₁, u₂, d} : Set (T ≃ₗ[ZMod 5] T))).relIndex
        (closure (ClassRefl 5 Q c)) := by
  classical
  obtain ⟨e, he⟩ := exists_isometry hT hQ hminus
  have he' : ∀ v : Fin 4 → ZMod 5, Q (e.symm v) = Qm v := by
    intro v
    rw [← he (e.symm v), LinearEquiv.apply_symm_apply]
  let φ : ((Fin 4 → ZMod 5) ≃ₗ[ZMod 5] (Fin 4 → ZMod 5)) ≃* (T ≃ₗ[ZMod 5] T) :=
    { toFun := fun x => e.trans (x.trans e.symm)
      invFun := fun y => e.symm.trans (y.trans e)
      left_inv := by intro x; ext w; simp
      right_inv := by intro y; ext w; simp
      map_mul' := by intro x y; ext w; simp }
  have hmap : ∀ (g : (Fin 4 → ZMod 5) ≃ₗ[ZMod 5] (Fin 4 → ZMod 5)) (t : T),
      e (φ g t) = g (e t) := by
    intro g t
    change e (e.symm (g (e t))) = g (e t)
    rw [LinearEquiv.apply_symm_apply]
  set u₁ : T ≃ₗ[ZMod 5] T := φ uOne with hu₁
  set u₂ : T ≃ₗ[ZMod 5] T := φ uTwo with hu₂
  set d : T ≃ₗ[ZMod 5] T := φ dZero with hd
  have hu₁_pow : u₁ ^ 5 = 1 := by rw [hu₁, ← map_pow, uOne_pow_five, map_one]
  have hu₂_pow : u₂ ^ 5 = 1 := by rw [hu₂, ← map_pow, uTwo_pow_five, map_one]
  have hd_pow : d ^ 12 = 1 := by rw [hd, ← map_pow, dZero_pow_twelve, map_one]
  have hd_conj_u₁ : d * u₁ * d⁻¹ = u₁ ^ 4 * u₂ ^ 4 := by
    rw [hd, hu₁, hu₂, ← map_mul, ← map_inv, ← map_mul, dZero_conj_uOne, map_mul, map_pow,
      map_pow]
  have hd_conj_u₂ : d * u₂ * d⁻¹ = u₁ ^ 3 * u₂ ^ 4 := by
    rw [hd, hu₁, hu₂, ← map_mul, ← map_inv, ← map_mul, dZero_conj_uTwo, map_mul, map_pow,
      map_pow]
  have hpow_inj : ∀ i j i' j' : ℕ, i < 5 → j < 5 → i' < 5 → j' < 5 →
      u₁ ^ i * u₂ ^ j = u₁ ^ i' * u₂ ^ j' → i = i' ∧ j = j' := by
    intro i j i' j' hi hj hi' hj' h
    have hs₁ : φ.symm u₁ = uOne := by rw [hu₁]; exact MulEquiv.symm_apply_apply φ uOne
    have hs₂ : φ.symm u₂ = uTwo := by rw [hu₂]; exact MulEquiv.symm_apply_apply φ uTwo
    have h' : uOne ^ i * uTwo ^ j = uOne ^ i' * uTwo ^ j' := by
      simpa only [map_mul, map_pow, hs₁, hs₂] using congrArg (⇑φ.symm) h
    exact uPow_injective hi hj hi' hj' h'
  have hu₁_ne : u₁ ≠ 1 := by
    intro h
    have hh : u₁ ^ 1 * u₂ ^ 0 = u₁ ^ 0 * u₂ ^ 0 := by simp [h]
    exact one_ne_zero
      (hpow_inj 1 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hh).1
  have hu₂_ne : u₂ ≠ 1 := by
    intro h
    have hh : u₁ ^ 0 * u₂ ^ 1 = u₁ ^ 0 * u₂ ^ 0 := by simp [h]
    exact one_ne_zero
      (hpow_inj 0 1 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hh).2
  have hmod : ∀ (x : T ≃ₗ[ZMod 5] T), orderOf x = 5 → ∀ z : ℤ,
      x ^ z = x ^ (z % 5).toNat := by
    intro x hxord z
    have h := zpow_mod_orderOf x z
    rw [hxord] at h
    calc x ^ z = x ^ (z % 5) := h.symm
      _ = x ^ ((z % 5).toNat : ℤ) := by
          congr 1
          exact (Int.toNat_of_nonneg (Int.emod_nonneg z (by norm_num : (5 : ℤ) ≠ 0))).symm
      _ = x ^ (z % 5).toNat := zpow_natCast x (z % 5).toNat
  have hu₁_order : orderOf u₁ = 5 := orderOf_eq_prime hu₁_pow hu₁_ne
  have hu₂_order : orderOf u₂ = 5 := orderOf_eq_prime hu₂_pow hu₂_ne
  have hdisj : Disjoint (Subgroup.zpowers u₁) (Subgroup.zpowers u₂) := by
    rw [Subgroup.disjoint_def]
    intro x hx hy
    rw [Subgroup.mem_zpowers_iff] at hx hy
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨n, hn⟩ := hy
    have hm : u₁ ^ m = u₁ ^ (m % 5).toNat := hmod u₁ hu₁_order m
    have hn' : u₂ ^ n = u₂ ^ (n % 5).toNat := hmod u₂ hu₂_order n
    rw [hm, hn'] at hn
    have hmi : (m % 5).toNat < 5 := by
      rw [Int.toNat_lt (Int.emod_nonneg m (by norm_num : (5 : ℤ) ≠ 0))]
      exact Int.emod_lt_of_pos m (by norm_num : (0 : ℤ) < 5)
    have hni : (n % 5).toNat < 5 := by
      rw [Int.toNat_lt (Int.emod_nonneg n (by norm_num : (5 : ℤ) ≠ 0))]
      exact Int.emod_lt_of_pos n (by norm_num : (0 : ℤ) < 5)
    have heq : u₁ ^ (m % 5).toNat * u₂ ^ 0 = u₁ ^ 0 * u₂ ^ (n % 5).toNat := by
      simp [hn]
    have hres := hpow_inj (m % 5).toNat 0 0 (n % 5).toNat hmi (by norm_num) (by norm_num) hni
      heq
    rw [hm, hres.1, pow_zero]
  have hH_card : Nat.card (Subgroup.zpowers u₁) = 5 := by
    rw [Nat.card_zpowers, hu₁_order]
  have hK_card : Nat.card (Subgroup.zpowers u₂) = 5 := by
    rw [Nat.card_zpowers, hu₂_order]
  have hcomm : Commute u₁ u₂ := by
    show u₁ * u₂ = u₂ * u₁
    rw [hu₁, hu₂, ← map_mul, ← map_mul, uOne_mul_uTwo]
  have hnorm : Subgroup.zpowers u₂ ≤
      Subgroup.normalizer (Subgroup.zpowers u₁ : Set (T ≃ₗ[ZMod 5] T)) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      change h ∈ Subgroup.zpowers u₁ at hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (hcomm.zpow_left k).eq)
  have hcoe := coe_sup_eq_mul_of_le_normalizer
    (H := Subgroup.zpowers u₁) (K := Subgroup.zpowers u₂) hnorm
  have hbij : Function.Bijective
      (fun p : Subgroup.zpowers u₁ × Subgroup.zpowers u₂ =>
        (⟨(p.1 : T ≃ₗ[ZMod 5] T) * p.2,
          Subgroup.mul_mem_sup p.1.2 p.2.2⟩ :
          (Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂ : Subgroup (T ≃ₗ[ZMod 5] T)))) := by
    constructor
    · intro p q hpq
      have hval : (p.1 : T ≃ₗ[ZMod 5] T) * p.2 = (q.1 : T ≃ₗ[ZMod 5] T) * q.2 :=
        congrArg (fun z : ↥(Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂) =>
          (z : T ≃ₗ[ZMod 5] T)) hpq
      exact Subgroup.mul_injective_of_disjoint hdisj hval
    · intro z
      have hz : (z : T ≃ₗ[ZMod 5] T) ∈
          (↑(Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂) : Set (T ≃ₗ[ZMod 5] T)) := z.2
      rw [hcoe] at hz
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hz
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  have hsup_card : Nat.card (↥(Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂ :
      Subgroup (T ≃ₗ[ZMod 5] T))) = 25 := by
    have hcard := Nat.card_congr (Equiv.ofBijective _ hbij)
    rw [Nat.card_prod, hH_card, hK_card] at hcard
    omega
  have hclosure : Subgroup.closure ({u₁, u₂} : Set (T ≃ₗ[ZMod 5] T)) =
      Subgroup.zpowers u₁ ⊔ Subgroup.zpowers u₂ := by
    rw [← Set.singleton_union, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure u₁,
      ← Subgroup.zpowers_eq_closure u₂]
  have hmem := mem_closure_classRefl (c := c) hc
  obtain ⟨ψ, hψ⟩ := wit_classRefl_transport (p := 5) (by norm_num) (by norm_num) Qm Q
    e.symm he' c rfl rfl
  have hu₁_mem : u₁ ∈ Subgroup.closure (ClassRefl 5 Q c) := by
    have hg : ((ψ ⟨uOne, hmem.1⟩ : ↥(Subgroup.closure (ClassRefl 5 Q c))) :
        T ≃ₗ[ZMod 5] T) = φ uOne := hψ ⟨uOne, hmem.1⟩
    rw [hu₁, ← hg]
    exact (ψ ⟨uOne, hmem.1⟩).2
  have hu₂_mem : u₂ ∈ Subgroup.closure (ClassRefl 5 Q c) := by
    have hg : ((ψ ⟨uTwo, hmem.2.1⟩ : ↥(Subgroup.closure (ClassRefl 5 Q c))) :
        T ≃ₗ[ZMod 5] T) = φ uTwo := hψ ⟨uTwo, hmem.2.1⟩
    rw [hu₂, ← hg]
    exact (ψ ⟨uTwo, hmem.2.1⟩).2
  have hd_mem : d ∈ Subgroup.closure (ClassRefl 5 Q c) := by
    have hg : ((ψ ⟨dZero, hmem.2.2⟩ : ↥(Subgroup.closure (ClassRefl 5 Q c))) :
        T ≃ₗ[ZMod 5] T) = φ dZero := hψ ⟨dZero, hmem.2.2⟩
    rw [hd, ← hg]
    exact (ψ ⟨dZero, hmem.2.2⟩).2
  have hR_le_O : Subgroup.closure (ClassRefl 5 Q c) ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    refine (Subgroup.closure_le (TauCeti.QuadraticMap.orthogonalGroup Q)).mpr ?_
    intro t ht
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr
      (isIsom_of_mem_closure_classRefl (p := 5) (Q := Q) (c := c)
        (Subgroup.subset_closure ht))
  have hR_dvd_O : Nat.card (Subgroup.closure (ClassRefl 5 Q c)) ∣
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    Subgroup.card_dvd_of_le hR_le_O
  have hO_card : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 31200 := by
    have hcardZ := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type
      (K := ZMod 5) (V := T) (Q := Q) hQ (m := 1) (by rw [hT])
      (ε := -1) (Or.inr ⟨rfl, hminus⟩)
    have hcardZ' : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) = 31200 := by
      rw [hcardZ]
      norm_num [Nat.card_zmod]
    exact_mod_cast hcardZ'
  have hR_dvd : Nat.card (Subgroup.closure (ClassRefl 5 Q c)) ∣ 31200 := by
    rw [hO_card] at hR_dvd_O
    exact hR_dvd_O
  have hB_le_R : Subgroup.closure ({u₁, u₂, d} : Set (T ≃ₗ[ZMod 5] T)) ≤
      Subgroup.closure (ClassRefl 5 Q c) := by
    refine (Subgroup.closure_le (Subgroup.closure (ClassRefl 5 Q c))).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hu₁_mem
    · exact hu₂_mem
    · exact hd_mem
  have hHc_le_B : Subgroup.closure ({u₁, u₂} : Set (T ≃ₗ[ZMod 5] T)) ≤
      Subgroup.closure ({u₁, u₂, d} : Set (T ≃ₗ[ZMod 5] T)) := by
    refine (Subgroup.closure_le (Subgroup.closure ({u₁, u₂, d} : Set (T ≃ₗ[ZMod 5] T)))).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  have hB_25 : 25 ∣ Nat.card (Subgroup.closure ({u₁, u₂, d} : Set (T ≃ₗ[ZMod 5] T))) := by
    have hdiv := Subgroup.card_dvd_of_le hHc_le_B
    rw [hclosure, hsup_card] at hdiv
    exact hdiv
  have hcocy : ∀ x y : T,
      ∑ k ∈ Finset.range 4, (u₁ ^ k) x + (u₁ ^ 4) (∑ k ∈ Finset.range 4, (u₂ ^ k) y) =
        d x →
      ∑ k ∈ Finset.range 3, (u₁ ^ k) x + (u₁ ^ 3) (∑ k ∈ Finset.range 4, (u₂ ^ k) y) =
        d y →
      x = 0 ∧ y = 0 := by
    intro x y h₁ h₂
    have he_u₁ : ∀ (k : ℕ) (t : T), e ((u₁ ^ k) t) = (uOne ^ k) (e t) := by
      intro k t
      have hk : u₁ ^ k = φ (uOne ^ k) := by rw [hu₁, ← map_pow]
      rw [hk, hmap]
    have he_u₂ : ∀ (k : ℕ) (t : T), e ((u₂ ^ k) t) = (uTwo ^ k) (e t) := by
      intro k t
      have hk : u₂ ^ k = φ (uTwo ^ k) := by rw [hu₂, ← map_pow]
      rw [hk, hmap]
    have he_d : ∀ t : T, e (d t) = dZero (e t) := by
      intro t
      rw [hd, hmap]
    have h₁' : ∑ k ∈ Finset.range 4, (uOne ^ k) (e x) +
        (uOne ^ 4) (∑ k ∈ Finset.range 4, (uTwo ^ k) (e y)) = dZero (e x) := by
      have h := congrArg e h₁
      rw [map_add, map_sum] at h
      have hA : ∑ k ∈ Finset.range 4, e ((u₁ ^ k) x) =
          ∑ k ∈ Finset.range 4, (uOne ^ k) (e x) :=
        Finset.sum_congr rfl (fun k _ => he_u₁ k x)
      have hB : e ((u₁ ^ 4) (∑ k ∈ Finset.range 4, (u₂ ^ k) y)) =
          (uOne ^ 4) (∑ k ∈ Finset.range 4, (uTwo ^ k) (e y)) := by
        rw [he_u₁, map_sum]
        exact congrArg (fun z => (uOne ^ 4) z)
          (Finset.sum_congr rfl (fun k _ => he_u₂ k y))
      rw [hA, hB, he_d] at h
      exact h
    have h₂' : ∑ k ∈ Finset.range 3, (uOne ^ k) (e x) +
        (uOne ^ 3) (∑ k ∈ Finset.range 4, (uTwo ^ k) (e y)) = dZero (e y) := by
      have h := congrArg e h₂
      rw [map_add, map_sum] at h
      have hA : ∑ k ∈ Finset.range 3, e ((u₁ ^ k) x) =
          ∑ k ∈ Finset.range 3, (uOne ^ k) (e x) :=
        Finset.sum_congr rfl (fun k _ => he_u₁ k x)
      have hB : e ((u₁ ^ 3) (∑ k ∈ Finset.range 4, (u₂ ^ k) y)) =
          (uOne ^ 3) (∑ k ∈ Finset.range 4, (uTwo ^ k) (e y)) := by
        rw [he_u₁, map_sum]
        exact congrArg (fun z => (uOne ^ 3) z)
          (Finset.sum_congr rfl (fun k _ => he_u₂ k y))
      rw [hA, hB, he_d] at h
      exact h
    obtain ⟨hx, hy⟩ := cocycle_eq_zero (e x) (e y) h₁' h₂'
    exact ⟨(e.map_eq_zero_iff).mp hx, (e.map_eq_zero_iff).mp hy⟩
  refine ⟨u₁, u₂, d, hu₁_mem, hu₂_mem, hd_mem, hd_pow, hd_conj_u₁, hd_conj_u₂, hcocy, ?_⟩
  intro h5
  have hrel : (Subgroup.closure ({u₁, u₂, d} : Set (T ≃ₗ[ZMod 5] T))).relIndex
      (Subgroup.closure (ClassRefl 5 Q c)) *
      Nat.card (Subgroup.closure ({u₁, u₂, d} : Set (T ≃ₗ[ZMod 5] T))) =
      Nat.card (Subgroup.closure (ClassRefl 5 Q c)) := by
    have h := Subgroup.relIndex_mul_card
      (H := Subgroup.closure ({u₁, u₂, d} : Set (T ≃ₗ[ZMod 5] T)))
      (K := Subgroup.closure (ClassRefl 5 Q c))
    rwa [inf_eq_left.mpr hB_le_R] at h
  have h125 : 125 ∣ Nat.card (Subgroup.closure (ClassRefl 5 Q c)) := by
    rw [← hrel]
    exact Nat.mul_dvd_mul h5 hB_25
  have hbad : 125 ∣ 31200 := dvd_trans h125 hR_dvd
  norm_num at hbad

end CFSG.StandardType.OFourMinusFive

end
