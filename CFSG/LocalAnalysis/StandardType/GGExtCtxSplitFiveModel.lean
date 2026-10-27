module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthNormal
public import CFSG.LocalAnalysis.StandardType.ZS.ClassReflClosure
public import CFSG.LocalAnalysis.StandardType.ZS.ClassReflSmul
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType.OFiveSeven

open Subgroup CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def Qm : QuadraticForm (ZMod 7) (Fin 5 → ZMod 7) :=
  QuadraticMap.linMulLin (LinearMap.proj 0) (LinearMap.proj 4) +
    QuadraticMap.linMulLin (LinearMap.proj 1) (LinearMap.proj 3) +
    QuadraticMap.linMulLin (LinearMap.proj 2) (LinearMap.proj 2)

@[expose] noncomputable def lOne : (Fin 5 → ZMod 7) ≃ₗ[ZMod 7] (Fin 5 → ZMod 7) :=
  Matrix.toLinearEquiv' !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 6;
      0, 0, 0, 0, 1]
    ⟨!![1, 6, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1],
      by decide, by decide⟩

@[expose] noncomputable def sOne : (Fin 5 → ZMod 7) ≃ₗ[ZMod 7] (Fin 5 → ZMod 7) :=
  Matrix.toLinearEquiv' !![1, 0, 0, 0, 0; 0, 1, 1, 5, 0; 0, 0, 1, 3, 0; 0, 0, 0, 1, 0;
      0, 0, 0, 0, 1]
    ⟨!![1, 0, 0, 0, 0; 0, 1, 6, 5, 0; 0, 0, 1, 4, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
      by decide, by decide⟩

@[expose] noncomputable def dTwo : (Fin 5 → ZMod 7) ≃ₗ[ZMod 7] (Fin 5 → ZMod 7) :=
  Matrix.toLinearEquiv' !![1, 0, 0, 0, 0; 0, 2, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 4, 0;
      0, 0, 0, 0, 1]
    ⟨!![1, 0, 0, 0, 0; 0, 4, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 2, 0; 0, 0, 0, 0, 1],
      by decide, by decide⟩

theorem Qm_apply (v : Fin 5 → ZMod 7) : Qm v = v 0 * v 4 + v 1 * v 3 + v 2 ^ 2 := by
  unfold Qm
  simp only [QuadraticMap.add_apply, QuadraticMap.linMulLin_apply, LinearMap.proj_apply]
  ring

private theorem polar_Qm_apply (x y : Fin 5 → ZMod 7) :
    QuadraticMap.polar Qm x y =
      x 0 * y 4 + x 4 * y 0 + x 1 * y 3 + x 3 * y 1 + 2 * x 2 * y 2 := by
  simp only [QuadraticMap.polar, Qm_apply, Pi.add_apply]
  ring

theorem Qm_nondegenerate : (QuadraticMap.polarBilin Qm).Nondegenerate := by
  have hsymm : (QuadraticMap.polarBilin Qm).IsSymm :=
    ⟨fun x y => by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
      exact QuadraticMap.polar_comm Qm x y⟩
  rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft hsymm.isRefl]
  intro x h
  have key2 : ∀ a : ZMod 7, 2 * a = 0 → a = 0 := by decide
  have h0 : x 0 = 0 := by simpa [polar_Qm_apply, Pi.single_apply] using h (Pi.single 4 1)
  have h4 : x 4 = 0 := by simpa [polar_Qm_apply, Pi.single_apply] using h (Pi.single 0 1)
  have h1 : x 1 = 0 := by simpa [polar_Qm_apply, Pi.single_apply] using h (Pi.single 3 1)
  have h3 : x 3 = 0 := by simpa [polar_Qm_apply, Pi.single_apply] using h (Pi.single 1 1)
  have h2 : x 2 = 0 :=
    key2 (x 2) (by simpa [polar_Qm_apply, Pi.single_apply] using h (Pi.single 2 1))
  funext i
  fin_cases i <;> assumption

private def ie5 : (Fin 2 ⊕ Fin 2 ⊕ Unit) ≃ Fin 5 :=
  ((Equiv.sumCongr (Equiv.refl (Fin 2))
    ((Equiv.sumCongr (Equiv.refl (Fin 2)) (finOneEquiv).symm).trans
      finSumFinEquiv)).trans finSumFinEquiv).trans
    (Equiv.swap (2 : Fin 5) (4 : Fin 5))

private theorem ie5_symm_zero : ie5.symm 0 = Sum.inl 0 := by decide

private theorem ie5_symm_one : ie5.symm 1 = Sum.inl 1 := by decide

private theorem ie5_symm_two : ie5.symm 2 = Sum.inr (Sum.inr ()) := by decide

private theorem ie5_symm_three : ie5.symm 3 = Sum.inr (Sum.inl 1) := by decide

private theorem ie5_symm_four : ie5.symm 4 = Sum.inr (Sum.inl 0) := by decide

private noncomputable def sigma :
    (Fin 2 ⊕ Fin 2 ⊕ Unit → ZMod 7) ≃ₗ[ZMod 7] (Fin 5 → ZMod 7) :=
  (LinearEquiv.funCongrLeft (ZMod 7) (ZMod 7) ie5).symm

private theorem sigma_apply (v : Fin 2 ⊕ Fin 2 ⊕ Unit → ZMod 7) (j : Fin 5) :
    sigma v j = v (ie5.symm j) := by
  simp [sigma]

private theorem Qm_sigma [Fact (Nat.Prime 7)]
    (v : Fin 2 ⊕ Fin 2 ⊕ Unit → ZMod 7) :
    Qm (sigma v) = CFSG.LieType.Universal.Spin.quadOdd 2 (ZMod 7) v := by
  rw [Qm_apply, CFSG.LieType.Universal.Spin.quadOdd_apply, Fin.sum_univ_two]
  simp only [sigma_apply, ie5_symm_zero, ie5_symm_one, ie5_symm_two, ie5_symm_three,
    ie5_symm_four]

theorem exists_isometry {T : Type} [AddCommGroup T] [Module (ZMod 7) T]
    [Module.Finite (ZMod 7) T] (hT : Module.finrank (ZMod 7) T = 5)
    {Q : QuadraticForm (ZMod 7) T} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    ∃ d : ZMod 7, d ≠ 0 ∧ ∃ e : T ≃ₗ[ZMod 7] (Fin 5 → ZMod 7), ∀ t, Qm (e t) = d * Q t := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h2 : ringChar (ZMod 7) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    norm_num
  have hdim : Module.finrank (ZMod 7) T = 2 * 2 + 1 := by rw [hT]
  obtain ⟨d, hd, ⟨iso⟩⟩ :=
    CFSG.GroupTheory.WeirSylow.exists_smul_isometry_quadOdd h2 Q hQ (n := 2) hdim
  let sigmaIso : (CFSG.LieType.Universal.Spin.quadOdd 2 (ZMod 7)).IsometryEquiv Qm :=
    ⟨sigma, fun v => Qm_sigma v⟩
  refine ⟨d, hd, (iso.trans sigmaIso).toLinearEquiv, fun t => ?_⟩
  simpa [QuadraticMap.smul_apply, smul_eq_mul] using (iso.trans sigmaIso).map_app t

private lemma lOne_apply (v : Fin 5 → ZMod 7) :
    lOne v = ![v 0 + v 1, v 1, v 2, v 3 - v 4, v 4] := by
  rw [lOne, ← LinearEquiv.coe_coe, Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]
  funext k
  fin_cases k <;> simp [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_five] <;>
    ring_nf <;> reduce_mod_char <;> ring

private lemma sOne_apply (v : Fin 5 → ZMod 7) :
    sOne v = ![v 0, v 1 + v 2 + 5 * v 3, v 2 + 3 * v 3, v 3, v 4] := by
  rw [sOne, ← LinearEquiv.coe_coe, Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]
  funext k
  fin_cases k <;> simp [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_five]

private lemma dTwo_apply (v : Fin 5 → ZMod 7) :
    dTwo v = ![v 0, 2 * v 1, v 2, 4 * v 3, v 4] := by
  rw [dTwo, ← LinearEquiv.coe_coe, Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]
  funext k
  fin_cases k <;> simp [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_five]

private lemma dTwo_symm_apply (v : Fin 5 → ZMod 7) :
    dTwo.symm v = ![v 0, 4 * v 1, v 2, 2 * v 3, v 4] := by
  rw [dTwo, ← LinearEquiv.coe_coe, Matrix.toLinearEquiv'_symm_apply, Matrix.toLin'_apply]
  change Matrix.mulVec (!![1, 0, 0, 0, 0; 0, 4, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 2, 0;
      0, 0, 0, 0, 1] : Matrix (Fin 5) (Fin 5) (ZMod 7)) v = _
  funext k
  fin_cases k <;> simp [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_five]

private lemma lOne_pow_apply (n : ℕ) : ∀ v : Fin 5 → ZMod 7,
    (lOne ^ n) v = ![v 0 + (n : ZMod 7) * v 1, v 1, v 2, v 3 - (n : ZMod 7) * v 4, v 4] := by
  induction n with
  | zero => intro v; funext i; fin_cases i <;> simp
  | succ n ih =>
      intro v
      rw [pow_succ, LinearEquiv.mul_apply, ih (lOne v), lOne_apply]
      funext i
      fin_cases i <;> simp [Nat.cast_succ] <;> ring

private lemma sOne_pow_apply (n : ℕ) : ∀ v : Fin 5 → ZMod 7,
    (sOne ^ n) v = ![v 0, v 1 + (n : ZMod 7) * v 2 + 5 * (n : ZMod 7) ^ 2 * v 3,
      v 2 + 3 * (n : ZMod 7) * v 3, v 3, v 4] := by
  induction n with
  | zero => intro v; funext i; fin_cases i <;> simp
  | succ n ih =>
      intro v
      rw [pow_succ, LinearEquiv.mul_apply, ih (sOne v), sOne_apply]
      funext i
      fin_cases i <;> simp [Nat.cast_succ] <;> ring_nf <;> reduce_mod_char <;> ring_nf

theorem dTwo_pow_three : dTwo ^ 3 = 1 := by
  ext v i
  fin_cases i <;>
    simp [pow_succ, pow_one, pow_zero, LinearEquiv.mul_apply, LinearEquiv.coe_one,
      dTwo_apply] <;>
    ring_nf <;> reduce_mod_char <;> ring_nf

theorem dTwo_conj_lOne : dTwo * lOne * dTwo⁻¹ = lOne ^ 4 := by
  ext v i
  fin_cases i <;>
    simp [LinearEquiv.mul_apply, LinearEquiv.coe_inv, dTwo_symm_apply, lOne_apply,
      dTwo_apply, lOne_pow_apply] <;>
    ring_nf <;> reduce_mod_char <;> ring_nf

theorem dTwo_conj_sOne : dTwo * sOne * dTwo⁻¹ = sOne ^ 2 := by
  ext v i
  fin_cases i <;>
    simp [LinearEquiv.mul_apply, LinearEquiv.coe_inv, dTwo_symm_apply, sOne_apply,
      dTwo_apply, sOne_pow_apply] <;>
    ring_nf <;> reduce_mod_char <;> ring_nf

private lemma sum_lOne_range_four (x : Fin 5 → ZMod 7) :
    (∑ k ∈ Finset.range 4, (lOne ^ k) x) =
      ![4 * x 0 + 6 * x 1, 4 * x 1, 4 * x 2, 4 * x 3 - 6 * x 4, 4 * x 4] := by
  funext i
  fin_cases i <;>
    simp [Finset.sum_apply, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.sum_range_one, pow_zero, pow_one, pow_succ, LinearEquiv.mul_apply,
      LinearEquiv.coe_one, lOne_apply] <;>
    ring_nf <;> reduce_mod_char <;> ring

private lemma sum_sOne_range_two (y : Fin 5 → ZMod 7) :
    (∑ k ∈ Finset.range 2, (sOne ^ k) y) =
      ![2 * y 0, 2 * y 1 + y 2 + 5 * y 3, 2 * y 2 + 3 * y 3, 2 * y 3, 2 * y 4] := by
  funext i
  fin_cases i <;>
    simp [Finset.sum_apply, Finset.sum_range_succ, Finset.sum_range_zero,
      Finset.sum_range_one, pow_zero, pow_one, pow_succ, LinearEquiv.mul_apply,
      LinearEquiv.coe_one, sOne_apply] <;>
    ring_nf <;> reduce_mod_char <;> ring

theorem cocycle_exists (x y : Fin 5 → ZMod 7)
    (hx : ∑ k ∈ Finset.range 4, (lOne ^ k) x = dTwo x)
    (hy : ∑ k ∈ Finset.range 2, (sOne ^ k) y = dTwo y) :
    ∃ t, lOne t - t = x ∧ sOne t - t = y := by
  rw [sum_lOne_range_four, dTwo_apply] at hx
  rw [sum_sOne_range_two, dTwo_apply] at hy
  have key2 : ∀ a : ZMod 7, 2 * a = 0 → a = 0 := by decide
  have key3 : ∀ a : ZMod 7, 3 * a = 0 → a = 0 := by decide
  have keyneg2 : ∀ a : ZMod 7, -2 * a = 0 → a = 0 := by decide
  have hx1 : x 1 = 0 :=
    key2 _ (by have h := congrFun hx 1; simp at h; linear_combination h)
  have hx2 : x 2 = 0 :=
    key3 _ (by have h := congrFun hx 2; simp at h; linear_combination h)
  have hx4 : x 4 = 0 :=
    key3 _ (by have h := congrFun hx 4; simp at h; linear_combination h)
  have hx0 : x 0 = 0 :=
    key3 _ (by have h := congrFun hx 0; simp [hx1] at h; linear_combination h)
  have hy0 : y 0 = 0 := by have h := congrFun hy 0; simp at h; linear_combination h
  have hy4 : y 4 = 0 := by have h := congrFun hy 4; simp at h; linear_combination h
  have hy3 : y 3 = 0 :=
    keyneg2 _ (by have h := congrFun hy 3; simp at h; linear_combination h)
  have hy2 : y 2 = 0 := by have h := congrFun hy 2; simp [hy3] at h; linear_combination h
  refine ⟨![0, 0, y 1, 0, -x 3], ?_, ?_⟩
  · funext i
    fin_cases i <;> simp [lOne_apply, hx0, hx1, hx2, hx4]
  · funext i
    fin_cases i <;> simp [sOne_apply, hy0, hy2, hy3, hy4]

private lemma reflect_smul [Fact (Nat.Prime 7)] (a : Fin 5 → ZMod 7) (k : ZMod 7)
    (hk : Qm a * k = 1) (x : Fin 5 → ZMod 7) :
    CFSG.ClassicalGroups.Orthogonal.reflect Qm a x =
      x - ((Qm (a + x) - Qm a - Qm x) * k) • a := by
  have ha : Qm a ≠ 0 := left_ne_zero_of_mul_eq_one hk
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply ha, div_eq_mul_inv,
    inv_eq_of_mul_eq_one_right hk]
  rfl

private lemma zmod7_one_ne_zero : (1 : ZMod 7) ≠ 0 := by decide

private lemma zmod7_three_ne_zero : (3 : ZMod 7) ≠ 0 := by decide

local macro "rk " "(" a:term ", " k:term ")" : term =>
  `(reflect_smul $a $k (by rw [Qm_apply]; decide +revert))

local macro "reflect_ext" "[" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  refine (Pi.basisFun (ZMod 7) (Fin 5)).ext' fun i => ?_
  fin_cases i <;>
  simp only [Pi.basisFun_apply, LinearEquiv.mul_apply, lOne, sOne, dTwo,
    Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_five, Qm_apply, $xs,*] <;>
  decide +revert))

private lemma classRefl_mem [Fact (Nat.Prime 7)] {c : ZMod 7} (hc : c ≠ 0)
    {a : Fin 5 → ZMod 7} (ha : Qm a = c) :
    CFSG.ClassicalGroups.Orthogonal.reflect Qm a ∈ closure (ClassRefl 7 Qm c) :=
  Subgroup.subset_closure
    ((mem_classRefl_iff (p := 7) (by norm_num) Qm_nondegenerate hc _).mpr ⟨a, ha, rfl⟩)

local macro "rm" : tactic => `(tactic|
  first
    | exact classRefl_mem zmod7_one_ne_zero (by rw [Qm_apply]; decide +revert)
    | exact classRefl_mem zmod7_three_ne_zero (by rw [Qm_apply]; decide +revert))

private lemma sOne_mem_one [Fact (Nat.Prime 7)] :
    sOne ∈ closure (ClassRefl 7 Qm (1 : ZMod 7)) := by
  rw [show sOne = (CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 0, 1, 0, 0] *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 3, 1, 0, 0]) by
    reflect_ext [rk (![0, 0, 1, 0, 0], 1), rk (![0, 3, 1, 0, 0], 1)]]
  repeat (first | apply Subgroup.mul_mem | rm)

private lemma dTwo_mem_one [Fact (Nat.Prime 7)] :
    dTwo ∈ closure (ClassRefl 7 Qm (1 : ZMod 7)) := by
  rw [show dTwo = (CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 1, 0, 1, 0] *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 5, 0, 3, 0]) by
    reflect_ext [rk (![0, 1, 0, 1, 0], 1), rk (![0, 5, 0, 3, 0], 1)]]
  repeat (first | apply Subgroup.mul_mem | rm)

private lemma lOne_mem_one [Fact (Nat.Prime 7)] :
    lOne ∈ closure (ClassRefl 7 Qm (1 : ZMod 7)) := by
  rw [show lOne = (((CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 0, 1, 6, 0] *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![1, 0, 1, 6, 0]) *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 0, 1, 0, 0]) *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![6, 0, 1, 0, 0]) by
    reflect_ext [rk (![0, 0, 1, 6, 0], 1), rk (![1, 0, 1, 6, 0], 1),
      rk (![0, 0, 1, 0, 0], 1), rk (![6, 0, 1, 0, 0], 1)]]
  repeat (first | apply Subgroup.mul_mem | rm)

private lemma sOne_mem_three [Fact (Nat.Prime 7)] :
    sOne ∈ closure (ClassRefl 7 Qm (3 : ZMod 7)) := by
  rw [show sOne = (((CFSG.ClassicalGroups.Orthogonal.reflect Qm ![3, 0, 2, 0, 2] *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![3, 1, 2, 0, 2]) *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![1, 0, 0, 0, 3]) *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![6, 3, 0, 0, 4]) by
    reflect_ext [rk (![3, 0, 2, 0, 2], 5), rk (![3, 1, 2, 0, 2], 5),
      rk (![1, 0, 0, 0, 3], 5), rk (![6, 3, 0, 0, 4], 5)]]
  repeat (first | apply Subgroup.mul_mem | rm)

private lemma dTwo_mem_three [Fact (Nat.Prime 7)] :
    dTwo ∈ closure (ClassRefl 7 Qm (3 : ZMod 7)) := by
  rw [show dTwo = (CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 1, 0, 3, 0] *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 5, 0, 2, 0]) by
    reflect_ext [rk (![0, 1, 0, 3, 0], 5), rk (![0, 5, 0, 2, 0], 5)]]
  repeat (first | apply Subgroup.mul_mem | rm)

private lemma lOne_mem_three [Fact (Nat.Prime 7)] :
    lOne ∈ closure (ClassRefl 7 Qm (3 : ZMod 7)) := by
  rw [show lOne = (((CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 3, 0, 1, 0] *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![6, 4, 0, 6, 0]) *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![0, 2, 0, 5, 0]) *
      CFSG.ClassicalGroups.Orthogonal.reflect Qm ![5, 5, 0, 2, 0]) by
    reflect_ext [rk (![0, 3, 0, 1, 0], 5), rk (![6, 4, 0, 6, 0], 5),
      rk (![0, 2, 0, 5, 0], 5), rk (![5, 5, 0, 2, 0], 5)]]
  repeat (first | apply Subgroup.mul_mem | rm)

private lemma exists_sq_or_three_sq (c : ZMod 7) (hc : c ≠ 0) :
    (∃ s : ZMod 7, s ≠ 0 ∧ c = s ^ 2 * 1) ∨
      (∃ s : ZMod 7, s ≠ 0 ∧ c = s ^ 2 * 3) := by
  revert c
  decide

theorem mem_closure_classRefl {c : ZMod 7} (hc : c ≠ 0) :
    lOne ∈ closure (ClassRefl 7 Qm c) ∧ sOne ∈ closure (ClassRefl 7 Qm c) ∧
      dTwo ∈ closure (ClassRefl 7 Qm c) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rcases exists_sq_or_three_sq c hc with ⟨s, hs, hc'⟩ | ⟨s, hs, hc'⟩
  · rw [hc', classRefl_sq_mul (Q := Qm) (c := 1) (s := s) hs]
    exact ⟨lOne_mem_one, sOne_mem_one, dTwo_mem_one⟩
  · rw [hc', classRefl_sq_mul (Q := Qm) (c := 3) (s := s) hs]
    exact ⟨lOne_mem_three, sOne_mem_three, dTwo_mem_three⟩

private noncomputable def lMat : Matrix (Fin 5) (Fin 5) (ZMod 7) :=
  !![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 6; 0, 0, 0, 0, 1]

private noncomputable def sMat : Matrix (Fin 5) (Fin 5) (ZMod 7) :=
  !![1, 0, 0, 0, 0; 0, 1, 1, 5, 0; 0, 0, 1, 3, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

private noncomputable def lSL : Matrix.SpecialLinearGroup (Fin 5) (ZMod 7) :=
  ⟨lMat, by
    rw [lMat, Matrix.det_of_isUpperTriangular (by decide)]
    decide⟩

private noncomputable def sSL : Matrix.SpecialLinearGroup (Fin 5) (ZMod 7) :=
  ⟨sMat, by
    rw [sMat, Matrix.det_of_isUpperTriangular (by decide)]
    decide⟩

private lemma lOne_eq_toLin : lOne = Matrix.SpecialLinearGroup.toLin' lSL := by
  apply LinearEquiv.toLinearMap_injective
  rw [Matrix.SpecialLinearGroup.toLin'_to_linearMap]
  unfold lOne
  rw [Matrix.toLinearEquiv'_apply]
  rfl

private lemma sOne_eq_toLin : sOne = Matrix.SpecialLinearGroup.toLin' sSL := by
  apply LinearEquiv.toLinearMap_injective
  rw [Matrix.SpecialLinearGroup.toLin'_to_linearMap]
  unfold sOne
  rw [Matrix.toLinearEquiv'_apply]
  rfl

private lemma lSL_mem_unitriangular [Fact (Nat.Prime 7)] :
    lSL ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 5 (ZMod 7) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_unitriangular]
  constructor
  · change lMat.IsUpperTriangular
    decide +revert
  · change ∀ i : Fin 5, lMat i i = 1
    decide +revert

private lemma sSL_mem_unitriangular [Fact (Nat.Prime 7)] :
    sSL ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 5 (ZMod 7) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_unitriangular]
  constructor
  · change sMat.IsUpperTriangular
    decide +revert
  · change ∀ i : Fin 5, sMat i i = 1
    decide +revert

private abbrev H : Subgroup ((Fin 5 → ZMod 7) ≃ₗ[ZMod 7] (Fin 5 → ZMod 7)) :=
  closure ({lOne, sOne} : Set ((Fin 5 → ZMod 7) ≃ₗ[ZMod 7] (Fin 5 → ZMod 7)))

private lemma isPGroup_closure : IsPGroup 7 H := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hpgU : IsPGroup 7
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 5 (ZMod 7)) :=
    IsPGroup.of_card (by
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_unitriangular, Nat.card_zmod])
  refine (hpgU.map (Matrix.SpecialLinearGroup.toLin' :
    Matrix.SpecialLinearGroup (Fin 5) (ZMod 7) →*
      ((Fin 5 → ZMod 7) ≃ₗ[ZMod 7] (Fin 5 → ZMod 7)))).to_le ?_
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact Subgroup.mem_map.mpr ⟨lSL, lSL_mem_unitriangular, lOne_eq_toLin.symm⟩
  · exact Subgroup.mem_map.mpr ⟨sSL, sSL_mem_unitriangular, sOne_eq_toLin.symm⟩

private lemma inv_eq_pow_six {G : Type*} [Group G] (g : G) (h : g ^ 7 = 1) : g⁻¹ = g ^ 6 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', h]

private lemma lOne_inv_apply (v : Fin 5 → ZMod 7) :
    lOne.symm v = ![v 0 + 6 * v 1, v 1, v 2, v 3 + v 4, v 4] := by
  rw [lOne, ← LinearEquiv.coe_coe, Matrix.toLinearEquiv'_symm_apply, Matrix.toLin'_apply]
  change Matrix.mulVec (!![1, 6, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 1;
      0, 0, 0, 0, 1] : Matrix (Fin 5) (Fin 5) (ZMod 7)) v = _
  funext k
  fin_cases k <;> simp [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_five]

private lemma sOne_inv_apply (v : Fin 5 → ZMod 7) :
    sOne.symm v = ![v 0, v 1 + 6 * v 2 + 5 * v 3, v 2 + 4 * v 3, v 3, v 4] := by
  rw [sOne, ← LinearEquiv.coe_coe, Matrix.toLinearEquiv'_symm_apply, Matrix.toLin'_apply]
  change Matrix.mulVec (!![1, 0, 0, 0, 0; 0, 1, 6, 5, 0; 0, 0, 1, 4, 0; 0, 0, 0, 1, 0;
      0, 0, 0, 0, 1] : Matrix (Fin 5) (Fin 5) (ZMod 7)) v = _
  funext k
  fin_cases k <;> simp [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_five]

private noncomputable def C : (Fin 5 → ZMod 7) ≃ₗ[ZMod 7] (Fin 5 → ZMod 7) :=
  lOne * sOne * lOne⁻¹ * sOne⁻¹

private noncomputable def Z : (Fin 5 → ZMod 7) ≃ₗ[ZMod 7] (Fin 5 → ZMod 7) :=
  sOne * C * sOne⁻¹ * C⁻¹

private lemma C_apply (v : Fin 5 → ZMod 7) :
    C v = ![v 0 + v 2 + 2 * v 3 + 5 * v 4, v 1 - 2 * v 4, v 2 + 3 * v 4, v 3, v 4] := by
  simp only [C, LinearEquiv.mul_apply, LinearEquiv.coe_inv, sOne_inv_apply, lOne_inv_apply,
    sOne_apply, lOne_apply]
  funext i
  fin_cases i <;> simp <;> ring_nf <;> reduce_mod_char <;> ring_nf <;> reduce_mod_char

private lemma C_pow_apply (n : ℕ) : ∀ v : Fin 5 → ZMod 7,
    (C ^ n) v = ![v 0 + (n : ZMod 7) * v 2 + 2 * (n : ZMod 7) * v 3 +
        5 * (n : ZMod 7) ^ 2 * v 4,
      v 1 - 2 * (n : ZMod 7) * v 4, v 2 + 3 * (n : ZMod 7) * v 4, v 3, v 4] := by
  induction n with
  | zero => intro v; funext i; fin_cases i <;> simp
  | succ n ih =>
      intro v
      rw [pow_succ, LinearEquiv.mul_apply, ih (C v), C_apply]
      funext i
      fin_cases i <;> simp [Nat.cast_succ] <;> ring_nf <;> reduce_mod_char

private lemma C_pow_seven : C ^ 7 = 1 := by
  apply LinearEquiv.ext
  intro v
  rw [C_pow_apply]
  funext i
  fin_cases i <;> simp <;> ring_nf <;> reduce_mod_char

private lemma C_inv_eq : C⁻¹ = C ^ 6 := inv_eq_pow_six C C_pow_seven

private lemma C_inv_apply (v : Fin 5 → ZMod 7) :
    C⁻¹ v = ![v 0 + 6 * v 2 + 2 * 6 * v 3 + 5 * 6 ^ 2 * v 4,
      v 1 - 2 * 6 * v 4, v 2 + 3 * 6 * v 4, v 3, v 4] := by
  rw [C_inv_eq, C_pow_apply]
  rfl

private lemma Z_apply (v : Fin 5 → ZMod 7) :
    Z v = ![v 0 + 4 * v 3, v 1 + 3 * v 4, v 2, v 3, v 4] := by
  simp only [Z, LinearEquiv.mul_apply, LinearEquiv.coe_inv, C_inv_apply, sOne_inv_apply,
    C_apply, sOne_apply]
  funext i
  fin_cases i <;> simp <;> ring_nf <;> reduce_mod_char

private lemma Z_pow_apply (n : ℕ) : ∀ v : Fin 5 → ZMod 7,
    (Z ^ n) v = ![v 0 + 4 * (n : ZMod 7) * v 3, v 1 + 3 * (n : ZMod 7) * v 4, v 2, v 3, v 4] := by
  induction n with
  | zero => intro v; funext i; fin_cases i <;> simp
  | succ n ih =>
      intro v
      rw [pow_succ, LinearEquiv.mul_apply, ih (Z v), Z_apply]
      funext i
      fin_cases i <;> simp [Nat.cast_succ] <;> ring

private lemma pow_prod_coords (a b c d : ℕ) :
    ((lOne ^ a * sOne ^ b * C ^ c * Z ^ d) ![0, 0, 0, 0, 1]) 3 = -(a : ZMod 7) ∧
    ((lOne ^ a * sOne ^ b * C ^ c * Z ^ d) ![0, 0, 0, 0, 1]) 2 = 3 * (c : ZMod 7) ∧
    ((lOne ^ a * sOne ^ b * C ^ c * Z ^ d) ![0, 0, 0, 1, 0]) 2 = 3 * (b : ZMod 7) ∧
    ((lOne ^ a * sOne ^ b * C ^ c * Z ^ d) ![0, 0, 0, 1, 0]) 0 =
      4 * (d : ZMod 7) + 2 * (c : ZMod 7) + 5 * (a : ZMod 7) * (b : ZMod 7) ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [LinearEquiv.mul_apply, lOne_pow_apply, sOne_pow_apply, C_pow_apply, Z_pow_apply]
  all_goals simp
  all_goals ring_nf
  all_goals reduce_mod_char

private lemma fin7_natCast_injective {a b : Fin 7}
    (h : ((a : ℕ) : ZMod 7) = ((b : ℕ) : ZMod 7)) : a = b := by
  have hc := (ZMod.natCast_eq_natCast_iff' (a : ℕ) (b : ℕ) 7).mp h
  rw [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at hc
  exact Fin.ext hc

private lemma four_ne_zero_zmod_seven : (4 : ZMod 7) ≠ 0 := by decide

private noncomputable def powElem (a b c d : ℕ) : H :=
  ⟨lOne ^ a * sOne ^ b * C ^ c * Z ^ d, by
    have hl : lOne ∈ H := Subgroup.subset_closure (by simp)
    have hs : sOne ∈ H := Subgroup.subset_closure (by simp)
    have hC : C ∈ H := by
      rw [C]
      exact mul_mem (mul_mem (mul_mem hl hs) (inv_mem hl)) (inv_mem hs)
    have hZ : Z ∈ H := by
      rw [Z]
      exact mul_mem (mul_mem (mul_mem hs hC) (inv_mem hs)) (inv_mem hC)
    exact mul_mem (mul_mem (mul_mem (pow_mem hl a) (pow_mem hs b)) (pow_mem hC c))
      (pow_mem hZ d)⟩

theorem pow_four_dvd_card_closure :
    7 ^ 4 ∣ Nat.card (closure
      ({lOne, sOne} : Set ((Fin 5 → ZMod 7) ≃ₗ[ZMod 7] (Fin 5 → ZMod 7)))) := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Finite ((Fin 5 → ZMod 7) ≃ₗ[ZMod 7] (Fin 5 → ZMod 7)) :=
    Finite.of_injective
      (fun e : (Fin 5 → ZMod 7) ≃ₗ[ZMod 7] (Fin 5 → ZMod 7) =>
        (e : (Fin 5 → ZMod 7) → (Fin 5 → ZMod 7)))
      (fun a b h => LinearEquiv.ext (fun x => congrFun h x))
  change 7 ^ 4 ∣ Nat.card H
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 7) (G := H)).mp isPGroup_closure
  have hinj : Function.Injective (fun p : Fin 7 × Fin 7 × Fin 7 × Fin 7 =>
      powElem p.1 p.2.1 p.2.2.1 p.2.2.2) := by
    rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ hpq
    have hval : lOne ^ (a : ℕ) * sOne ^ (b : ℕ) * C ^ (c : ℕ) * Z ^ (d : ℕ) =
        lOne ^ (a' : ℕ) * sOne ^ (b' : ℕ) * C ^ (c' : ℕ) * Z ^ (d' : ℕ) := by
      simpa only [powElem] using congrArg Subtype.val hpq
    obtain ⟨h4, h2, h3, h0⟩ := pow_prod_coords a b c d
    obtain ⟨h4', h2', h3', h0'⟩ := pow_prod_coords a' b' c' d'
    have haZ : ((a : ℕ) : ZMod 7) = ((a' : ℕ) : ZMod 7) := by
      have h := congrArg (fun e => (e ![0, 0, 0, 0, 1]) 3) hval
      rw [h4, h4'] at h
      exact neg_inj.mp h
    have hcZ : ((c : ℕ) : ZMod 7) = ((c' : ℕ) : ZMod 7) := by
      have h := congrArg (fun e => (e ![0, 0, 0, 0, 1]) 2) hval
      rw [h2, h2'] at h
      exact mul_left_cancel₀ zmod7_three_ne_zero h
    have hbZ : ((b : ℕ) : ZMod 7) = ((b' : ℕ) : ZMod 7) := by
      have h := congrArg (fun e => (e ![0, 0, 0, 1, 0]) 2) hval
      rw [h3, h3'] at h
      exact mul_left_cancel₀ zmod7_three_ne_zero h
    have hdZ : ((d : ℕ) : ZMod 7) = ((d' : ℕ) : ZMod 7) := by
      have h := congrArg (fun e => (e ![0, 0, 0, 1, 0]) 0) hval
      rw [h0, h0', haZ, hbZ, hcZ] at h
      refine mul_left_cancel₀ four_ne_zero_zmod_seven ?_
      linear_combination (norm := (ring_nf; try reduce_mod_char)) h
    exact Prod.ext (fin7_natCast_injective haZ) (Prod.ext (fin7_natCast_injective hbZ)
      (Prod.ext (fin7_natCast_injective hcZ) (fin7_natCast_injective hdZ)))
  have hle4 : 7 ^ 4 ≤ Nat.card H := by
    have hdom : Nat.card (Fin 7 × Fin 7 × Fin 7 × Fin 7) = 7 ^ 4 := by
      rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_fin]
      norm_num
    rw [← hdom]
    exact Nat.card_le_card_of_injective _ hinj
  rw [hk] at hle4
  have hk4 : 4 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 7)).mp hle4
  rw [hk]
  exact pow_dvd_pow 7 hk4

theorem exists_splitData {T : Type} [AddCommGroup T] [Module (ZMod 7) T]
    [Module.Finite (ZMod 7) T] (hT : Module.finrank (ZMod 7) T = 5)
    {Q : QuadraticForm (ZMod 7) T} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {c : ZMod 7} (hc : c ≠ 0) :
    ∃ ℓ s d : T ≃ₗ[ZMod 7] T,
      ℓ ∈ closure (ClassRefl 7 Q c) ∧ s ∈ closure (ClassRefl 7 Q c) ∧
      d ∈ closure (ClassRefl 7 Q c) ∧ d ^ 3 = 1 ∧
      d * ℓ * d⁻¹ = ℓ ^ 4 ∧ d * s * d⁻¹ = s ^ 2 ∧
      (∀ x y : T, ∑ k ∈ Finset.range 4, (ℓ ^ k) x = d x →
        ∑ k ∈ Finset.range 2, (s ^ k) y = d y → ∃ t, ℓ t - t = x ∧ s t - t = y) ∧
      ¬ 7 ∣ (closure ({ℓ, s} : Set (T ≃ₗ[ZMod 7] T))).relIndex
        (closure (ClassRefl 7 Q c)) := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨μ, hμ, e, he⟩ := exists_isometry hT hQ
  have he' : ∀ v : Fin 5 → ZMod 7, (μ • Q) (e.symm v) = Qm v := by
    intro v
    rw [QuadraticMap.smul_apply, smul_eq_mul, ← he (e.symm v),
      LinearEquiv.apply_symm_apply]
  let φ : ((Fin 5 → ZMod 7) ≃ₗ[ZMod 7] (Fin 5 → ZMod 7)) ≃* (T ≃ₗ[ZMod 7] T) :=
    { toFun := fun x => e.trans (x.trans e.symm)
      invFun := fun y => e.symm.trans (y.trans e)
      left_inv := by intro x; ext w; simp
      right_inv := by intro y; ext w; simp
      map_mul' := by intro x y; ext w; simp }
  have hmap : ∀ (g : (Fin 5 → ZMod 7) ≃ₗ[ZMod 7] (Fin 5 → ZMod 7)) (t : T),
      e (φ g t) = g (e t) := fun g t => by
    change e (e.symm (g (e t))) = g (e t)
    rw [LinearEquiv.apply_symm_apply]
  have hmem := mem_closure_classRefl (c := μ * c) (mul_ne_zero hμ hc)
  have hsplit : Subgroup.closure (ClassRefl 7 Q c) =
      Subgroup.closure (ClassRefl 7 (μ • Q) (μ * c)) := by
    rw [classRefl_smul hμ]
  obtain ⟨ψ, hψ⟩ := wit_classRefl_transport (p := 7) (by norm_num) (by norm_num)
    (Q := Qm) (Q' := μ • Q) (e := e.symm) he' (c := μ * c) (hA := rfl) (hA' := hsplit)
  set ℓ : T ≃ₗ[ZMod 7] T := φ lOne with hℓ
  set s : T ≃ₗ[ZMod 7] T := φ sOne with hs
  set d : T ≃ₗ[ZMod 7] T := φ dTwo with hd
  have hφmem : ∀ g ∈ Subgroup.closure (ClassRefl 7 Qm (μ * c)),
      φ g ∈ Subgroup.closure (ClassRefl 7 Q c) := fun g hg => by
    have h := (ψ ⟨g, hg⟩).2
    rwa [hψ ⟨g, hg⟩] at h
  have hℓ_mem : ℓ ∈ Subgroup.closure (ClassRefl 7 Q c) := by
    rw [hℓ]; exact hφmem lOne hmem.1
  have hs_mem : s ∈ Subgroup.closure (ClassRefl 7 Q c) := by
    rw [hs]; exact hφmem sOne hmem.2.1
  have hd_mem : d ∈ Subgroup.closure (ClassRefl 7 Q c) := by
    rw [hd]; exact hφmem dTwo hmem.2.2
  have hd_pow : d ^ 3 = 1 := by rw [hd, ← map_pow, dTwo_pow_three, map_one]
  have hd_conj_l : d * ℓ * d⁻¹ = ℓ ^ 4 := by
    rw [hd, hℓ, ← map_mul, ← map_inv, ← map_mul, dTwo_conj_lOne, map_pow]
  have hd_conj_s : d * s * d⁻¹ = s ^ 2 := by
    rw [hd, hs, ← map_mul, ← map_inv, ← map_mul, dTwo_conj_sOne, map_pow]
  have hsum : ∀ (g : (Fin 5 → ZMod 7) ≃ₗ[ZMod 7] (Fin 5 → ZMod 7)) (k : ℕ) (z : T),
      ∑ i ∈ Finset.range k, (g ^ i) (e z) = e (∑ i ∈ Finset.range k, ((φ g) ^ i) z) := by
    intro g k z
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← map_pow]
      exact (hmap (g ^ i) z).symm
  have hcocy : ∀ x y : T, ∑ k ∈ Finset.range 4, (ℓ ^ k) x = d x →
      ∑ k ∈ Finset.range 2, (s ^ k) y = d y →
      ∃ t, ℓ t - t = x ∧ s t - t = y := by
    intro x y hx hy
    have hx' : ∑ k ∈ Finset.range 4, (lOne ^ k) (e x) = dTwo (e x) := by
      rw [hsum lOne 4 x, ← hℓ, hx, hd]
      exact hmap dTwo x
    have hy' : ∑ k ∈ Finset.range 2, (sOne ^ k) (e y) = dTwo (e y) := by
      rw [hsum sOne 2 y, ← hs, hy, hd]
      exact hmap dTwo y
    obtain ⟨t₀, ht₀l, ht₀s⟩ := cocycle_exists (e x) (e y) hx' hy'
    refine ⟨e.symm t₀, ?_, ?_⟩
    · apply e.injective
      rw [map_sub, hℓ, hmap lOne (e.symm t₀), LinearEquiv.apply_symm_apply]
      exact ht₀l
    · apply e.injective
      rw [map_sub, hs, hmap sOne (e.symm t₀), LinearEquiv.apply_symm_apply]
      exact ht₀s
  have hH_le_K : Subgroup.closure ({ℓ, s} : Set (T ≃ₗ[ZMod 7] T)) ≤
      Subgroup.closure (ClassRefl 7 Q c) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hℓ_mem
    · exact hs_mem
  have hR_le_O : Subgroup.closure (ClassRefl 7 Q c) ≤
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    (Subgroup.closure_le _).mpr fun t ht =>
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr
        (isIsom_of_mem_closure_classRefl (p := 7) (Q := Q) (c := c)
          (Subgroup.subset_closure ht))
  have hR_dvd_O : Nat.card (Subgroup.closure (ClassRefl 7 Q c)) ∣
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    Subgroup.card_dvd_of_le hR_le_O
  have h2char : ringChar (ZMod 7) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; decide
  have hcardZ := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd (K := ZMod 7)
    (V := T) h2char (Q := Q) hQ (n := 2) (by norm_num [hT])
  have hO_card : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 553190400 := by
    have h : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) = 553190400 := by
      rw [hcardZ, Nat.card_zmod]
      norm_num [Finset.prod_Icc_succ_top, Finset.prod_empty]
    exact_mod_cast h
  have hmap_cl : φ.mapSubgroup (Subgroup.closure ({lOne, sOne} :
      Set ((Fin 5 → ZMod 7) ≃ₗ[ZMod 7] (Fin 5 → ZMod 7)))) =
      Subgroup.closure ({ℓ, s} : Set (T ≃ₗ[ZMod 7] T)) := by
    rw [MulEquiv.coe_mapSubgroup, MonoidHom.map_closure, Set.image_pair]
    simp [hℓ, hs]
  have hcard : Nat.card (Subgroup.closure ({lOne, sOne} :
      Set ((Fin 5 → ZMod 7) ≃ₗ[ZMod 7] (Fin 5 → ZMod 7)))) =
      Nat.card (Subgroup.closure ({ℓ, s} : Set (T ≃ₗ[ZMod 7] T))) := by
    rw [← hmap_cl]
    exact (Subgroup.card_mapSubgroup (H := Subgroup.closure ({lOne, sOne} :
      Set ((Fin 5 → ZMod 7) ≃ₗ[ZMod 7] (Fin 5 → ZMod 7)))) φ).symm
  refine ⟨ℓ, s, d, hℓ_mem, hs_mem, hd_mem, hd_pow, hd_conj_l, hd_conj_s, hcocy, ?_⟩
  intro h7
  have hbad : 7 ^ 5 ∣ 553190400 := by
    rw [← hO_card]
    refine dvd_trans ?_ hR_dvd_O
    have h := Subgroup.relIndex_mul_card
      (H := Subgroup.closure ({ℓ, s} : Set (T ≃ₗ[ZMod 7] T)))
      (K := Subgroup.closure (ClassRefl 7 Q c))
    rw [inf_eq_left.mpr hH_le_K] at h
    rw [← h, show (7 : ℕ) ^ 5 = 7 * 7 ^ 4 by norm_num]
    exact Nat.mul_dvd_mul h7 (by rw [← hcard]; exact pow_four_dvd_card_closure)
  norm_num at hbad

end CFSG.StandardType.OFiveSeven

end
