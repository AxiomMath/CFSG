module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusWtDefs
public import CFSG.LieType.Universal.Spin.Twisted.Torus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mTorus

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.SmallO8mTorus

theorem omq_exists_shortField_embedding {K : Type} [Field K] (b c : K) {k : Type} [Field k]
    [IsAlgClosed k] (ι : K →+* k) :
    ∃ ι' : ShortField b c →+* k, ∀ x : K, ι' (algebraMap K (ShortField b c) x) = ι x := by
  letI : Algebra K k := ι.toAlgebra
  have hdeg : (Polynomial.C (1 : k) * Polynomial.X ^ 2 + Polynomial.C (-(ι b)) * Polynomial.X +
      Polynomial.C (ι c)).degree ≠ 0 := by
    rw [Polynomial.degree_quadratic one_ne_zero]
    norm_num
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root _ hdeg
  have hu : r * r = (-c) • (1 : k) + b • r := by
    simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] at hr
    simp only [Algebra.smul_def, map_neg, mul_one]
    change r * r = -(ι c) + ι b * r
    linear_combination hr
  let φ := QuadraticAlgebra.lift ⟨r, hu⟩
  exact ⟨φ.toRingHom, fun x => φ.commutes x⟩

theorem omq_shortField_pow_card_succ {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (x : ShortField b c) :
    x ^ (Nat.card K + 1) = algebraMap K (ShortField b c) (QuadraticAlgebra.norm x) := by
  haveI := fact_shortField hirr
  let σ : ShortField b c ≃ₐ[K] ShortField b c :=
    { toFun := star
      invFun := star
      left_inv := star_star
      right_inv := star_star
      map_mul' := fun x y => by rw [star_mul, mul_comm]
      map_add' := star_add
      commutes' := fun r => by ext <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star] }
  have hb : b ≠ 0 := by
    intro hb
    obtain ⟨r, hr⟩ := isSquare_of_charTwo' (-c)
    exact (Fact.out : ∀ r : K, r ^ 2 ≠ -c + b * r) r (by simpa [hb, pow_two] using hr.symm)
  have hσ : σ ≠ 1 := by
    intro h
    have h' := congrArg (fun f : ShortField b c ≃ₐ[K] ShortField b c =>
      (f (QuadraticAlgebra.omega : ShortField b c)).re) h
    simp [σ, QuadraticAlgebra.re_star] at h'
    exact hb h'
  let : Fintype K := Fintype.ofFinite K
  have h := CFSG.LocalAnalysis.eq_pow_card_of_ne_one
    (QuadraticAlgebra.finrank_eq_two (R := K) (a := -c) (b := b)) hσ x
  change star x = _ at h
  rw [← Nat.card_eq_fintype_card] at h
  rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star, h, pow_succ, mul_comm]

@[expose] def OmqMinusToral (n : ℕ) {K : Type*} [Field K] {b c : K}
    (g : spinGroup (quadMinus n K b c)) (t : Fin (n - 1) → Kˣ) (z : ShortField b c) : Prop :=
  (∀ i, spinAction (quadMinus n K b c) g (eVec n i) = (t i : K) • eVec n i) ∧
    (∀ i, spinAction (quadMinus n K b c) g (fVec n i) = (((t i)⁻¹ : Kˣ) : K) • fVec n i) ∧
    QuadraticAlgebra.norm z = 1 ∧
    ∀ u : ShortField b c, spinAction (quadMinus n K b c) g (planeVec n (fieldCoord u)) =
      planeVec n (fieldCoord (z * u))

theorem OmqMinusToral.one (n : ℕ) {K : Type*} [Field K] {b c : K} :
    OmqMinusToral n (1 : spinGroup (quadMinus n K b c)) (fun _ => 1) (1 : ShortField b c) := by
  refine ⟨fun i => ?_, fun i => ?_, ?_, fun u => ?_⟩ <;> simp

theorem OmqMinusToral.mul {n : ℕ} {K : Type*} [Field K] {b c : K}
    {g g' : spinGroup (quadMinus n K b c)} {t t' : Fin (n - 1) → Kˣ} {z z' : ShortField b c}
    (h : OmqMinusToral n g t z) (h' : OmqMinusToral n g' t' z') :
    OmqMinusToral n (g * g') (t * t') (z * z') := by
  refine ⟨fun i => ?_, fun i => ?_, ?_, fun u => ?_⟩
  · rw [map_mul, LinearEquiv.mul_apply, h'.1 i, map_smul, h.1 i, smul_smul, Pi.mul_apply,
      Units.val_mul, mul_comm]
  · rw [map_mul, LinearEquiv.mul_apply, h'.2.1 i, map_smul, h.2.1 i, smul_smul, Pi.mul_apply,
      mul_inv, Units.val_mul, mul_comm]
  · rw [map_mul, h.2.2.1, h'.2.2.1, one_mul]
  · rw [map_mul, LinearEquiv.mul_apply, h'.2.2.2 u, h.2.2.2, mul_assoc]

theorem OmqMinusToral.mat_inl_inl {n : ℕ} {K : Type*} [Field K] {b c : K}
    {g : spinGroup (quadMinus n K b c)} {t : Fin (n - 1) → Kˣ} {z : ShortField b c}
    (h : OmqMinusToral n g t z) (i : Fin (n - 1)) : mat n g (.inl i) (.inl i) = (t i : K) := by
  rw [mat_apply]
  have e : (Pi.single (Sum.inl i) 1 : Vm n K) = eVec n i := rfl
  rw [e, h.1 i]
  simp [eVec]

private theorem c2slomqmw1_planeVec_one {n : ℕ} {K : Type*} [Field K] {b c : K} :
    planeVec n (fieldCoord (1 : ShortField b c)) = (Pi.single (.inr (.inr 0)) 1 : Vm n K) := by
  funext x
  rcases x with i | i | t
  · simp [planeVec, Pi.single_apply]
  · simp [planeVec, Pi.single_apply]
  · fin_cases t <;> simp [planeVec, fieldCoord, Pi.single_apply] <;> rfl

theorem OmqMinusToral.omqMinusZ_eq {n : ℕ} {K : Type*} [Field K] {b c : K}
    {g : spinGroup (quadMinus n K b c)} {t : Fin (n - 1) → Kˣ} {z : ShortField b c}
    (h : OmqMinusToral n g t z) : omqMinusZ n g = z := by
  have h1 := h.2.2.2 1
  rw [mul_one] at h1
  have e0 : mat n g (.inr (.inr 0)) (.inr (.inr 0)) = z.re := by
    rw [mat_apply, ← c2slomqmw1_planeVec_one (n := n) (b := b) (c := c), h1]
    simp [planeVec, fieldCoord]
  have e1 : mat n g (.inr (.inr 1)) (.inr (.inr 0)) = z.im := by
    rw [mat_apply, ← c2slomqmw1_planeVec_one (n := n) (b := b) (c := c), h1]
    simp [planeVec, fieldCoord]
  unfold omqMinusZ
  rw [e0, e1]

theorem omq_omMinus_wt_eq_of_toral {n : ℕ} {K : Type*} [Field K] {b c : K} {k : Type*} [Field k]
    {m h : ℕ} (ι : K →+* k) (ι' : ShortField b c →+* k) (ν : OmqMinusLat (n - 1) m h)
    {g : spinGroup (quadMinus n K b c)} {t : Fin (n - 1) → Kˣ} {z : ShortField b c}
    (hg : OmqMinusToral n g t z) :
    omqMinusWt n ι ι' ν g = (∏ i, ι (t i : K) ^ (ν.1 i).val) * ι' z ^ ν.2.val := by
  unfold omqMinusWt
  simp only [hg.mat_inl_inl, hg.omqMinusZ_eq]

theorem omq_omMinus_toral_longTorus {n : ℕ} {K : Type*} [Field K] {b c : K} {i : Fin (n - 1)}
    (hi : i.val + 1 < n - 1) (a : Kˣ) :
    OmqMinusToral n ((minusFrame n b c).longTorus (succ_ne_of_lt n hi) true false a)
      (fun l => if l = i then a else if l = ⟨i.val + 1, hi⟩ then a⁻¹ else 1)
      (1 : ShortField b c) := by
  refine ⟨fun l => ?_, fun l => ?_, by simp, fun u => ?_⟩
  · have h := spinAction_longTorus_eVec n (b := b) (c := c) hi a l
    rw [minusVec_true] at h
    rw [h]
    have h3 : (⟨i.val + 1, hi⟩ : Fin (n - 1)) ≠ i := (succ_ne_of_lt n hi).symm
    by_cases h1 : l = i
    · simp [h1]
    · by_cases h2 : l = ⟨i.val + 1, hi⟩ <;> simp [h1, h2, h3]
  · have h := spinAction_longTorus_minusVec_not n (b := b) (c := c) hi a l
    rw [minusVec_false] at h
    rw [h]
    have h3 : (⟨i.val + 1, hi⟩ : Fin (n - 1)) ≠ i := (succ_ne_of_lt n hi).symm
    by_cases h1 : l = i
    · simp [h1, longCoroot, succ_ne_of_lt n hi]
    · by_cases h2 : l = ⟨i.val + 1, hi⟩
      · simp [h1, h2, h3, longCoroot]
      · simp [h1, h2, longCoroot]
  · rw [one_mul]
    exact spinAction_longTorus_planeVec n (succ_ne_of_lt n hi) true false a _

theorem omq_omMinus_toral_shortTorusHom {n : ℕ} {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1)) (u : (ShortField b c)ˣ) :
    OmqMinusToral n (shortTorusHom n hirr i u)
      (fun l => if l = i then Units.map QuadraticAlgebra.norm u else 1)
      ((u : ShortField b c) / star (u : ShortField b c)) := by
  haveI := fact_shortField hirr
  have ha : fieldCoord (u : ShortField b c) ≠ 0 := fieldCoord_ne_zero u.ne_zero
  have hN : QuadraticAlgebra.norm (u : ShortField b c) ≠ 0 :=
    (QuadraticAlgebra.norm_eq_zero_iff_eq_zero).not.mpr u.ne_zero
  rw [shortTorusHom_apply]
  refine ⟨fun l => ?_, fun l => ?_, ?_, fun x => ?_⟩
  · by_cases hl : l = i
    · subst hl
      rw [spinAction_shortTorusElt_eVec n hirr l ha, planeNorm_fieldCoord]
      simp
    · rw [spinAction_shortTorusElt_eVec_of_ne n hirr hl]
      simp [hl]
  · by_cases hl : l = i
    · subst hl
      rw [spinAction_shortTorusElt_fVec n hirr l ha, planeNorm_fieldCoord]
      simp
    · rw [spinAction_shortTorusElt_fVec_of_ne n hirr hl]
      simp [hl]
  · have h1 : (u : ShortField b c) / star (u : ShortField b c) * star (u : ShortField b c) = u :=
      div_mul_cancel₀ _ (star_ne_zero.mpr u.ne_zero)
    have h2 := congrArg QuadraticAlgebra.norm h1
    rw [map_mul, QuadraticAlgebra.norm_star] at h2
    exact mul_right_cancel₀ hN (h2.trans (one_mul _).symm)
  · rw [spinAction_shortTorusElt_planeVec n hirr i ha]
    rw [planeRefl_comp_fieldCoord u x]

end CFSG.LocalAnalysis.WeakClosure81
