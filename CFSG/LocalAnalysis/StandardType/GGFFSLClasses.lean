module

public import CFSG.LocalAnalysis.StandardType.GGFFModelDefs
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFWreath
import CFSG.LocalAnalysis.StandardType.GGFFSLClassesK

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.GGFF

open Matrix
open scoped MatrixGroups
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)
open CFSG.RankThree.PartTwo.Sec4.RonanK429F (W6.T W7.T)
open CFSG.RankThree.PartTwo.Sec4.RonanK429F

private def fixCount (n : ℕ) (M : Matrix (Fin n) (Fin n) (ZMod 2)) : ℕ :=
  (Finset.univ.filter fun u : Fin n → ZMod 2 => M *ᵥ u = u).card

private theorem card_fix_conj {n : ℕ} {x y : SL(n, ZMod 2)} (h : IsConj x y) :
    fixCount n (x : Matrix (Fin n) (Fin n) (ZMod 2)) =
      fixCount n (y : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have hcM : (y : Matrix (Fin n) (Fin n) (ZMod 2)) =
      (c : Matrix (Fin n) (Fin n) (ZMod 2)) * (x : Matrix (Fin n) (Fin n) (ZMod 2)) *
        ((c⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
    rw [← hc, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have hmul : (c : Matrix (Fin n) (Fin n) (ZMod 2)) *
      ((c⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hmul' : ((c⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
      (c : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hleft : ∀ u : Fin n → ZMod 2,
      ((c⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
        ((c : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u) = u := by
    intro u
    rw [Matrix.mulVec_mulVec, hmul', Matrix.one_mulVec]
  have hright : ∀ u : Fin n → ZMod 2,
      (c : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
        (((c⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u) = u := by
    intro u
    rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
  simp only [fixCount]
  refine Finset.card_bij (fun u _ => (c : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u) ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    calc (y : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
          ((c : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u)
        = ((c : Matrix (Fin n) (Fin n) (ZMod 2)) *
            (x : Matrix (Fin n) (Fin n) (ZMod 2)) *
            ((c⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) *ᵥ
              ((c : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u) := by rw [hcM]
      _ = (c : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
            ((x : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
              (((c⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
                ((c : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u))) := by
            rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = (c : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
            ((x : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u) := by rw [hleft]
      _ = (c : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u := by rw [hu]
  · intro u1 _ u2 _ huu
    have h' := congrArg (fun w =>
      ((c⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w) huu
    simpa only [hleft] using h'
  · intro v hv
    refine ⟨((c⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      rw [hcM] at hv
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hv
      have h' := congrArg (fun w =>
        ((c⁻¹ : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w) hv
      simpa only [hleft] using h'
    · exact hright v

private lemma wt_le_three (v : Fin 3 → ZMod 3) : wt v ≤ 3 := by
  simpa [wt] using
    Finset.card_filter_le (Finset.univ : Finset (Fin 3)) (fun i => v i ≠ 0)

private theorem fixCount_vecElt6 :
    ∀ v : Fin 3 → ZMod 3,
      fixCount 6 ((vecElt W6.T v : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        2 ^ (6 - 2 * wt v) := by
  intro v
  by_cases hv : v = 0
  · subst hv
    rw [W6.vecElt_zero_T, Matrix.SpecialLinearGroup.coe_one, SLClassesK.wt_zero]
    simp [fixCount]
  · have hk : ∀ k, k < 4 → 1 ≤ k → fixCount 6 ((vecElt W6.T (SLClassesK.repV k) :
        SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 2 ^ (6 - 2 * k) := by
      decide +kernel
    rw [card_fix_conj (SLClassesK.conjRep6 v hv)]
    exact hk (wt v) (by have := wt_le_three v; omega) (SLClassesK.one_le_wt hv)

private def rep6 (k : ℕ) : SL(6, ZMod 2) :=
  if k = 1 then W6.r1 else if k = 2 then W6.r2 else W6.r3

private theorem conjRep6 (v : Fin 3 → ZMod 3) (hv : v ≠ 0) :
    IsConj (vecElt W6.T v) (rep6 (wt v)) := by
  have h := SLClassesK.conjRep6 v hv
  rwa [SLClassesK.vecElt_repV] at h

theorem conj_iff_SL6 : ∀ v w : Fin 3 → ZMod 3, v ≠ 0 → w ≠ 0 →
    (IsConj (vecElt W6.T v) (vecElt W6.T w) ↔ wt v = wt w) := by
  intro v w hv hw
  constructor
  · intro hconj
    have hfix := card_fix_conj hconj
    rw [fixCount_vecElt6 v, fixCount_vecElt6 w] at hfix
    have hwt := Nat.pow_right_injective (le_refl 2) hfix
    have hv3 := wt_le_three v
    have hw3 := wt_le_three w
    omega
  · intro hwt
    have hx := conjRep6 v hv
    have hy := conjRep6 w hw
    rw [hwt] at hx
    exact hx.trans hy.symm

private def gfun (a b c : Fin 3) : Fin 3 → Fin 3 := ![a, b, c]

private lemma gfun_perm (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    gfun (σ 0) (σ 1) (σ 2) i = σ i := by
  fin_cases i <;> rfl

private lemma injective_gfun_perm (σ : Equiv.Perm (Fin 3)) :
    Function.Injective (gfun (σ 0) (σ 1) (σ 2)) := by
  intro i j h
  apply σ.injective
  rw [← gfun_perm σ i, ← gfun_perm σ j]
  exact h

private def actFun6 (f : Fin 3 → Fin 3) (j : Fin 6) : Fin 6 :=
  Fin.ofNat 6 (2 * (f (Fin.ofNat 3 (j.val / 2))).val + j.val % 2)

private def P6f (f : Fin 3 → Fin 3) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun i j => if i = actFun6 f j then 1 else 0

private def bVec6 : Fin 3 → SL(6, ZMod 2) := ![W6.s1, W6.s2, W6.s3]

private def monoH6 (a b c : Fin 3) (ε : Fin 3 → ZMod 3) : SL(6, ZMod 2) :=
  (if ε 0 = 2 then bVec6 a else 1) * (if ε 1 = 2 then bVec6 b else 1) *
    (if ε 2 = 2 then bVec6 c else 1)

private def hM6 (a b c : Fin 3) (ε : Fin 3 → ZMod 3) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ((monoH6 a b c ε : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) * P6f (gfun a b c)

private def hMinv6 (a b c : Fin 3) (ε : Fin 3 → ZMod 3) :
    Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  (P6f (gfun a b c))ᵀ *
    ((monoH6 a b c ε : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))

private theorem hM6_mul_hMinv6 :
    ∀ a b c : Fin 3, Function.Injective (gfun a b c) → ∀ ε : Fin 3 → ZMod 3,
      hM6 a b c ε * hMinv6 a b c ε = 1 := by
  intro a b c hinj ε
  have hM : monoH6 a b c ε * monoH6 a b c ε = 1 :=
    SLClassesK.monoX_sq SLClassesK.sv6_sq SLClassesK.sv6_comm a b c ε
  have hP : P6f (gfun a b c) = SLClassesK.pK6 ![a, b, c] := rfl
  unfold hM6 hMinv6
  rw [hP, mul_assoc, ← mul_assoc (SLClassesK.pK6 _), SLClassesK.pK6_mul_transpose a b c hinj,
    one_mul, ← Matrix.SpecialLinearGroup.coe_mul, hM, Matrix.SpecialLinearGroup.coe_one]

private theorem mono_table6 :
    ∀ (a b c : Fin 3) (ε : Fin 3 → ZMod 3), Function.Injective (gfun a b c) →
      (∀ i, ε i ≠ 0) → ∀ i : Fin 3,
        hM6 a b c ε * ![W6.t1M, W6.t2M, W6.t3M] i =
          (![W6.t1M, W6.t2M, W6.t3M] (gfun a b c i)) ^ (ε i).val * hM6 a b c ε := by
  intro a b c ε hinj hε i
  have hg : gfun a b c = ![a, b, c] := rfl
  unfold hM6
  rw [hg] at hinj ⊢
  have hP : P6f ![a, b, c] = SLClassesK.pK6 ![a, b, c] := rfl
  have hS : monoH6 a b c ε * W6.T (![a, b, c] i) =
      W6.T (![a, b, c] i) ^ (ε i).val * monoH6 a b c ε :=
    SLClassesK.mono_semiconj SLClassesK.sv6_sq SLClassesK.sv6_conj a b c hinj ε hε i
  have hSM : (monoH6 a b c ε : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
      ![W6.t1M, W6.t2M, W6.t3M] (![a, b, c] i) =
      ![W6.t1M, W6.t2M, W6.t3M] (![a, b, c] i) ^ (ε i).val *
        (monoH6 a b c ε : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
    rw [← W6.coe_T, ← Matrix.SpecialLinearGroup.coe_pow, ← Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, hS]
  rw [hP, mul_assoc, SLClassesK.pK6_mul_T a b c hinj i, ← mul_assoc, hSM, mul_assoc]

theorem mono_SL6 : ∀ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) →
    ∃ h : SL(6, ZMod 2), ∀ i, h * W6.T i * h⁻¹ = W6.T (σ i) ^ (ε i).val := by
  intro σ ε hε
  refine ⟨W6.mkSL6 (hM6 (σ 0) (σ 1) (σ 2) ε) (hMinv6 (σ 0) (σ 1) (σ 2) ε)
    (hM6_mul_hMinv6 (σ 0) (σ 1) (σ 2) (injective_gfun_perm σ) ε), ?_⟩
  intro i
  apply conj_eq_of_mul_eq
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow, W6.coe_T]
  rw [← gfun_perm σ i]
  exact mono_table6 (σ 0) (σ 1) (σ 2) ε (injective_gfun_perm σ) hε i

private theorem fixCount_vecElt7 :
    ∀ v : Fin 3 → ZMod 3,
      fixCount 7 ((vecElt W7.T v : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) =
        2 ^ (7 - 2 * wt v) := by
  intro v
  by_cases hv : v = 0
  · subst hv
    rw [W7.vecElt_zero_T, Matrix.SpecialLinearGroup.coe_one, SLClassesK.wt_zero]
    simp [fixCount]
  · have hk : ∀ k, k < 4 → 1 ≤ k → fixCount 7 ((vecElt W7.T (SLClassesK.repV k) :
        SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) = 2 ^ (7 - 2 * k) := by
      decide +kernel
    rw [card_fix_conj (SLClassesK.conjRep7 v hv)]
    exact hk (wt v) (by have := wt_le_three v; omega) (SLClassesK.one_le_wt hv)

private def rep7 (k : ℕ) : SL(7, ZMod 2) :=
  if k = 1 then W7.r1 else if k = 2 then W7.r2 else W7.r3

private theorem conjRep7 (v : Fin 3 → ZMod 3) (hv : v ≠ 0) :
    IsConj (vecElt W7.T v) (rep7 (wt v)) := by
  have h := SLClassesK.conjRep7 v hv
  rwa [SLClassesK.vecElt_repV] at h

theorem conj_iff_SL7 : ∀ v w : Fin 3 → ZMod 3, v ≠ 0 → w ≠ 0 →
    (IsConj (vecElt W7.T v) (vecElt W7.T w) ↔ wt v = wt w) := by
  intro v w hv hw
  constructor
  · intro hconj
    have hfix := card_fix_conj hconj
    rw [fixCount_vecElt7 v, fixCount_vecElt7 w] at hfix
    have hwt := Nat.pow_right_injective (le_refl 2) hfix
    have hv3 := wt_le_three v
    have hw3 := wt_le_three w
    omega
  · intro hwt
    have hx := conjRep7 v hv
    have hy := conjRep7 w hw
    rw [hwt] at hx
    exact hx.trans hy.symm

private def actFun7 (f : Fin 3 → Fin 3) (j : Fin 7) : Fin 7 :=
  if j.val = 6 then 6
  else Fin.ofNat 7 (2 * (f (Fin.ofNat 3 (j.val / 2))).val + j.val % 2)

private def P7f (f : Fin 3 → Fin 3) : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  Matrix.of fun i j => if i = actFun7 f j then 1 else 0

private def bVec7 : Fin 3 → SL(7, ZMod 2) := ![W7.s1, W7.s2, W7.s3]

private def monoH7 (a b c : Fin 3) (ε : Fin 3 → ZMod 3) : SL(7, ZMod 2) :=
  (if ε 0 = 2 then bVec7 a else 1) * (if ε 1 = 2 then bVec7 b else 1) *
    (if ε 2 = 2 then bVec7 c else 1)

private def hM7 (a b c : Fin 3) (ε : Fin 3 → ZMod 3) : Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  ((monoH7 a b c ε : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2)) * P7f (gfun a b c)

private def hMinv7 (a b c : Fin 3) (ε : Fin 3 → ZMod 3) :
    Matrix (Fin 7) (Fin 7) (ZMod 2) :=
  (P7f (gfun a b c))ᵀ *
    ((monoH7 a b c ε : SL(7, ZMod 2)) : Matrix (Fin 7) (Fin 7) (ZMod 2))

private theorem hM7_mul_hMinv7 :
    ∀ a b c : Fin 3, Function.Injective (gfun a b c) → ∀ ε : Fin 3 → ZMod 3,
      hM7 a b c ε * hMinv7 a b c ε = 1 := by
  intro a b c hinj ε
  have hM : monoH7 a b c ε * monoH7 a b c ε = 1 :=
    SLClassesK.monoX_sq SLClassesK.sv7_sq SLClassesK.sv7_comm a b c ε
  have hP : P7f (gfun a b c) = SLClassesK.pK7 ![a, b, c] := rfl
  unfold hM7 hMinv7
  rw [hP, mul_assoc, ← mul_assoc (SLClassesK.pK7 _), SLClassesK.pK7_mul_transpose a b c hinj,
    one_mul, ← Matrix.SpecialLinearGroup.coe_mul, hM, Matrix.SpecialLinearGroup.coe_one]

private theorem mono_table7 :
    ∀ (a b c : Fin 3) (ε : Fin 3 → ZMod 3), Function.Injective (gfun a b c) →
      (∀ i, ε i ≠ 0) → ∀ i : Fin 3,
        hM7 a b c ε * ![W7.t1M, W7.t2M, W7.t3M] i =
          (![W7.t1M, W7.t2M, W7.t3M] (gfun a b c i)) ^ (ε i).val * hM7 a b c ε := by
  intro a b c ε hinj hε i
  have hg : gfun a b c = ![a, b, c] := rfl
  unfold hM7
  rw [hg] at hinj ⊢
  have hP : P7f ![a, b, c] = SLClassesK.pK7 ![a, b, c] := rfl
  have hS : monoH7 a b c ε * W7.T (![a, b, c] i) =
      W7.T (![a, b, c] i) ^ (ε i).val * monoH7 a b c ε :=
    SLClassesK.mono_semiconj SLClassesK.sv7_sq SLClassesK.sv7_conj a b c hinj ε hε i
  have hSM : (monoH7 a b c ε : Matrix (Fin 7) (Fin 7) (ZMod 2)) *
      ![W7.t1M, W7.t2M, W7.t3M] (![a, b, c] i) =
      ![W7.t1M, W7.t2M, W7.t3M] (![a, b, c] i) ^ (ε i).val *
        (monoH7 a b c ε : Matrix (Fin 7) (Fin 7) (ZMod 2)) := by
    rw [← W7.coe_T, ← Matrix.SpecialLinearGroup.coe_pow, ← Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, hS]
  rw [hP, mul_assoc, SLClassesK.pK7_mul_T a b c hinj i, ← mul_assoc, hSM, mul_assoc]

theorem mono_SL7 : ∀ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) →
    ∃ h : SL(7, ZMod 2), ∀ i, h * W7.T i * h⁻¹ = W7.T (σ i) ^ (ε i).val := by
  intro σ ε hε
  refine ⟨W7.mkSL7 (hM7 (σ 0) (σ 1) (σ 2) ε) (hMinv7 (σ 0) (σ 1) (σ 2) ε)
    (hM7_mul_hMinv7 (σ 0) (σ 1) (σ 2) (injective_gfun_perm σ) ε), ?_⟩
  intro i
  apply conj_eq_of_mul_eq
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow, W7.coe_T]
  rw [← gfun_perm σ i]
  exact mono_table7 (σ 0) (σ 1) (σ 2) ε (injective_gfun_perm σ) hε i

end CFSG.StandardType.GGFF

end
