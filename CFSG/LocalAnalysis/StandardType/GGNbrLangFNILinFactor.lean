module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.StandardType

private def fnilg_P {ι : Type*} {M : ι → Type*} [∀ i, Zero (M i)] (k : ι) (r : ∀ i, M i) : Prop :=
  ∀ i, i ≠ k → r i = 0

private lemma fnilg_P_single {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, Zero (M i)]
    (k : ι) (x : M k) : fnilg_P k (Pi.single k x) := by
  intro i hi
  exact Pi.single_eq_of_ne (M := M) hi x

private lemma fnilg_P_iff {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, Zero (M i)]
    (k : ι) (r : ∀ i, M i) : fnilg_P k r ↔ r = Pi.single k (r k) := by
  constructor
  · intro h
    funext i
    by_cases hi : i = k
    · subst hi; simp
    · rw [h i hi, Pi.single_eq_of_ne (M := M) hi]
  · intro h
    rw [h]
    exact fnilg_P_single k (r k)

private lemma fnilg_P_add {ι : Type*} {M : ι → Type*} [∀ i, AddZeroClass (M i)]
    {k : ι} {r q : ∀ i, M i} (hr : fnilg_P k r) (hq : fnilg_P k q) :
    fnilg_P k (r + q) := by
  intro i hi
  rw [Pi.add_apply, hr i hi, hq i hi, zero_add]

private lemma fnilg_P_mul {ι : Type*} {M : ι → Type*} [∀ i, MulZeroClass (M i)]
    {k : ι} {r q : ∀ i, M i} (hr : fnilg_P k r) (hq : fnilg_P k q) :
    fnilg_P k (r * q) := by
  intro i hi
  rw [Pi.mul_apply, hr i hi, hq i hi, zero_mul]

private lemma fnilg_P_zero {ι : Type*} {M : ι → Type*} [∀ i, Zero (M i)] (k : ι) :
    fnilg_P k (0 : ∀ i, M i) := by
  intro i _
  rfl

private lemma fnilg_mulSingle_sub_one {ι : Type*} [DecidableEq ι] {M : ι → Type*}
    [∀ i, Ring (M i)] (k : ι) (x : M k) :
    Pi.mulSingle k x - 1 = Pi.single k (x - 1) := by
  ext i
  by_cases h : i = k
  · subst h; simp
  · rw [Pi.single_eq_of_ne (M := M) h, Pi.sub_apply, Pi.mulSingle_eq_of_ne (M := M) h]
    simp

private lemma fnilg_P_single_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    {D : ι → Type*} [∀ i, Field (D i)] {d : ι → ℕ} (k : ι) (hd : 2 ≤ d k)
    (s : (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) ≃+*
         (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)))
    (hs : ∀ x : Matrix.SpecialLinearGroup (Fin (d k)) (D k),
      ∃ y : Matrix.SpecialLinearGroup (Fin (d k)) (D k),
        s (Pi.mulSingle k (x : Matrix (Fin (d k)) (Fin (d k)) (D k))) =
          Pi.mulSingle k (y : Matrix (Fin (d k)) (Fin (d k)) (D k))) :
    ∀ M : Matrix (Fin (d k)) (Fin (d k)) (D k), fnilg_P k (s (Pi.single k M)) := by
  have hoff : ∀ (i j : Fin (d k)), i ≠ j → ∀ a : D k,
      fnilg_P k (s (Pi.single k (Matrix.single i j a))) := by
    intro i j hij a
    obtain ⟨y, hy⟩ := hs ⟨Matrix.transvection i j a, by
      rw [Matrix.det_transvection_of_ne i j hij a]⟩
    have hsingle : (Pi.single k (Matrix.single i j a) :
          ∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) =
        (Pi.mulSingle k (Matrix.transvection i j a) :
          ∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) - 1 := by
      rw [fnilg_mulSingle_sub_one
        (M := fun i => Matrix (Fin (d i)) (Fin (d i)) (D i)) k (Matrix.transvection i j a)]
      congr 1
      simp [Matrix.transvection]
    have hmain : s (Pi.single k (Matrix.single i j a)) =
        Pi.single k ((y : Matrix (Fin (d k)) (Fin (d k)) (D k)) - 1) := by
      rw [hsingle, map_sub, hy, map_one,
        fnilg_mulSingle_sub_one
          (M := fun i => Matrix (Fin (d i)) (Fin (d i)) (D i)) k
          (y : Matrix (Fin (d k)) (Fin (d k)) (D k))]
    rw [hmain]
    exact fnilg_P_single (M := fun i => Matrix (Fin (d i)) (Fin (d i)) (D i)) k
      ((y : Matrix (Fin (d k)) (Fin (d k)) (D k)) - 1)
  intro M
  refine Matrix.induction_on'
    (P := fun M : Matrix (Fin (d k)) (Fin (d k)) (D k) => fnilg_P k (s (Pi.single k M)))
    M ?_ ?_ ?_
  · simpa using fnilg_P_zero (M := fun i => Matrix (Fin (d i)) (Fin (d i)) (D i)) k
  · intro p q hp hq
    rw [Pi.single_add, map_add]
    exact fnilg_P_add hp hq
  · intro i j a
    by_cases hij : i = j
    · subst hij
      obtain ⟨j', hj'⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin (d k))
        (by rw [Fintype.card_fin]; exact lt_of_lt_of_le (by decide) hd) i
      have hdiag : Matrix.single i i a =
          Matrix.single i j' a * Matrix.single j' i (1 : D k) := by
        rw [Matrix.single_mul_single_same, mul_one]
      rw [hdiag, Pi.single_mul, map_mul]
      exact fnilg_P_mul (hoff i j' (Ne.symm hj') a) (hoff j' i hj' 1)
    · exact hoff i j hij a

theorem fniLin_factor_fixed {ι : Type} [Fintype ι] [DecidableEq ι] {D : ι → Type} [∀ i, Field (D i)]
    {d : ι → ℕ}
    (s : (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) ≃+* (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)))
    (k : ι) (hd : 2 ≤ d k)
    (hs : ∀ x : Matrix.SpecialLinearGroup (Fin (d k)) (D k),
      ∃ y : Matrix.SpecialLinearGroup (Fin (d k)) (D k),
        s (Pi.mulSingle k (x : Matrix (Fin (d k)) (Fin (d k)) (D k))) =
          Pi.mulSingle k (y : Matrix (Fin (d k)) (Fin (d k)) (D k)))
    (hs' : ∀ x : Matrix.SpecialLinearGroup (Fin (d k)) (D k),
      ∃ y : Matrix.SpecialLinearGroup (Fin (d k)) (D k),
        s.symm (Pi.mulSingle k (x : Matrix (Fin (d k)) (Fin (d k)) (D k))) =
          Pi.mulSingle k (y : Matrix (Fin (d k)) (Fin (d k)) (D k))) :
    s (Pi.single k 1) = Pi.single k 1 := by
  have hQ : ∀ M : Matrix (Fin (d k)) (Fin (d k)) (D k), fnilg_P k (s (Pi.single k M)) :=
    fnilg_P_single_map k hd s hs
  have hQ' : ∀ M : Matrix (Fin (d k)) (Fin (d k)) (D k), fnilg_P k (s.symm (Pi.single k M)) :=
    fnilg_P_single_map k hd s.symm hs'
  have he : fnilg_P k (s (Pi.single k 1)) := hQ 1
  have he' : fnilg_P k (s.symm (Pi.single k 1)) := hQ' 1
  have h1 : Pi.single k (1 : Matrix (Fin (d k)) (Fin (d k)) (D k)) * s (Pi.single k 1) =
      s (Pi.single k 1) := by
    rw [← Pi.single_mul_left (i := k) (f := s (Pi.single k 1))
        (1 : Matrix (Fin (d k)) (Fin (d k)) (D k)), one_mul]
    exact ((fnilg_P_iff k (s (Pi.single k 1))).mp he).symm
  have h2 : s.symm (Pi.single k 1) * Pi.single k (1 : Matrix (Fin (d k)) (Fin (d k)) (D k)) =
      s.symm (Pi.single k 1) := by
    rw [← Pi.single_mul_right (i := k) (f := s.symm (Pi.single k 1))
        (1 : Matrix (Fin (d k)) (Fin (d k)) (D k)), mul_one]
    exact ((fnilg_P_iff k (s.symm (Pi.single k 1))).mp he').symm
  have h3 : Pi.single k (1 : Matrix (Fin (d k)) (Fin (d k)) (D k)) * s (Pi.single k 1) =
      Pi.single k (1 : Matrix (Fin (d k)) (Fin (d k)) (D k)) := by
    have h := congrArg s h2
    rw [map_mul, s.apply_symm_apply] at h
    exact h
  exact h1.symm.trans h3

end CFSG.StandardType
