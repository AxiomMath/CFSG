module

public import CFSG.RankThree.PartTwo.Sec15.Item15Statements
import CFSG.RankThree.PartTwo.Sec13.Item13GL
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1511Point

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec15

private def q1 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

private def q2 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

private def q3 : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 1 2

private def qS : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 0 2

private lemma q1_mul_q1 : q1 * q1 = 1 := by decide

private lemma q3_eq : q3 = q1 * q2 := by decide

private lemma q1_comm_q2 : q1 * q2 = q2 * q1 := by decide

private lemma qS_pow_three : qS ^ 3 = 1 := by decide

private lemma qS_conj_q1 : qS * q1 * qS⁻¹ = q2 := by decide

private lemma qS_conj_q2 : qS * q2 * qS⁻¹ = q3 := by decide

private lemma qS_conj_q3 : qS * q3 * qS⁻¹ = q1 := by decide

private lemma q1_ne_one : q1 ≠ 1 := by decide

private def fixedSub {A : Type*} [Group A] (t : MulAut A) : Subgroup A where
  carrier := {a | t a = a}
  mul_mem' := by
    intro a b ha hb
    show t (a * b) = a * b
    rw [map_mul, ha, hb]
  one_mem' := by
    show t 1 = 1
    rw [map_one]
  inv_mem' := by
    intro a ha
    show t a⁻¹ = a⁻¹
    rw [map_inv, ha]

private def invertedSub {A : Type*} [Group A] (hcomm : ∀ a b : A, a * b = b * a)
    (t : MulAut A) : Subgroup A where
  carrier := {a | t a = a⁻¹}
  mul_mem' := by
    intro a b ha hb
    show t (a * b) = (a * b)⁻¹
    rw [map_mul, ha, hb, mul_inv_rev]
    exact hcomm a⁻¹ b⁻¹
  one_mem' := by
    show t 1 = 1⁻¹
    rw [map_one, inv_one]
  inv_mem' := by
    intro a ha
    show t a⁻¹ = (a⁻¹)⁻¹
    rw [map_inv, ha]

private theorem fixed_mul_inverted_decomp {A : Type*} [Group A]
    (hcomm : ∀ a b : A, a * b = b * a) (hexp : ∀ a : A, a ^ 3 = 1) {t : MulAut A}
    (ht : t * t = 1) (a : A) :
    (a * t a) ^ 2 ∈ fixedSub t ∧ (a * (t a)⁻¹) ^ 2 ∈ invertedSub hcomm t ∧
      a = (a * t a) ^ 2 * (a * (t a)⁻¹) ^ 2 := by
  have ht_apply : ∀ x : A, t (t x) = x := by
    intro x
    have h := congrArg (fun f : MulAut A => f x) ht
    simpa [MulAut.mul_apply, MulAut.one_apply] using h
  refine ⟨?_, ?_, ?_⟩
  · show t ((a * t a) ^ 2) = (a * t a) ^ 2
    rw [map_pow, map_mul, ht_apply, hcomm (t a) a]
  · show t ((a * (t a)⁻¹) ^ 2) = ((a * (t a)⁻¹) ^ 2)⁻¹
    rw [map_pow, map_mul, map_inv, ht_apply]
    rw [show t a * a⁻¹ = (a * (t a)⁻¹)⁻¹ from by rw [mul_inv_rev, inv_inv]]
    rw [inv_pow]
  · letI : CommGroup A := { ‹Group A› with mul_comm := hcomm }
    have h1 : (a * t a) ^ 2 * (a * (t a)⁻¹) ^ 2 = a ^ 4 := by
      rw [mul_pow, mul_pow, inv_pow]
      rw [show a ^ 2 * (t a) ^ 2 * (a ^ 2 * ((t a) ^ 2)⁻¹) =
          a ^ 2 * a ^ 2 * ((t a) ^ 2 * ((t a) ^ 2)⁻¹) by ac_rfl]
      rw [mul_inv_cancel, mul_one, ← pow_two (a ^ 2), ← pow_mul]
    rw [h1, show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hexp a, one_mul]

private theorem eq_one_of_eq_inv {A : Type*} [Group A] {c : A} (hc3 : c ^ 3 = 1)
    (h : c = c⁻¹) : c = 1 := by
  have h2 : c ^ 2 = 1 := by
    rw [pow_two]
    have h' : c⁻¹ * c = 1 := inv_mul_cancel c
    simpa [← h] using h'
  calc c = c * c ^ 2 := by rw [h2, mul_one]
    _ = c ^ 3 := by group
    _ = 1 := hc3

private theorem eq_one_of_eq_sq {A : Type*} [Group A] {c : A} (hc3 : c ^ 3 = 1)
    (h : c = c ^ 2) : c = 1 := by
  apply eq_one_of_eq_inv hc3
  conv_lhs => rw [h]
  calc c ^ 2 = c ^ 3 * c⁻¹ := by group
    _ = c⁻¹ := by rw [hc3, one_mul]

private theorem fixedSub_inf_invertedSub_eq_bot {A : Type*} [Group A]
    (hcomm : ∀ a b : A, a * b = b * a) (hexp : ∀ a : A, a ^ 3 = 1) (t : MulAut A) :
    fixedSub t ⊓ invertedSub hcomm t = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  have h1 : t a = a := ha.1
  have h2 : t a = a⁻¹ := ha.2
  exact eq_one_of_eq_inv (hexp a) (h1.symm.trans h2)

private theorem fixedSub_sup_invertedSub_eq_top {A : Type*} [Group A]
    (hcomm : ∀ a b : A, a * b = b * a) (hexp : ∀ a : A, a ^ 3 = 1) {t : MulAut A}
    (ht : t * t = 1) : fixedSub t ⊔ invertedSub hcomm t = ⊤ := by
  apply eq_top_iff.mpr
  intro a _
  have hx := (fixed_mul_inverted_decomp hcomm hexp ht a).1
  have hy := (fixed_mul_inverted_decomp hcomm hexp ht a).2.1
  have hde := (fixed_mul_inverted_decomp hcomm hexp ht a).2.2
  rw [hde]
  exact mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy)

private theorem card_fixedSub_mul_card_invertedSub {A : Type*} [Group A] [Finite A]
    (hcomm : ∀ a b : A, a * b = b * a) (hexp : ∀ a : A, a ^ 3 = 1)
    {t : MulAut A} (ht : t * t = 1) :
    Nat.card (fixedSub t) * Nat.card (invertedSub hcomm t) = Nat.card A := by
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (fixedSub t)
    (invertedSub hcomm t) (fun x _ y _ => hcomm x y)).1
  rw [fixedSub_sup_invertedSub_eq_top hcomm hexp ht,
    fixedSub_inf_invertedSub_eq_bot hcomm hexp t, Subgroup.card_top, Subgroup.card_bot] at hprod
  simpa using hprod.symm

private theorem card_eq_inf_mul_inf_of_invariant {A : Type*} [Group A] [Finite A]
    (hcomm : ∀ a b : A, a * b = b * a) (hexp : ∀ a : A, a ^ 3 = 1)
    {t : MulAut A} (ht : t * t = 1) {B : Subgroup A}
    (hB : ∀ a ∈ B, t a ∈ B) :
    Nat.card B = Nat.card ↥(B ⊓ fixedSub t) * Nat.card ↥(B ⊓ invertedSub hcomm t) := by
  have hsup : (B ⊓ fixedSub t) ⊔ (B ⊓ invertedSub hcomm t) = B := by
    apply le_antisymm
    · exact sup_le inf_le_left inf_le_left
    · intro a ha
      have hx := (fixed_mul_inverted_decomp hcomm hexp ht a).1
      have hy := (fixed_mul_inverted_decomp hcomm hexp ht a).2.1
      have hde := (fixed_mul_inverted_decomp hcomm hexp ht a).2.2
      have hxB : (a * t a) ^ 2 ∈ B := by
        have hta : t a ∈ B := hB a ha
        have h1 : a * t a ∈ B := B.mul_mem ha hta
        rw [pow_two]
        exact B.mul_mem h1 h1
      have hyB : (a * (t a)⁻¹) ^ 2 ∈ B := by
        have hta : (t a)⁻¹ ∈ B := B.inv_mem (hB a ha)
        have h1 : a * (t a)⁻¹ ∈ B := B.mul_mem ha hta
        rw [pow_two]
        exact B.mul_mem h1 h1
      rw [hde]
      exact mul_mem
        (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hxB, hx⟩))
        (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hyB, hy⟩))
  have hinf : (B ⊓ fixedSub t) ⊓ (B ⊓ invertedSub hcomm t) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have hc : a ∈ fixedSub t := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ha).1).2
    have hg : a ∈ invertedSub hcomm t := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp ha).2).2
    have hmem : a ∈ fixedSub t ⊓ invertedSub hcomm t := Subgroup.mem_inf.mpr ⟨hc, hg⟩
    rwa [fixedSub_inf_invertedSub_eq_bot hcomm hexp t] at hmem
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (B ⊓ fixedSub t)
    (B ⊓ invertedSub hcomm t) (fun x _ y _ => hcomm x y)).1
  rw [hsup, hinf, Subgroup.card_bot] at hprod
  simpa using hprod

private theorem map_mem_invertedSub {A : Type*} [Group A]
    (hcomm : ∀ a b : A, a * b = b * a) {S T T' : MulAut A}
    (hconj : S * T * S⁻¹ = T') {a : A} (ha : a ∈ invertedSub hcomm T) :
    S a ∈ invertedSub hcomm T' := by
  show T' (S a) = (S a)⁻¹
  calc T' (S a) = (S * T * S⁻¹) (S a) := by rw [hconj]
    _ = S (T (S⁻¹ (S a))) := by rw [MulAut.mul_apply, MulAut.mul_apply]
    _ = S (T a) := by rw [MulAut.inv_apply_self]
    _ = S (a⁻¹) := by rw [show T a = a⁻¹ from ha]
    _ = (S a)⁻¹ := by rw [map_inv]

private theorem card_invertedSub_le {A : Type*} [Group A] [Finite A]
    (hcomm : ∀ a b : A, a * b = b * a) {S T T' : MulAut A}
    (hconj : S * T * S⁻¹ = T') :
    Nat.card (invertedSub hcomm T) ≤ Nat.card (invertedSub hcomm T') :=
  Nat.card_le_card_of_injective
    (fun a : invertedSub hcomm T =>
      (⟨S a.1, map_mem_invertedSub hcomm hconj a.2⟩ : invertedSub hcomm T'))
    (fun a b h => Subtype.ext (S.injective (congrArg Subtype.val h)))

private theorem card_inf_invertedSub_le {A : Type*} [Group A] [Finite A]
    (hcomm : ∀ a b : A, a * b = b * a) {S T T' U U' : MulAut A}
    (hT : S * T * S⁻¹ = T') (hU : S * U * S⁻¹ = U') :
    Nat.card ↥(invertedSub hcomm T ⊓ invertedSub hcomm U) ≤
      Nat.card ↥(invertedSub hcomm T' ⊓ invertedSub hcomm U') := by
  refine Nat.card_le_card_of_injective
    (fun a : ↥(invertedSub hcomm T ⊓ invertedSub hcomm U) =>
      (⟨S a.1, ?_⟩ : ↥(invertedSub hcomm T' ⊓ invertedSub hcomm U')))
    (fun a b h => Subtype.ext (S.injective (congrArg Subtype.val h)))
  exact Subgroup.mem_inf.mpr
    ⟨map_mem_invertedSub hcomm hT (Subgroup.mem_inf.mp a.2).1,
     map_mem_invertedSub hcomm hU (Subgroup.mem_inf.mp a.2).2⟩

private theorem eq_one_of_invertedSub_eq_bot {A : Type*} [Group A]
    (hcomm : ∀ a b : A, a * b = b * a) (hexp : ∀ a : A, a ^ 3 = 1)
    {t : MulAut A} (ht : t * t = 1) (hbot : invertedSub hcomm t = ⊥) : t = 1 := by
  apply MulEquiv.ext
  intro a
  have hx := (fixed_mul_inverted_decomp hcomm hexp ht a).1
  have hy := (fixed_mul_inverted_decomp hcomm hexp ht a).2.1
  have hde := (fixed_mul_inverted_decomp hcomm hexp ht a).2.2
  have hy1 : (a * (t a)⁻¹) ^ 2 = 1 := by
    have hmem : (a * (t a)⁻¹) ^ 2 ∈ invertedSub hcomm t := hy
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have ha : a = (a * t a) ^ 2 := by
    conv_lhs => rw [hde]
    rw [hy1, mul_one]
  have hxfix : t ((a * t a) ^ 2) = (a * t a) ^ 2 := hx
  rw [← ha] at hxfix
  simpa using hxfix

private theorem conjugation_fixes_c {A : Type*} [Group A] {c : A}
    (hexp : ∀ a : A, a ^ 3 = 1) (hc1 : c ≠ 1)
    (ι : Equiv.Perm (Fin 4) →* MulAut A)
    (hfix : ∀ σ : Equiv.Perm (Fin 4), ι σ c ∈ Subgroup.zpowers c) :
    ι qS c = c ∧ ι q1 c = c ∧ ι q2 c = c ∧ ι q3 c = c := by
  let S : MulAut A := ι qS
  let T1 : MulAut A := ι q1
  let T2 : MulAut A := ι q2
  let T3 : MulAut A := ι q3
  have hS_pow : S ^ 3 = 1 := by
    show ι qS ^ 3 = 1
    rw [← map_pow, qS_pow_three, map_one]
  have hT1_sq : T1 * T1 = 1 := by
    show ι q1 * ι q1 = 1
    rw [← map_mul, q1_mul_q1, map_one]
  have hT3_eq : T3 = T1 * T2 := by
    show ι q3 = ι q1 * ι q2
    rw [q3_eq, map_mul]
  have hconj1 : S * T1 * S⁻¹ = T2 := by
    have h := congrArg ι qS_conj_q1
    simpa [S, T1, T2, map_mul, map_inv] using h
  have hconj2 : S * T2 * S⁻¹ = T3 := by
    have h := congrArg ι qS_conj_q2
    simpa [S, T2, T3, map_mul, map_inv] using h
  have hS_c_ne_one : S c ≠ 1 := fun h => hc1 (S.injective (by rw [h, map_one]))
  have hSc : S c = c := by
    rcases Sec13.eq_of_mem_zpowers_of_pow_three (hexp c) (hfix qS) with h | h | h
    · exact absurd h hS_c_ne_one
    · exact h
    · exfalso
      have hss : S (S c) = c := by
        rw [h, map_pow, h]
        rw [show (c ^ 2) ^ 2 = c ^ 4 by group]
        rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hexp c, one_mul]
      have hS3c : S (S (S c)) = c := by
        have h' := congrArg (fun f : MulAut A => f c) hS_pow
        simpa [pow_three, MulAut.mul_apply] using h'
      have hcon : S (S (S c)) = c ^ 2 := by rw [hss, h]
      rw [hcon] at hS3c
      exact hc1 (eq_one_of_eq_sq (hexp c) hS3c.symm)
  have hSinv_c : S⁻¹ c = c := by
    calc S⁻¹ c = S⁻¹ (S c) := by rw [hSc]
      _ = c := MulAut.inv_apply_self A S c
  have hS_fix : ∀ x : A, (x = c ∨ x = c ^ 2) → S x = x := by
    rintro x (rfl | rfl)
    · exact hSc
    · rw [map_pow, hSc]
  have hT1_c_ne_one : T1 c ≠ 1 := fun h => hc1 (T1.injective (by rw [h, map_one]))
  have hT1_c_cases : T1 c = c ∨ T1 c = c ^ 2 := by
    rcases Sec13.eq_of_mem_zpowers_of_pow_three (hexp c) (hfix q1) with h | h | h
    · exact absurd h hT1_c_ne_one
    · exact Or.inl h
    · exact Or.inr h
  have hT2_c_eq : T2 c = T1 c := by
    calc T2 c = (S * T1 * S⁻¹) c := by rw [hconj1]
      _ = S (T1 (S⁻¹ c)) := by rw [MulAut.mul_apply, MulAut.mul_apply]
      _ = S (T1 c) := by rw [hSinv_c]
      _ = T1 c := hS_fix (T1 c) hT1_c_cases
  have hT2_c_cases : T2 c = c ∨ T2 c = c ^ 2 := by
    rcases hT1_c_cases with h | h
    · exact Or.inl (hT2_c_eq.trans h)
    · exact Or.inr (hT2_c_eq.trans h)
  have hT3_c_eq : T3 c = T2 c := by
    calc T3 c = (S * T2 * S⁻¹) c := by rw [hconj2]
      _ = S (T2 (S⁻¹ c)) := by rw [MulAut.mul_apply, MulAut.mul_apply]
      _ = S (T2 c) := by rw [hSinv_c]
      _ = T2 c := hS_fix (T2 c) hT2_c_cases
  have hT1_T1_c : T1 (T1 c) = c := by
    have h := congrArg (fun f : MulAut A => f c) hT1_sq
    simpa [MulAut.mul_apply, MulAut.one_apply] using h
  have hT3_c : T3 c = c := by
    rw [hT3_eq, MulAut.mul_apply, hT2_c_eq, hT1_T1_c]
  have hT2_c : T2 c = c := hT3_c_eq.symm.trans hT3_c
  have hT1_c : T1 c = c := hT2_c_eq.symm.trans hT2_c
  exact ⟨hSc, hT1_c, hT2_c, hT3_c⟩

private theorem invertedSub_inf_eq_inf_fixedSub {A : Type*} [Group A]
    (hcomm : ∀ a b : A, a * b = b * a) {T1 T2 T3 : MulAut A}
    (hT3 : T3 = T1 * T2) :
    invertedSub hcomm T2 ⊓ invertedSub hcomm T3 = invertedSub hcomm T2 ⊓ fixedSub T1 := by
  apply le_antisymm
  · intro a ha
    rw [Subgroup.mem_inf] at ha ⊢
    refine ⟨ha.1, ?_⟩
    have hT3a : T3 a = a⁻¹ := ha.2
    have hT3expr : T3 a = (T1 a)⁻¹ := by
      rw [hT3, MulAut.mul_apply, show T2 a = a⁻¹ from ha.1, map_inv]
    have h1 : (T1 a)⁻¹ = a⁻¹ := hT3expr.symm.trans hT3a
    exact inv_inj.mp h1
  · intro a ha
    rw [Subgroup.mem_inf] at ha ⊢
    refine ⟨ha.1, ?_⟩
    have hT1a : T1 a = a := ha.2
    show T3 a = a⁻¹
    rw [hT3, MulAut.mul_apply, show T2 a = a⁻¹ from ha.1, map_inv, hT1a]

private theorem mapsTo_invertedSub_of_commute {A : Type*} [Group A]
    (hcomm : ∀ a b : A, a * b = b * a) {T1 T2 : MulAut A}
    (hT12 : T1 * T2 = T2 * T1) :
    ∀ a ∈ invertedSub hcomm T2, T1 a ∈ invertedSub hcomm T2 := by
  intro a ha
  show T2 (T1 a) = (T1 a)⁻¹
  calc T2 (T1 a) = (T2 * T1) a := by rw [MulAut.mul_apply]
    _ = (T1 * T2) a := by rw [← hT12]
    _ = T1 (T2 a) := by rw [MulAut.mul_apply]
    _ = T1 (a⁻¹) := by rw [show T2 a = a⁻¹ from ha]
    _ = (T1 a)⁻¹ := by rw [map_inv]

private theorem eq_three_of_sq_dvd_27 {x : ℕ} (hx : x ^ 2 ∣ 27) (hx1 : x ^ 2 ≠ 1) :
    x = 3 := by
  have hx2le : x ^ 2 ≤ 27 := Nat.le_of_dvd (by norm_num) hx
  have hxpos : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · rw [h] at hx
      exact absurd hx (by norm_num)
    · exact h
  have hx5 : x ≤ 5 := by
    by_contra hc
    have hx6 : 6 ≤ x := by omega
    have h1 : 6 * 6 ≤ x * x := Nat.mul_le_mul hx6 hx6
    have h2 : x ^ 2 ≤ 27 := hx2le
    rw [pow_two] at h2
    omega
  have hcases : x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by omega
  rcases hcases with h1 | h2 | h3 | h4 | h5
  · exfalso
    apply hx1
    rw [h1]
    norm_num
  · rw [h2] at hx
    exact absurd hx (by norm_num)
  · exact h3
  · rw [h4] at hx
    exact absurd hx (by norm_num)
  · rw [h5] at hx
    exact absurd hx (by norm_num)

private theorem counting_core {A : Type*} [Group A] [Finite A]
    (hcomm : ∀ a b : A, a * b = b * a) (hexp : ∀ a : A, a ^ 3 = 1)
    (hcard : Nat.card A = 27) {c : A} (hc1 : c ≠ 1) {S T1 T2 T3 : MulAut A}
    (hT1_sq : T1 * T1 = 1) (hT1_ne_one : T1 ≠ 1) (hT1T2_comm : T1 * T2 = T2 * T1)
    (hT3_eq : T3 = T1 * T2) (hconj1 : S * T1 * S⁻¹ = T2)
    (hconj2 : S * T2 * S⁻¹ = T3) (hconj3 : S * T3 * S⁻¹ = T1)
    (hT1_c : T1 c = c) (hT2_c : T2 c = c) : False := by
  let C1 : Subgroup A := fixedSub T1
  let B1 : Subgroup A := invertedSub hcomm T1
  let B2 : Subgroup A := invertedSub hcomm T2
  let B3 : Subgroup A := invertedSub hcomm T3
  have hC1B1_bot : C1 ⊓ B1 = ⊥ := fixedSub_inf_invertedSub_eq_bot hcomm hexp T1
  have hC1B1_prod : Nat.card C1 * Nat.card B1 = Nat.card A :=
    card_fixedSub_mul_card_invertedSub hcomm hexp hT1_sq
  have hB1_le_B2 : Nat.card B1 ≤ Nat.card B2 := card_invertedSub_le hcomm hconj1
  have hB2_le_B3 : Nat.card B2 ≤ Nat.card B3 := card_invertedSub_le hcomm hconj2
  have hB3_le_B1 : Nat.card B3 ≤ Nat.card B1 := card_invertedSub_le hcomm hconj3
  have hB1_eq_B2 : Nat.card B1 = Nat.card B2 :=
    le_antisymm hB1_le_B2 (hB2_le_B3.trans hB3_le_B1)
  let x : ℕ := Nat.card ↥(B1 ⊓ B2)
  have hB1B2_le_B2B3 : Nat.card ↥(B1 ⊓ B2) ≤ Nat.card ↥(B2 ⊓ B3) :=
    card_inf_invertedSub_le hcomm hconj1 hconj2
  have hB2B3_le_B3B1 : Nat.card ↥(B2 ⊓ B3) ≤ Nat.card ↥(B3 ⊓ B1) :=
    card_inf_invertedSub_le hcomm hconj2 hconj3
  have hB3B1_le_B1B2 : Nat.card ↥(B3 ⊓ B1) ≤ Nat.card ↥(B1 ⊓ B2) :=
    card_inf_invertedSub_le hcomm hconj3 hconj1
  have hB1B2_eq_B2B3 : Nat.card ↥(B1 ⊓ B2) = Nat.card ↥(B2 ⊓ B3) :=
    le_antisymm hB1B2_le_B2B3 (hB2B3_le_B3B1.trans hB3B1_le_B1B2)
  have hx23 : Nat.card ↥(B2 ⊓ B3) = x := hB1B2_eq_B2B3.symm
  have hT1_B2 : ∀ a ∈ B2, T1 a ∈ B2 := mapsTo_invertedSub_of_commute hcomm hT1T2_comm
  have hB2_card : Nat.card B2 = Nat.card ↥(B2 ⊓ C1) * Nat.card ↥(B2 ⊓ B1) :=
    card_eq_inf_mul_inf_of_invariant hcomm hexp hT1_sq hT1_B2
  have hB2B3_eq_B2C1 : B2 ⊓ B3 = B2 ⊓ C1 := invertedSub_inf_eq_inf_fixedSub hcomm hT3_eq
  have hB2_card_sq : Nat.card B2 = x ^ 2 := by
    have h1 : Nat.card ↥(B2 ⊓ C1) = x := by
      rw [← hB2B3_eq_B2C1]
      exact hx23
    have h2 : Nat.card ↥(B2 ⊓ B1) = x := by rw [inf_comm]
    rw [hB2_card, h1, h2, pow_two]
  have hB1_eq_x2 : Nat.card B1 = x ^ 2 := by rw [hB1_eq_B2, hB2_card_sq]
  have hx2_ne_one : x ^ 2 ≠ 1 := by
    rw [← hB1_eq_x2]
    intro h
    exact hT1_ne_one (eq_one_of_invertedSub_eq_bot hcomm hexp hT1_sq
      ((Subgroup.card_eq_one).mp h))
  have hx2_dvd : x ^ 2 ∣ 27 := by
    rw [← hB1_eq_x2]
    simpa [hcard] using Subgroup.card_subgroup_dvd_card B1
  have hx_eq_three : x = 3 := eq_three_of_sq_dvd_27 hx2_dvd hx2_ne_one
  have hB1_card : Nat.card B1 = 9 := by rw [hB1_eq_x2, hx_eq_three]; norm_num
  have hC1_card : Nat.card C1 = 3 := by
    have hprod : Nat.card C1 * Nat.card B1 = 27 := by simpa [hcard] using hC1B1_prod
    rw [hB1_card] at hprod
    omega
  have hc_mem_C1 : c ∈ C1 := hT1_c
  have hC1_eq_zpowers : C1 = Subgroup.zpowers c := by
    refine (Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers c) (K := C1) ?_ ?_).symm
    · rw [Subgroup.zpowers_le]
      exact hc_mem_C1
    · rw [hC1_card, Nat.card_zpowers, orderOf_eq_prime (hexp c) hc1]
  have hB2B3_eq_C1 : B2 ⊓ B3 = C1 := by
    refine Subgroup.eq_of_le_of_card_ge (H := B2 ⊓ B3) (K := C1) ?_ ?_
    · rw [hB2B3_eq_B2C1]
      exact inf_le_right
    · rw [hx23, hx_eq_three, hC1_card]
  have hc_mem_B2B3 : c ∈ B2 ⊓ B3 := by
    rw [hB2B3_eq_C1]
    exact hc_mem_C1
  have hT2_c_inv : T2 c = c⁻¹ := (Subgroup.mem_inf.mp hc_mem_B2B3).1
  exact hc1 (eq_one_of_eq_inv (hexp c) (hT2_c.symm.trans hT2_c_inv))

theorem false_of_perm_four_fixes {A : Type*} [Group A] [Finite A]
    (hcomm : ∀ a b : A, a * b = b * a) (hexp : ∀ a : A, a ^ 3 = 1) (hcard : Nat.card A = 27)
    {c : A} (hc1 : c ≠ 1) (ι : Equiv.Perm (Fin 4) →* MulAut A) (hι : Function.Injective ι)
    (hfix : ∀ σ : Equiv.Perm (Fin 4), ι σ c ∈ Subgroup.zpowers c) : False := by
  let S : MulAut A := ι qS
  let T1 : MulAut A := ι q1
  let T2 : MulAut A := ι q2
  let T3 : MulAut A := ι q3
  have hT1_sq : T1 * T1 = 1 := by
    show ι q1 * ι q1 = 1
    rw [← map_mul, q1_mul_q1, map_one]
  have hT1_ne_one : T1 ≠ 1 := fun h =>
    q1_ne_one (hι (by simpa [T1, map_one] using h))
  have hT1T2_comm : T1 * T2 = T2 * T1 := by
    show ι q1 * ι q2 = ι q2 * ι q1
    rw [← map_mul, ← map_mul, q1_comm_q2]
  have hT3_eq : T3 = T1 * T2 := by
    show ι q3 = ι q1 * ι q2
    rw [q3_eq, map_mul]
  have hconj1 : S * T1 * S⁻¹ = T2 := by
    have h := congrArg ι qS_conj_q1
    simpa [S, T1, T2, map_mul, map_inv] using h
  have hconj2 : S * T2 * S⁻¹ = T3 := by
    have h := congrArg ι qS_conj_q2
    simpa [S, T2, T3, map_mul, map_inv] using h
  have hconj3 : S * T3 * S⁻¹ = T1 := by
    have h := congrArg ι qS_conj_q3
    simpa [S, T3, T1, map_mul, map_inv] using h
  obtain ⟨-, hT1_c, hT2_c, -⟩ := conjugation_fixes_c hexp hc1 ι hfix
  exact counting_core hcomm hexp hcard hc1 hT1_sq hT1_ne_one hT1T2_comm hT3_eq
    hconj1 hconj2 hconj3 hT1_c hT2_c

private theorem mem_zpowers_subtype_of_mem_wStar {G : Type*} [Group G] {A : Subgroup G} {c : G}
    (hcA : c ∈ A)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (x : wStar A) :
    ((x : MulAut A) ⟨c, hcA⟩ : A) ∈ Subgroup.zpowers (⟨c, hcA⟩ : A) := by
  obtain ⟨w, hwN, -, hwx⟩ := Sec4.mem_autIn_iff.mp x.2
  have hw : w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := hW hwN
  have hmem : w * c * w⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp hw c).mp (Subgroup.mem_zpowers c)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_zpow]
  have hxapp : (((x : MulAut A) ⟨c, hcA⟩ : A) : G) = w * c * w⁻¹ := by
    rw [← hwx, Sec4.normalizerMonoidHom_apply_coe]
  rw [hxapp]
  exact hk

theorem not_wStarS4_of_le_normalizer {G : Type} [Group G] {A : Subgroup G} {c : G}
    (hA : Late.IsE27 A) (hcA : c ∈ A) (hc1 : c ≠ 1)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    ¬ WStarS4 A := by
  haveI : IsMulCommutative ↥A := hA.1.1
  haveI : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [hA.2]; norm_num)
  have hpow : ∀ a : ↥A, a ^ 3 = 1 := by
    intro a
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hA.1.2 a a.2
  have hc1' : (⟨c, hcA⟩ : ↥A) ≠ 1 := by
    intro h
    exact hc1 (congrArg Subtype.val h)
  intro hWS4
  rcases hWS4 with h | h
  · obtain ⟨φ⟩ := h
    let ι : Equiv.Perm (Fin 4) →* MulAut A := (wStar A).subtype.comp φ.symm.toMonoidHom
    have hι : Function.Injective ι := by
      intro σ τ h
      exact φ.symm.injective ((wStar A).subtype_injective h)
    have hfix : ∀ σ : Equiv.Perm (Fin 4), ι σ ⟨c, hcA⟩ ∈ Subgroup.zpowers ⟨c, hcA⟩ :=
      fun σ => mem_zpowers_subtype_of_mem_wStar hcA hW (φ.symm σ)
    exact false_of_perm_four_fixes (A := ↥A) (fun a b => mul_comm' a b)
      hpow hA.2 hc1' ι hι hfix
  · obtain ⟨φ⟩ := h
    let ψ : Equiv.Perm (Fin 4) →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4) :=
      MonoidHom.inr (Multiplicative (ZMod 2)) (Equiv.Perm (Fin 4))
    let ι : Equiv.Perm (Fin 4) →* MulAut A :=
      (wStar A).subtype.comp (φ.symm.toMonoidHom.comp ψ)
    have hψ : Function.Injective ψ := by
      intro σ τ h
      have h' := congrArg Prod.snd h
      simpa [ψ, MonoidHom.inr_apply] using h'
    have hι : Function.Injective ι := by
      intro σ τ h
      exact hψ (φ.symm.injective ((wStar A).subtype_injective h))
    have hfix : ∀ σ : Equiv.Perm (Fin 4), ι σ ⟨c, hcA⟩ ∈ Subgroup.zpowers ⟨c, hcA⟩ :=
      fun σ => mem_zpowers_subtype_of_mem_wStar hcA hW (φ.symm (ψ σ))
    exact false_of_perm_four_fixes (A := ↥A) (fun a b => mul_comm' a b)
      hpow hA.2 hc1' ι hι hfix

end CFSG.RankThree.PartTwo.Sec15.Proof1511Point
