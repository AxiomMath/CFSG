module

public import CFSG.Quasithin.Vol2.KGFactC31KG443Sec

public section

namespace CFSG.Quasithin.KGC31.NoM22

open Function CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Quasithin.KGC31.KG443

theorem pow_card_eq_zero_of_isNilpotent {F : Type*} [Field F] {n : Type*} [Fintype n]
    [DecidableEq n] {N : Matrix n n F} (h : IsNilpotent N) : N ^ Fintype.card n = 0 := by
  have h1 : N.charpoly = Polynomial.X ^ Fintype.card n :=
    sub_eq_zero.mp (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h).eq_zero
  have h2 := Matrix.aeval_self_charpoly N
  rw [h1] at h2
  simpa using h2

theorem pow_four_eq_one_of_two_pow {F : Type*} [Field F] [CharP F 2] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (hι : Fintype.card ι ≤ 4) {U : Matrix ι ι F} {k : ℕ} (hU : U ^ 2 ^ k = 1) :
    U ^ 4 = 1 := by
  rcases isEmpty_or_nonempty ι with hι0 | hι0
  · exact Subsingleton.elim _ _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (U - 1) ^ 2 ^ k = 0 := by
    rw [sub_pow_char_pow_of_commute 2 k (Commute.one_right U), hU, one_pow, sub_self]
  have h2 : (U - 1) ^ Fintype.card ι = 0 := pow_card_eq_zero_of_isNilpotent ⟨_, h1⟩
  have h4 : (U - 1) ^ 4 = 0 := by
    rw [show 4 = Fintype.card ι + (4 - Fintype.card ι) by omega, pow_add, h2, zero_mul]
  have h5 : U ^ 4 = ((U - 1) + 1) ^ 2 ^ 2 := by rw [sub_add_cancel]; norm_num
  rw [h5, add_pow_char_pow_of_commute 2 2 (Commute.one_right _), one_pow,
    show (2 : ℕ) ^ 2 = 4 by norm_num, h4, zero_add]

theorem gl_pow_four_eq_one {F : Type*} [Field F] [CharP F 2] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (hι : Fintype.card ι ≤ 4) {g : GL ι F} {k : ℕ} (hg : g ^ 2 ^ k = 1) :
    g ^ 4 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  refine pow_four_eq_one_of_two_pow hι (k := k) ?_
  rw [← Units.val_pow_eq_pow_val, hg, Units.val_one]

@[expose] def o8W : List ℤ := [2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1]

theorem o8_pow : (M22.elt o8W) ^ 8 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  refine perm_eq_of_rep ((M22.rep_elt o8W).powT M22.hn22 8) (Rep.idT M22.hn22) ?_
  decide +kernel

theorem o8_pow_four_ne : (M22.elt o8W) ^ 4 ≠ 1 := fun h => by
  have h1 : (((M22.elt o8W) ^ 4 : M22.G₀) : Equiv.Perm (Fin 22)) =
      ((1 : M22.G₀) : Equiv.Perm (Fin 22)) := congrArg Subtype.val h
  rw [Subgroup.coe_pow] at h1
  refine perm_ne_of_rep ((M22.rep_elt o8W).powT M22.hn22 4) (Rep.idT M22.hn22) ⟨1, by norm_num⟩
    ?_ h1
  decide +kernel

theorem orderOf_o8 : orderOf (M22.elt o8W) = 8 := by
  have hd : orderOf (M22.elt o8W) ∣ 2 ^ 3 := orderOf_dvd_of_pow_eq_one (by simpa using o8_pow)
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have h4 : ¬ orderOf (M22.elt o8W) ∣ 4 := fun h => o8_pow_four_ne (orderOf_dvd_iff_pow_eq_one.mp h)
  interval_cases i
  · exact absurd (hi'.symm ▸ (by norm_num : (2 : ℕ) ^ 0 ∣ 4)) h4
  · exact absurd (hi'.symm ▸ (by norm_num : (2 : ℕ) ^ 1 ∣ 4)) h4
  · exact absurd (hi'.symm ▸ (by norm_num : (2 : ℕ) ^ 2 ∣ 4)) h4
  · rw [hi']; norm_num

theorem not_secOnto_of_pow_four_of {A T : Type} [Group A] [Finite A] [Group T] {t : T}
    (ht : orderOf t = 8) (h : ∀ a : A, (∃ k : ℕ, a ^ 2 ^ k = 1) → a ^ 4 = 1) :
    ¬ SecOnto A T := by
  rintro ⟨Y, φ, hφ⟩
  obtain ⟨y, hy⟩ := hφ t
  have hn0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
  obtain ⟨e, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 2 (by norm_num)
  have h2 : ((y ^ m : ↥Y) : A) ^ 2 ^ e = 1 := by
    rw [← Subgroup.coe_pow, ← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one, Subgroup.coe_one]
  have h4 : (y ^ m) ^ 4 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact h _ ⟨e, h2⟩)
  have hφ4 : t ^ (m * 4) = 1 := by
    rw [pow_mul, ← hy, ← map_pow, ← map_pow, h4, map_one]
  have hd : 8 ∣ m * 4 := ht ▸ orderOf_dvd_of_pow_eq_one hφ4
  have hodd : Odd m := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hm)
  obtain ⟨j, rfl⟩ := hodd
  omega

theorem not_secOnto_of_pow_four {A : Type} [Group A] [Finite A]
    (h : ∀ a : A, (∃ k : ℕ, a ^ 2 ^ k = 1) → a ^ 4 = 1) :
    ¬ SecOnto A (NativeSporadic.Carrier .M22) :=
  not_secOnto_of_pow_four_of (T := NativeSporadic.Carrier .M22) (t := M22.elt o8W) orderOf_o8 h

theorem SecOnto.of_quot {A T : Type} [Group A] [Group T] {N : Subgroup A} [N.Normal]
    (h : SecOnto (A ⧸ N) T) : SecOnto A T := by
  obtain ⟨Y, φ, hφ⟩ := h
  let ρ : ↥(Y.comap (QuotientGroup.mk' N)) →* ↥Y :=
    ((QuotientGroup.mk' N).comp (Y.comap (QuotientGroup.mk' N)).subtype).codRestrict Y
      fun y => y.2
  refine ⟨Y.comap (QuotientGroup.mk' N), φ.comp ρ, hφ.comp fun y => ?_⟩
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective N (y : A ⧸ N)
  exact ⟨⟨a, show QuotientGroup.mk' N a ∈ Y from ha ▸ y.2⟩, Subtype.ext ha⟩

theorem not_secOnto_glSub {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type} [Fintype ι]
    [DecidableEq ι] (hι : Fintype.card ι ≤ 4) (H : Subgroup (GL ι K)) :
    ¬ SecOnto ↥H (NativeSporadic.Carrier .M22) := by
  refine not_secOnto_of_pow_four fun a ⟨k, hk⟩ => Subtype.ext ?_
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  refine gl_pow_four_eq_one hι (k := k) ?_
  rw [← Subgroup.coe_pow, hk, Subgroup.coe_one]

theorem not_secOnto_quot {K : Type} [Field K] [Finite K] [CharP K 2] {ι : Type} [Fintype ι]
    [DecidableEq ι] (hι : Fintype.card ι ≤ 4) (H : Subgroup (GL ι K)) (N : Subgroup ↥H) [N.Normal] :
    ¬ SecOnto (↥H ⧸ N) (NativeSporadic.Carrier .M22) := fun h =>
  not_secOnto_glSub hι H (SecOnto.of_quot h)

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) : CharP K 2 := by
  refine (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr ?_
  have : Fintype K := Fintype.ofFinite K
  have h0 : ((2 ^ f : ℕ) : K) = 0 := by
    rw [← hK, Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero K
  rw [Nat.cast_pow] at h0
  exact pow_eq_zero_iff (by omega) |>.mp h0

end CFSG.Quasithin.KGC31.NoM22

end
