module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Combinatorics.Matroid.Init

public section

namespace CFSG.Quasithin.Background.Harris.AutBorel

open Polynomial

theorem sigma_eq_one_of_fix_pow_nine {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ (2 * n)) (σ : K ≃+* K)
    (h : ∀ a : Kˣ, σ ((a : K) ^ 9) = (a : K) ^ 9) : σ = 1 ∨ n = 3 := by
  classical
  by_cases hσ : σ = 1
  · exact Or.inl hσ
  by_cases hn3 : n = 3
  · exact Or.inr hn3
  exfalso
  obtain ⟨F, hmemF⟩ : ∃ F : Subfield K, ∀ x : K, x ∈ F ↔ σ x = x :=
    ⟨σ.toRingHom.eqLocusField (RingHom.id K), fun x => by
      simp [RingHom.mem_eqLocusField]⟩
  have : Fintype K := Fintype.ofFinite K
  have hKcard : Fintype.card K = 2 ^ (2 * n) := by
    rw [← hK, Nat.card_eq_fintype_card]
  obtain ⟨x0, hx0⟩ : ∃ x : K, σ x ≠ x := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    exact hσ (RingEquiv.ext fun x => by simpa using hcon x)
  have hx0F : x0 ∉ F := fun hm => hx0 ((hmemF x0).1 hm)
  have hqlt : Nat.card F < Nat.card K := Finite.card_subtype_lt (p := fun y => y ∈ F) hx0F
  have hdim := Module.natCard_eq_pow_finrank (K := F) (V := K)
  have hkpos : 0 < Module.finrank F K := Module.finrank_pos
  rw [hK] at hdim
  have hqdvd : Nat.card F ∣ 2 ^ (2 * n) := by
    rw [hdim]; exact dvd_pow_self _ hkpos.ne'
  obtain ⟨d, hdle, hqd⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hqdvd
  have hdk : 2 * n = d * Module.finrank F K := by
    have h2 : (2:ℕ) ^ (2 * n) = 2 ^ (d * Module.finrank F K) := by
      rw [hdim, hqd, ← pow_mul]
    exact Nat.pow_right_injective (le_refl 2) h2
  have hk2 : 2 ≤ Module.finrank F K := by
    by_contra hlt
    have hk1 : Module.finrank F K = 1 := by omega
    rw [hk1, mul_one] at hdk
    have hd : Nat.card F = Nat.card K := by
      rw [hqd, hK, show d = 2 * n by omega]
    omega
  have hdn : d ≤ n := by
    have : d * 2 ≤ d * Module.finrank F K := Nat.mul_le_mul_left d hk2
    omega
  have hd1 : 1 ≤ d := by
    by_contra hd0
    have hd00 : d = 0 := by omega
    rw [hd00, zero_mul] at hdk
    omega
  have hferm : ∀ a : K, a ∈ F → a ≠ 0 → a ^ (Nat.card F - 1) = 1 := by
    intro a ha ha0
    have : Fintype F := Fintype.ofFinite F
    have h1 := FiniteField.pow_card_sub_one_eq_one (⟨a, ha⟩ : F)
      (fun h0 => ha0 (congrArg Subtype.val h0))
    rw [Nat.card_eq_fintype_card]
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hg : ∀ x : K, x ≠ 0 →
      x ^ Nat.gcd (9 * (Nat.card F - 1)) (2 ^ (2 * n) - 1) = 1 := by
    intro x hx
    rw [pow_gcd_eq_one]
    refine ⟨?_, ?_⟩
    · have hmem : x ^ 9 ∈ F := by
        rw [hmemF]
        have := h (Units.mk0 x hx)
        simpa using this
      rw [pow_mul]
      exact hferm _ hmem (pow_ne_zero _ hx)
    · have := FiniteField.pow_card_sub_one_eq_one x hx
      rw [hKcard] at this
      exact this
  have hcount : 2 ^ (2 * n) - 1 ≤ Nat.gcd (9 * (Nat.card F - 1)) (2 ^ (2 * n) - 1) := by
    have h22 : 2 ^ 2 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hgpos : 0 < Nat.gcd (9 * (Nat.card F - 1)) (2 ^ (2 * n) - 1) := by
      apply Nat.gcd_pos_of_pos_right
      norm_num at h22
      omega
    have hsub : (Finset.univ.erase (0 : K)) ⊆
        (nthRoots (Nat.gcd (9 * (Nat.card F - 1)) (2 ^ (2 * n) - 1)) (1 : K)).toFinset := by
      intro x hx
      rw [Finset.mem_erase] at hx
      rw [Multiset.mem_toFinset, mem_nthRoots hgpos]
      exact hg x hx.1
    have h1 := Finset.card_le_card hsub
    have h2 := (Multiset.toFinset_card_le
      (nthRoots (Nat.gcd (9 * (Nat.card F - 1)) (2 ^ (2 * n) - 1)) (1 : K))).trans
      (card_nthRoots _ _)
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hKcard] at h1
    omega
  have hq2 : 2 ≤ Nat.card F := by
    rw [hqd]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd1
  have hgle : Nat.gcd (9 * (Nat.card F - 1)) (2 ^ (2 * n) - 1) ≤ 9 * (Nat.card F - 1) :=
    Nat.gcd_le_left _ (by omega)
  rw [hqd] at hcount hgle
  rcases (show n = 2 ∨ 4 ≤ n by omega) with rfl | h4
  · interval_cases d <;> norm_num at hcount
  · have hX : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h4
    have hY : 2 ^ d ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hdn
    have hXX : 2 ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [two_mul, pow_add]
    have hY1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have h5 : 2 ^ (2 * n) ≤ 9 * 2 ^ d := by
      have h6 := le_trans hcount hgle
      have h7 : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
      omega
    rw [hXX] at h5
    norm_num at hX
    nlinarith [Nat.mul_le_mul_right (2 ^ n) hX]

end CFSG.Quasithin.Background.Harris.AutBorel

end
