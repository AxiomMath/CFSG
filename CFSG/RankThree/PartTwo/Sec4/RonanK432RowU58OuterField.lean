module

public import CFSG.RankThree.PartTwo.KFacts.KS21AutThreeU58

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.RankThree.PartTwo.KFacts.KS21.U58
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem exists_frob_gen : ∃ σ : K ≃+* K, (∀ a : K, σ a = a ^ 2) ∧ orderOf σ = 6 ∧
    Subgroup.zpowers σ = ⊤ := by
  obtain ⟨σ, hσ, hord, hzp, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality (F := K) Nat.prime_two (n := 6)
      (by norm_num) (by rw [card_K]; norm_num)
  exact ⟨σ, fun a => hσ a, hord, hzp⟩

theorem frob_pow_apply {σ : K ≃+* K} (hσ : ∀ a : K, σ a = a ^ 2) (r : ℕ) (a : K) :
    (σ ^ r) a = a ^ 2 ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ']
    change σ ((σ ^ r) a) = a ^ 2 ^ (r + 1)
    rw [ih, hσ, ← pow_mul, pow_succ]

theorem eq_one_of_pow_three_of_zeta {φ : K ≃+* K} (h3 : φ ^ 3 = 1)
    (hz : φ (ζ9 : K) = (ζ9 : K) ∨ φ (ζ9 : K) = (ζ9 : K)⁻¹) : φ = 1 := by
  obtain ⟨σ, hσ, hord, hzp⟩ := exists_frob_gen
  haveI : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [card_ringAut_K]; norm_num)
  have hφmem : φ ∈ Submonoid.powers σ := by
    rw [mem_powers_iff_mem_zpowers, hzp]
    exact Subgroup.mem_top φ
  obtain ⟨n, hn⟩ := hφmem
  have hn' : σ ^ n = φ := hn
  have hprim : IsPrimitiveRoot (ζ9 : K) 9 := by
    rw [IsPrimitiveRoot.coe_units_iff, ← orderOf_ζ9]
    exact IsPrimitiveRoot.orderOf ζ9
  have hz9 : (ζ9 : K) ^ 9 = 1 := hprim.pow_eq_one
  have hz8 : (ζ9 : K)⁻¹ = (ζ9 : K) ^ 8 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hz9)
  have h6 : σ ^ (3 * n) = 1 := by rw [pow_mul', hn', h3]
  have hdvd : 6 ∣ 3 * n := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one h6
  have hφ : σ ^ (n % 6) = φ := by
    rw [← hord, pow_mod_orderOf, hn']
  have hn6 : n % 6 = 0 ∨ n % 6 = 2 ∨ n % 6 = 4 := by omega
  rcases hn6 with h0 | h2 | h4
  · rw [h0, pow_zero] at hφ
    exact hφ.symm
  · exfalso
    rw [h2] at hφ
    have hφz : φ (ζ9 : K) = (ζ9 : K) ^ 4 := by
      rw [← hφ, frob_pow_apply hσ]
      norm_num
    rcases hz with hz | hz
    · rw [hφz] at hz
      have h41 := hprim.pow_inj (i := 4) (j := 1) (by norm_num) (by norm_num)
        (by rw [pow_one]; exact hz)
      omega
    · rw [hφz, hz8] at hz
      have h48 := hprim.pow_inj (i := 4) (j := 8) (by norm_num) (by norm_num) hz
      omega
  · exfalso
    rw [h4] at hφ
    have hφz : φ (ζ9 : K) = (ζ9 : K) ^ 7 := by
      rw [← hφ, frob_pow_apply hσ]
      rw [show (2 : ℕ) ^ 4 = 7 + 9 from rfl, pow_add, hz9, mul_one]
    rcases hz with hz | hz
    · rw [hφz] at hz
      have h71 := hprim.pow_inj (i := 7) (j := 1) (by norm_num) (by norm_num)
        (by rw [pow_one]; exact hz)
      omega
    · rw [hφz, hz8] at hz
      have h78 := hprim.pow_inj (i := 7) (j := 8) (by norm_num) (by norm_num) hz
      omega

end CFSG.RankThree.PartTwo.Sec4.RonanK432
