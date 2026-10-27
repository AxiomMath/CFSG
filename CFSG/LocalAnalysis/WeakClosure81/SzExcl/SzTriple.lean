module

public import CFSG.GH74.Uniqueness.Bender.Models

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SzExcl

open Subgroup CFSG.GH74.Uniqueness.Bender

private theorem exists_szTriple_of_benderCore {S : Type} [Group S] [Finite S] {n : ℕ}
    {Q : Subgroup S} {t₀ : S} (hc : BenderCore (2 ^ n) 2 1 Q t₀)
    {s : S} (hs : s * s = 1) (hs1 : s ≠ 1) (hsQ : s ∈ Q) (hn : 2 < 2 ^ n) :
    ∃ c₂ c₃ : S, s * (c₂⁻¹ * s * c₂) = c₂⁻¹ * s * c₂ * s ∧ c₂⁻¹ * s * c₂ ≠ s ∧
      s * (c₃⁻¹ * s * c₃) ≠ c₃⁻¹ * s * c₃ * s ∧
      c₂⁻¹ * s * c₂ * (c₃⁻¹ * s * c₃) ≠ c₃⁻¹ * s * c₃ * (c₂⁻¹ * s * c₂) := by
  classical
  have hs2 : orderOf s = 2 := by
    apply orderOf_eq_prime _ hs1
    rwa [sq]
  have hsZ : s ∈ rootCenter Q := hc.mem_rootCenter_of_mul_self hsQ hs
  have hzex : ∃ z ∈ rootCenter Q, z ≠ 1 ∧ z ≠ s := by
    by_contra hcon
    have hsub : rootCenter Q ≤ Subgroup.zpowers s := by
      intro z hz
      by_contra hzsp
      have hz1 : z ≠ 1 := by
        rintro rfl
        exact hzsp (Subgroup.one_mem (Subgroup.zpowers s))
      have hzs : z ≠ s := by
        intro h
        apply hzsp
        rw [h]
        exact Subgroup.mem_zpowers s
      exact hcon ⟨z, hz, hz1, hzs⟩
    have hcard : Nat.card (rootCenter Q) ≤ Nat.card (Subgroup.zpowers s) :=
      Subgroup.card_le_of_le hsub
    rw [hc.card_center, Nat.card_zpowers, hs2] at hcard
    omega
  obtain ⟨z, hzZ, hz1, hzs⟩ := hzex
  have hz2 : z * z = 1 := hc.center_sq z hzZ
  have hsz : s * z = z * s := (mem_rootCenter_iff.mp hzZ).2 s hsQ
  have ht0_1 : t₀ ≠ 1 := by
    intro h1
    apply hc.not_mem
    rw [h1]
    exact (borel Q).one_mem
  obtain ⟨c₂, hc₂⟩ := isConj_iff.mp (hc.isConj_of_involutions hs hs1 hz2 hz1)
  obtain ⟨c₃, hc₃⟩ := isConj_iff.mp (hc.isConj_of_involutions hs hs1 hc.sq_eq_one ht0_1)
  refine ⟨c₂⁻¹, c₃⁻¹, ?_, ?_, ?_, ?_⟩
  · simpa only [inv_inv, hc₂] using hsz
  · simpa only [inv_inv, hc₂] using hzs
  · rw [inv_inv, hc₃]
    intro hst
    have hmem : t₀ ∈ Q := by
      rw [← hc.centralizer_eq_of_e_one hsZ hs1]
      exact Subgroup.mem_centralizer_iff.mpr (by simpa using hst)
    exact hc.not_mem (le_borel Q hmem)
  · rw [inv_inv, inv_inv, hc₂, hc₃]
    intro hzt
    have hmem : t₀ ∈ Q := by
      rw [← hc.centralizer_eq_of_e_one hzZ hz1]
      exact Subgroup.mem_centralizer_iff.mpr (by simpa using hzt)
    exact hc.not_mem (le_borel Q hmem)

theorem exists_szTriple {S : Type} [Group S] [Finite S] {n : ℕ}
    (h : BenderType S n 2 1) {s : S} (hs : s * s = 1) (hs1 : s ≠ 1) :
    ∃ c₂ c₃ : S, s * (c₂⁻¹ * s * c₂) = c₂⁻¹ * s * c₂ * s ∧ c₂⁻¹ * s * c₂ ≠ s ∧
      s * (c₃⁻¹ * s * c₃) ≠ c₃⁻¹ * s * c₃ * s ∧
      c₂⁻¹ * s * c₂ * (c₃⁻¹ * s * c₃) ≠ c₃⁻¹ * s * c₃ * (c₂⁻¹ * s * c₂) := by
  classical
  obtain ⟨a, ha, hn⟩ : ∃ a : ℕ, 1 ≤ a ∧ n = 2 * a + 1 := by
    rcases h.cases' with ⟨h1, -, -⟩ | ⟨-, -, a, ha, hn⟩ | ⟨h3, -, -⟩
    · omega
    · exact ⟨a, ha, hn⟩
    · omega
  have hn3 : 3 ≤ n := by omega
  have hpow : 2 < 2 ^ n := by
    calc 2 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have hs2 : orderOf s = 2 := by
    apply orderOf_eq_prime _ hs1
    rwa [sq]
  have hS2 : IsPGroup 2 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs2, pow_one])
  obtain ⟨Q, hsQ⟩ := IsPGroup.exists_le_sylow (G := S) (p := 2) hS2
  obtain ⟨t₀, hc⟩ := h.exists_benderCore Q
  exact exists_szTriple_of_benderCore hc hs hs1 (hsQ (Subgroup.mem_zpowers s)) hpow

end CFSG.LocalAnalysis.WeakClosure81.SzExcl
