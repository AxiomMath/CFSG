module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

public section

namespace CFSG.Quasithin.C124

open Equiv Equiv.Perm

theorem exists_odd_centralizer {m : ℕ} (hm : 5 ≤ m) {s : Perm (Fin m)} (hs3 : s ^ 3 = 1)
    (hs1 : s ≠ 1) : ∃ z ∈ Subgroup.centralizer {s}, sign z = -1 := by
  have hcyc : ∀ c ∈ s.cycleType, c = 3 := by
    intro c hc
    have hc3 : c ∣ 3 := (dvd_of_mem_cycleType hc).trans (orderOf_dvd_of_pow_eq_one hs3)
    have h2 : 2 ≤ c := two_le_of_mem_cycleType hc
    rcases (Nat.dvd_prime Nat.prime_three).1 hc3 with h | h <;> omega
  by_contra hcon
  push Not at hcon
  have hle : Subgroup.centralizer {s} ≤ alternatingGroup (Fin m) := by
    intro z hz
    rw [mem_alternatingGroup]
    rcases Int.units_eq_one_or (sign z) with h | h
    · exact h
    · exact absurd h (hcon z hz)
  have hcard := card_le_of_centralizer_le_alternating hle
  have hcount := count_le_one_of_centralizer_le_alternating hle
  have hne : s.cycleType ≠ 0 := fun h => hs1 (cycleType_eq_zero.1 h)
  obtain ⟨c, hc⟩ := Multiset.exists_mem_of_ne_zero hne
  have hc3 : c = 3 := hcyc c hc
  have hrep : s.cycleType = Multiset.replicate (Multiset.card s.cycleType) 3 :=
    Multiset.eq_replicate_card.2 hcyc
  have hcnt : Multiset.card s.cycleType ≤ 1 := by
    have := hcount 3
    rwa [hrep, Multiset.count_replicate_self] at this
  have hsum : s.cycleType.sum ≤ 3 := by
    rw [hrep, Multiset.sum_replicate]
    simp only [smul_eq_mul]
    omega
  rw [Fintype.card_fin] at hcard
  omega

theorem exists_inv_conj_alt {m : ℕ} (hm : 5 ≤ m) {σ : alternatingGroup (Fin m)} (h3 : σ ^ 3 = 1)
    (h1 : σ ≠ 1) : ∃ τ : alternatingGroup (Fin m), τ * σ * τ⁻¹ = σ⁻¹ := by
  set s : Perm (Fin m) := (σ : Perm (Fin m)) with hs
  have hs3 : s ^ 3 = 1 := by simpa using congrArg Subtype.val h3
  have hs1 : s ≠ 1 := fun h => h1 (Subtype.ext h)
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 (cycleType_inv s).symm)
  obtain ⟨z, hz, hzs⟩ := exists_odd_centralizer hm hs3 hs1
  have hzc : z * s * z⁻¹ = s := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hz
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  rcases Int.units_eq_one_or (sign g) with h | h
  · refine ⟨⟨g, mem_alternatingGroup.2 h⟩, Subtype.ext ?_⟩
    simpa using hg
  · refine ⟨⟨g * z, mem_alternatingGroup.2 (by rw [map_mul, h, hzs]; rfl)⟩, Subtype.ext ?_⟩
    have : g * z * s * (g * z)⁻¹ = g * (z * s * z⁻¹) * g⁻¹ := by group
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    rw [← hs, this, hzc, hg]

end CFSG.Quasithin.C124
