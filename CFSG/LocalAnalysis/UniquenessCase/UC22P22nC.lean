module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p22nc_le_normalizer_inf_centralizer {M V : Subgroup G}
    (hMV : M ≤ normalizer (V : Set G)) :
    M ≤ normalizer ((M ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := by
  have hconj : ∀ m ∈ M, ∀ k ∈ M ⊓ centralizer (V : Set G),
      m * k * m⁻¹ ∈ M ⊓ centralizer (V : Set G) := by
    intro m hm k hk
    obtain ⟨hkM, hkC⟩ := Subgroup.mem_inf.1 hk
    refine Subgroup.mem_inf.2 ⟨M.mul_mem (M.mul_mem hm hkM) (M.inv_mem hm), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : m⁻¹ * v * m ∈ V := by
      have := ((Subgroup.mem_normalizer_iff.1 (hMV (M.inv_mem hm))) v).1 hv
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hkC _ hv'
    calc v * (m * k * m⁻¹) = m * ((m⁻¹ * v * m) * k) * m⁻¹ := by group
      _ = m * (k * (m⁻¹ * v * m)) * m⁻¹ := by rw [h1]
      _ = m * k * m⁻¹ * v := by group
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact hconj m hm k hk
  · intro hk
    have := hconj m⁻¹ (M.inv_mem hm) _ hk
    simpa [mul_assoc] using this

theorem uc22p22nc_inCalV1_of_good (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ} (hp : p ∈ D.sig)
    {V P : Subgroup G} (hV : InCalV D.M V) (hPM : P ≤ D.M) (hPp : IsPGroup p P)
    (hPc : ¬ IsCyclic P) (hPV : P ⊓ centralizer (V : Set G) = ⊥) : InCalV1 D.M D.T V := by
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM : D.M ⊓ centralizer (V : Set G) ≤ D.M := inf_le_left
  have hMK := uc22p22nc_le_normalizer_inf_centralizer hV.2.2.1
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ centralizer (V : Set G))
      (D.M ⊓ centralizer (V : Set G)) := by
    have h := D.sylowM.inf_of_le_normalizer hKM hMK
    rwa [← inf_assoc, inf_eq_left.2 D.sylowM.le] at h
  have hPK : P ⊓ (D.M ⊓ centralizer (V : Set G)) = ⊥ := by
    rw [← inf_assoc, inf_eq_left.2 hPM, hPV]
  obtain ⟨X, hXM, hXp, hXnc, hXN⟩ := uc22p22e_frattini_sub hKM hMK hS hPp hPM hPK hPc
  refine ⟨hV, Set.eq_singleton_iff_unique_mem.2 ⟨⟨D.maxLocal, inf_le_left⟩, ?_⟩⟩
  rintro N ⟨hNloc, hNle⟩
  have hNX : N ∈ calMOf X :=
    ⟨hNloc, fun x hx => hNle (Subgroup.mem_inf.2 ⟨hXM hx, hXN hx⟩)⟩
  have h1 : calMOf X = {D.M} := h61 p hp X hXM hXp hXnc
  rw [h1] at hNX
  exact hNX

end CFSG.LocalAnalysis.UniquenessCase.UC22
