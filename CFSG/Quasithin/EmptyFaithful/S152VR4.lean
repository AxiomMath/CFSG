module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsSL3

public section

namespace CFSG.Quasithin.S152V

open CFSG.QuasithinUnique.Unc25K1

theorem conj_pow_eq {Ĝ : Type*} [Group Ĝ] (g h : Ĝ) (n : ℕ) : (g⁻¹ * h * g) ^ n = g⁻¹ * h ^ n * g := by
  have := map_pow (MulAut.conj g⁻¹) h n
  simpa [MulAut.conj_apply] using this.symm

theorem no_commuting_involution_S3 (H : Subgroup S3)
    (hH : Nat.card H = 9) (hexp : ∀ x ∈ H, x ^ 3 = 1) (t : S3) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (hcomm : ∀ h ∈ H, t * h = h * t) : False := by
  obtain ⟨g, hg⟩ := hconjS t ht1 ht2
  let H' : Subgroup S3 := H.map (MulAut.conj g⁻¹).toMonoidHom
  have hH'card : Nat.card H' = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hH
  have hH'mem : ∀ x ∈ H', ∃ h ∈ H, x = g⁻¹ * h * g := by
    rintro x ⟨h, hh, rfl⟩
    exact ⟨h, hh, by simp⟩
  have hsub : ∀ x ∈ H', x ∈ TlS := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := hH'mem x hx
    rw [← hTlS]
    constructor
    · have h1 := hcomm h hh
      rw [← hg] at h1
      calc g⁻¹ * h * g * u0S = g⁻¹ * (h * (g * u0S * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * u0S * g⁻¹) * h) * g := by rw [h1]
        _ = u0S * (g⁻¹ * h * g) := by group
    · rw [conj_pow_eq, hexp h hh]
      group
  have hH'3 : ∀ x ∈ H', x ^ 3 = 1 := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := hH'mem x hx
    rw [conj_pow_eq, hexp h hh]
    group
  classical
  let Hs : Finset S3 := (H' : Set S3).toFinset
  have hHs : Hs.card = 9 := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact hH'card
  have hT : TlS.toFinset.card ≤ 9 := by
    refine (List.toFinset_card_le TlS).trans ?_
    simp [TlS]
  have hsubset : Hs ⊆ TlS.toFinset := by
    intro x hx
    rw [Set.mem_toFinset] at hx
    exact List.mem_toFinset.2 (hsub x hx)
  have heq : Hs = TlS.toFinset := Finset.eq_of_subset_of_card_le hsubset (by rw [hHs]; exact hT)
  have haS : aS ∈ H' := by
    have : aS ∈ Hs := heq ▸ List.mem_toFinset.2 aS_mem
    simpa [Hs] using this
  have hbS : bS ∈ H' := by
    have : bS ∈ Hs := heq ▸ List.mem_toFinset.2 bS_mem
    simpa [Hs] using this
  have h3 := hH'3 _ (H'.mul_mem haS hbS)
  obtain ⟨-, -, h2, h4⟩ := abS
  apply h2
  have : aS * bS = 1 := by
    have h5 : (aS * bS) ^ 4 = (aS * bS) ^ 3 * (aS * bS) := pow_succ _ _
    rw [h4, h3, one_mul] at h5
    exact h5.symm
  rw [this]
  simp

end CFSG.Quasithin.S152V
