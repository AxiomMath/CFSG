module

public import CFSG.Quasithin.Background.F7TwoInvD4Field

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.EvenBN.TrialityD4
open CFSG.ComponentClassification.OuterAutomorphisms (inner)


theorem exists_conj_φ₀ {X : Type} [Group X] {f : ℕ} (d : TrialityD4Data X (2 ^ f)) (hf1 : 1 ≤ f)
    (hX : TwistedChevalleyModel X .D4 (2 ^ f)) {φ : MulAut X} (hφ2 : φ ^ 2 = 1)
    (hφo : φ ∉ inner X) : Even f ∧ ∃ ψ : MulAut X, ψ * φ * ψ⁻¹ = d.φ ^ (3 * f / 2) := by
  obtain ⟨M, _, _, σ, hM, hσ, ⟨E⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf1 hX
  have hα₁2 : MulAut.congr E φ ^ 2 = 1 := by rw [← map_pow, hφ2, map_one]
  have hα₁o : MulAut.congr E φ ∉ inner (graphFixedRootGroup TwistTag.D4 M σ.toRingHom) := by
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hφo
  obtain ⟨hev, δ, hδ, -, ψ₁, hψ₁, -⟩ := even_triality_outer_involutions_canonical_field hf1 M hM
    σ hσ (MulAut.congr E φ) hα₁2 hα₁o
  refine ⟨hev, ?_⟩
  obtain ⟨hord, hinn, -, -⟩ := d.yamada_3_13_1 hev rfl
  have hφ₀2 : (d.φ ^ (3 * f / 2)) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (d.φ ^ (3 * f / 2))
    rwa [hord] at h
  have hα₂2 : MulAut.congr E (d.φ ^ (3 * f / 2)) ^ 2 = 1 := by
    rw [← map_pow, hφ₀2, map_one]
  have hα₂o : MulAut.congr E (d.φ ^ (3 * f / 2)) ∉
      inner (graphFixedRootGroup TwistTag.D4 M σ.toRingHom) := by
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hinn
  obtain ⟨-, δ', hδ', -, ψ₂, hψ₂, -⟩ := even_triality_outer_involutions_canonical_field hf1 M hM
    σ hσ (MulAut.congr E (d.φ ^ (3 * f / 2))) hα₂2 hα₂o
  have hδδ : δ' = δ := RingEquiv.ext fun c => by rw [hδ', hδ]
  rw [hδδ] at hψ₂
  refine ⟨(MulAut.congr E).symm (ψ₂⁻¹ * ψ₁), (MulAut.congr E).injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  calc ψ₂⁻¹ * ψ₁ * MulAut.congr E φ * (ψ₂⁻¹ * ψ₁)⁻¹
      = ψ₂⁻¹ * (ψ₁ * MulAut.congr E φ * ψ₁⁻¹) * ψ₂ := by group
    _ = MulAut.congr E (d.φ ^ (3 * f / 2)) := by rw [hψ₁, ← hψ₂]; group

theorem invAutGen_of_trialityD4Data {X : Type} [Group X] {f : ℕ} (d : TrialityD4Data X (2 ^ f))
    (hf1 : 1 ≤ f) (hX : TwistedChevalleyModel X .D4 (2 ^ f)) {φ : MulAut X}
    (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1) : InvAutGen X φ := by
  by_cases hin : φ ∈ inner X
  · obtain ⟨y, rfl⟩ := hin
    have hyy : y * y = 1 := d.mulAutConj_injective (by rw [map_mul, map_one]; exact hφ2)
    have hy1 : y ≠ 1 := fun h => hφ1 (by rw [h, map_one])
    have h2 : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hyy) hy1
    obtain ⟨g, hg | hg⟩ := d.involution_conj y h2
    · exact invAutGen_conj_of_isConj (isConj_iff.2 ⟨g⁻¹, by rw [← hg]; group⟩)
        (invAutGen_conj_x₆ d)
    · exact invAutGen_conj_of_isConj (isConj_iff.2 ⟨g⁻¹, by rw [← hg]; group⟩)
        (invAutGen_conj_x₄ d)
  · obtain ⟨hev, ψ, hψ⟩ := exists_conj_φ₀ d hf1 hX (by rw [sq]; exact hφ2) hin
    exact invAutGen_of_conj_aut ψ⁻¹ (by rw [← hψ]; group) (invAutGen_φ₀ d rfl hev)

end CFSG.Quasithin.F7Two
