module

public import CFSG.RankThree.GroupTheory.SteinbergBYCentralCoverRank
public import CFSG.RankThree.GroupTheory.SteinbergBYDegreeFourUnipotent
import CFSG.RankThree.Coprime.EvenCenterSectionCover

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open CFSG CFSG.Assembly.LowTwoRank

theorem exists_elementaryAbelian_power_action_of_mulEquiv {T T' : Type*} [Group T] [Group T']
    (e : T ≃* T') {ℓ n : ℕ}
    (h : ∃ U : Subgroup T', IsElementaryAbelian ℓ U ∧ Nat.card U = n ∧
      ∃ d : T', ∀ u ∈ U, d * u * d⁻¹ = u ^ 4) :
    ∃ U : Subgroup T, IsElementaryAbelian ℓ U ∧ Nat.card U = n ∧
      ∃ d : T, ∀ u ∈ U, d * u * d⁻¹ = u ^ 4 := by
  obtain ⟨U, hU, hUc, d, hd⟩ := h
  obtain ⟨hU', hUc'⟩ := RankThree.Coprime.isElementaryAbelian_map_mulEquiv e.symm hU
  refine ⟨U.map e.symm.toMonoidHom, hU', hUc'.trans hUc, e.symm d, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  change e.symm d * e.symm u * (e.symm d)⁻¹ = (e.symm u) ^ 4
  rw [← map_inv, ← map_mul, ← map_mul, hd u hu, map_pow]

theorem degree_four_classical_odd_central_cover_rank_four {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hℓ5 : ℓ ≠ 5) (hf : 1 ≤ f) (hℓ3 : ℓ = 3 → 2 ≤ f) {c : StatedLieTag}
    (hc : c = .PSL ∨ c = .PSU) {T : Type} [Group T] (hT : StatedClassicalModel T c 4 ℓ f)
    {Y : Type*} [Group Y] [Finite Y] (φ : Y →* T) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) : 4 ≤ pRank ℓ Y := by
  have hUd : ∃ U : Subgroup T, IsElementaryAbelian ℓ U ∧ Nat.card U = ℓ ^ (4 * f) ∧
      ∃ d : T, ∀ u ∈ U, d * u * d⁻¹ = u ^ 4 := by
    rcases hc with rfl | rfl
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hT
      exact exists_elementaryAbelian_power_action_of_mulEquiv e
        (linear_unipotent_torus hℓ hℓ2 hK)
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hT
      exact exists_elementaryAbelian_power_action_of_mulEquiv e
        (unitary_unipotent_torus hℓ hℓ2 hf hK)
  obtain ⟨U, hU, hUcard, d, hd⟩ := hUd
  by_cases hf2 : 2 ≤ f
  · exact four_le_pRank_of_central_cover hℓ hℓ2 φ hφ hker hU hUcard (by omega)
  · have hf1 : f = 1 := by omega
    have hℓ3' : ℓ ≠ 3 := fun h => hf2 (hℓ3 h)
    have hs : ¬ ℓ ∣ 4 ^ 2 - 1 := by
      intro h15
      have h15' : ℓ ∣ 3 * 5 := by simpa using h15
      rcases (Nat.Prime.dvd_mul hℓ).mp h15' with h3 | h5
      · exact hℓ3' ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp h3)
      · exact hℓ5 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_five).mp h5)
    have h := le_pRank_of_central_cover_of_power_action hℓ φ hφ hker hU hUcard hs
      (by norm_num) hd
    rw [hf1] at h
    simpa using h

end CFSG.RankThree.GroupTheory.SteinbergBY
