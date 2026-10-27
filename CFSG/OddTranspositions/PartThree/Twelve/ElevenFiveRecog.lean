module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveChart
import CFSG.OddTranspositions.PartThree.Twelve.NineGraphIso

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.Fischer

theorem isFiveReflectionModel_of_commGraphIso {G : Type} [Group G] {D : Set G} {n : ℕ}
    {ε π : Bool} (hS : Setup G D) (hS' : Setup (fiveProjective n ε π) (fiveProjClass n ε π))
    (hZ : Subgroup.center G = ⊥) (hZ' : Subgroup.center (fiveProjective n ε π) = ⊥)
    (β : commGraph (fiveProjClass n ε π) ≃g commGraph D)
    (haxis : ∀ u : D, ∀ σ : commGraph D ≃g commGraph D,
      (∀ v : D, Commute (v : G) u → σ v = v) →
      (∀ v : D, σ v = v) ∨ ∀ v : D, (σ v : G) = (u : G) * v * u) :
    IsFiveReflectionModel n ε π D := by
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_of_commGraphIso hS' hS hZ' hZ β haxis
  rw [isFiveReflectionModel_iff_proj]
  refine ⟨φ.symm, fun g => ?_⟩
  constructor
  · intro hg
    obtain ⟨x, hx⟩ := β.surjective ⟨g, hg⟩
    have h1 : φ (x : fiveProjective n ε π) = g := by
      rw [hφ x, hx]
    have h2 : φ.symm g = x := by
      rw [← h1]
      exact φ.symm_apply_apply _
    rw [h2]
    exact x.2
  · intro hg
    have h3 : φ (φ.symm g) ∈ D := by
      have h4 := (β ⟨φ.symm g, hg⟩).2
      rwa [← hφ ⟨φ.symm g, hg⟩] at h4
    rwa [φ.apply_symm_apply] at h3

end CFSG.OddTranspositions.PartThree

end
