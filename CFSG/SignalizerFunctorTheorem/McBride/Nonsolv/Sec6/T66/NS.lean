module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.GroupBasic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T65

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem mem_msig_thetaNs_of_mem_nsSet (h : Counterexample p A θ) {X : Subgroup G}
    (hX : X ∈ Msig p A θ) (hD : thetaOf θ A ≤ X) {Y : Subgroup G} (hY : Y ∈ nsSet p A X) :
    Y ∈ Msig p A (thetaNs p A θ) := by
  obtain ⟨hYX, hDY, hAY, hel, hB, hsolv⟩ := hY
  refine ⟨hAY, hX.2.1.of_dvd_right (Subgroup.card_dvd_of_le hYX), fun a ha ha1 => ?_, hB⟩
  have hmem : Y ⊓ Subgroup.centralizer {a} ∈ nsSet p A (θ a) := by
    refine ⟨(inf_le_inf_right _ hYX).trans (hX.2.2.1 a ha ha1), ?_, ?_, ?_⟩
    ·
      intro d hd
      have hdD : d ∈ thetaOf θ A := by
        rw [← h.isFunctor.inf_centralizer_self ha ha1]
        exact hd
      refine Subgroup.inf_normalizer_le_normalizer_inf ⟨hDY ⟨hD hdD, hd.2⟩, ?_⟩
      exact mem_normalizer_centralizer_singleton
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha) hd.2)
    ·
      intro a' ha'
      refine Subgroup.inf_normalizer_le_normalizer_inf ⟨hAY ha', ?_⟩
      refine mem_normalizer_centralizer_singleton ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact comm_of_mem_of_isMulCommutative h.elemAbelian.1 ha' ha
    · refine ⟨hel, hypB_mono inf_le_left hB, ?_⟩
      have hle : Y ⊓ Subgroup.centralizer {a} ⊓ Subgroup.centralizer (A : Set G) ≤
          Y ⊓ Subgroup.centralizer (A : Set G) :=
        inf_le_inf_right _ inf_le_left
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  exact le_iSup₂_of_le _ hmem le_rfl

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
