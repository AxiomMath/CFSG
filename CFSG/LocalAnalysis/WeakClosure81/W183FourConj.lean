module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalSuzuki
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

theorem w183four_conj_cases {L T : Subgroup G}
    (h : Set.ncard {X : Subgroup G | ∃ t ∈ T, X = conjSubgroup L t} ≤ 2) :
    (∀ t ∈ T, conjSubgroup L t = L) ∨
      ∃ t ∈ T, conjSubgroup L t ≠ L ∧
        ∀ s ∈ T, conjSubgroup L s = L ∨ conjSubgroup L s = conjSubgroup L t := by
  classical
  by_cases hall : ∀ t ∈ T, conjSubgroup L t = L
  · exact Or.inl hall
  · right
    obtain ⟨t, htT, hne⟩ : ∃ t ∈ T, conjSubgroup L t ≠ L := by
      by_contra hc
      exact hall fun t ht => by
        by_contra hh
        exact hc ⟨t, ht, hh⟩
    refine ⟨t, htT, hne, fun s hs => ?_⟩
    set S : Set (Subgroup G) := {X | ∃ t ∈ T, X = conjSubgroup L t} with hS
    have hLS : L ∈ S := ⟨1, T.one_mem, (conjSubgroup_one L).symm⟩
    have htS : conjSubgroup L t ∈ S := ⟨t, htT, rfl⟩
    have hsub : ({L, conjSubgroup L t} : Set (Subgroup G)) ⊆ S := by
      intro X hX
      rcases hX with rfl | rfl
      · exact hLS
      · exact htS
    have hcard : ({L, conjSubgroup L t} : Set (Subgroup G)).ncard = 2 :=
      Set.ncard_pair (Ne.symm hne)
    have heq : ({L, conjSubgroup L t} : Set (Subgroup G)) = S :=
      Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite S)
    have hsS : conjSubgroup L s ∈ S := ⟨s, hs, rfl⟩
    rw [← heq] at hsS
    rcases hsS with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1

theorem w183four_le_normalizer {L T H : Subgroup G} (hLT : L ⊔ T = H)
    (h : ∀ t ∈ T, conjSubgroup L t = L) : H ≤ Subgroup.normalizer (L : Set G) := by
  rw [← hLT]
  refine sup_le Subgroup.le_normalizer ?_
  intro t ht
  rw [Subgroup.mem_set_normalizer_iff]
  intro l
  have h1 : l ∈ conjSubgroup L t ↔ t * l * t⁻¹ ∈ L := mem_conjSubgroup_iff
  rw [h t ht] at h1
  exact h1

end CFSG.LocalAnalysis.WeakClosure81

end
