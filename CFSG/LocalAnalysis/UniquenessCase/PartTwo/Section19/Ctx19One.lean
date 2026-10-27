module

public import CFSG.Adapters.LieModelSimple
public import CFSG.GroupTheory.OddAutomorphismTwoGroup
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FSqIndex

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem card_bar2_of_isAlt_five {K : Subgroup G} (h : IsAlt (Bar2 K) 5) :
    Nat.card (Bar2 K) = 60 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

theorem isSimpleGroup_bar2_of_isAlt_five {K : Subgroup G} (h : IsAlt (Bar2 K) 5) :
    IsSimpleGroup (Bar2 K) := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 5))
  exact e.isSimpleGroup

theorem isSimpleGroup_bar2_of_shape {L : Subgroup G}
    (h : IsL2 (Bar2 L) 2 ∨ IsU3 (Bar2 L) 2) : IsSimpleGroup (Bar2 L) := by
  rcases h with hs | hs
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hs
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hs

theorem three_dvd_bar2_of_shape {L : Subgroup G}
    (h : IsL2 (Bar2 L) 2 ∨ IsU3 (Bar2 L) 2) : 3 ∣ Nat.card (Bar2 L) := by
  rcases h with hs | hs
  · have hsc : CFSG.Assembly.LowTwoRank.StatedClassicalModel (Bar2 L) .PSL 2 2 2 :=
      CFSG.Blueprint.LieModel.statedClassicalModel hs (by decide)
    have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two hsc).1 rfl
    rw [h1]
    decide
  · have hsc : CFSG.Assembly.LowTwoRank.StatedClassicalModel (Bar2 L) .PSU 3 2 2 :=
      CFSG.Blueprint.LieModel.statedClassicalModel hs (by decide)
    have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two hsc).2.1 rfl
    rw [h1]
    decide

theorem three_dvd_bar2_of_isAlt {K : Subgroup G} (h : IsAlt (Bar2 K) 5) :
    3 ∣ Nat.card (Bar2 K) := by
  rw [card_bar2_of_isAlt_five h]
  norm_num

theorem le_centralizer_of_bar2_simple
    {V₀ L : Subgroup G} (hLperf : ⁅L, L⁆ = L) (hLsimple : IsSimpleGroup (Bar2 L))
    (h5 : 5 ∣ Nat.card (Bar2 L)) (hLN : L ≤ normalizer (V₀ : Set G))
    (hV2 : IsPGroup 2 V₀) (h8 : Nat.card V₀ ≤ 8) :
    L ≤ centralizer (V₀ : Set G) :=
  CFSG.GroupTheory.le_centralizer_of_perfect_of_isSimple_quotient
    (CFSG.pCore 2 ↥L) hLperf CFSG.pCore_isPGroup hLsimple h5 hLN hV2 h8

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
