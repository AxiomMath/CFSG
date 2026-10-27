module

public import CFSG.RankThree.PartOne.N143.SectionListLieC

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly TauCeti Subgroup

@[expose] def TwoPowFiveFor (P : CFSGIndex → Prop) : Prop :=
  ∀ i : CFSGIndex, P i → ∀ (T : Type) [Group T], Nonempty (T ≃* i.Group) →
    ∃ U : Subgroup T, IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ (3 + 2)

theorem NoLowTwoRankSectionFor.of_twoPowFive {P : CFSGIndex → Prop} (h : TwoPowFiveFor P) :
    NoLowTwoRankSectionFor P :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hU ⟨i, hi, e⟩ => hU (h i hi _ e)

@[expose] def IsLieLowTwoRankIndex : CFSGIndex → Prop
  | .lie ⟨.A r q, _⟩ => (r = 4 ∧ q.p ≠ 2) ∨ (r = 5 ∧ q.card % 4 = 3)
  | .lie ⟨.twistedA r q, _⟩ => (r = 4 ∧ q.p ≠ 2) ∨ (r = 5 ∧ q.card % 4 = 1)
  | .lie ⟨.C r _, _⟩ => r = 3
  | _ => False

@[expose] def IsLieTwoPowFiveIndex (i : CFSGIndex) : Prop :=
  IsLieUnlistedRestIndex i ∧ ¬ IsLieLowTwoRankIndex i

theorem noLowTwoRankSectionFor_rest_of_split (h5 : TwoPowFiveFor IsLieTwoPowFiveIndex)
    (hLow : NoLowTwoRankSectionFor IsLieLowTwoRankIndex) :
    NoLowTwoRankSectionFor IsLieUnlistedRestIndex := by
  intro L _ _ hK he H M _ _ hM π hπ hU ⟨i, hi, e⟩
  by_cases hl : IsLieLowTwoRankIndex i
  · exact hLow L hK he H M hM π hπ hU ⟨i, hl, e⟩
  · exact (NoLowTwoRankSectionFor.of_twoPowFive h5) L hK he H M hM π hπ hU ⟨i, ⟨hi, hl⟩, e⟩

end CFSG.RankThree.PartOne.N143
