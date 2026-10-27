module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Catalog

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly TauCeti Subgroup

@[expose] def NoLowTwoRankSectionFor (P : CFSGIndex → Prop) : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsKGroup L → CFSG.Assembly.evenRank L ≤ 3 →
    ∀ (H : Subgroup L) (M : Type) [Group M] [Finite M], CFSG.IsQuasisimple M → ∀ π : H →* M,
      Function.Surjective π →
      (¬ ∃ U : Subgroup (M ⧸ center M), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ (3 + 2)) →
      (∃ i : CFSGIndex, P i ∧ Nonempty ((M ⧸ center M) ≃* i.Group)) → False

namespace NoLowTwoRankSectionFor

theorem mono {P Q : CFSGIndex → Prop} (h : NoLowTwoRankSectionFor Q) (hPQ : ∀ i, P i → Q i) :
    NoLowTwoRankSectionFor P :=
  fun L _ _ hK he H M _ _ hM π hπ hU ⟨i, hi, e⟩ => h L hK he H M hM π hπ hU ⟨i, hPQ i hi, e⟩

end NoLowTwoRankSectionFor

@[expose] def IsHardL3Index : CFSGIndex → Prop
  | .lie ⟨.A r q, _⟩ => r = 2 ∧ q.p ≠ 2 ∧ 4 ≤ q.exponent
  | .lie ⟨.twistedA r q, _⟩ => r = 2 ∧ q.p ≠ 2 ∧ 4 ≤ q.exponent
  | _ => False

@[expose] def IsHardRankTwoIndex : CFSGIndex → Prop
  | .lie ⟨.A r q, _⟩ => r = 3 ∧ q.p ≠ 2 ∧ 2 ≤ q.exponent
  | .lie ⟨.twistedA r q, _⟩ => r = 3 ∧ q.p ≠ 2 ∧ 2 ≤ q.exponent
  | .lie ⟨.B r q, _⟩ => r = 2 ∧ q.p ≠ 2 ∧ 2 ≤ q.exponent
  | _ => False

@[expose] def IsHardExceptionalIndex : CFSGIndex → Prop
  | .lie ⟨.G2 q, _⟩ => q.p ≠ 2 ∧ 2 ≤ q.exponent
  | .lie ⟨.reeG2 m, _⟩ => 2 ≤ m
  | .lie ⟨.trialityD4 q, _⟩ => q.p ≠ 2
  | _ => False

@[expose] def IsHardLowTwoIndex (i : CFSGIndex) : Prop :=
  IsHardL3Index i ∨ IsHardRankTwoIndex i ∨ IsHardExceptionalIndex i

theorem noLowTwoRankSectionFor_hard (h3 : NoLowTwoRankSectionFor IsHardL3Index)
    (h4 : NoLowTwoRankSectionFor IsHardRankTwoIndex)
    (hE : NoLowTwoRankSectionFor IsHardExceptionalIndex) :
    NoLowTwoRankSectionFor IsHardLowTwoIndex :=
  fun L _ _ hK he H M _ _ hM π hπ hU ⟨i, hi, e⟩ => by
    rcases hi with hi | hi | hi
    · exact h3 L hK he H M hM π hπ hU ⟨i, hi, e⟩
    · exact h4 L hK he H M hM π hπ hU ⟨i, hi, e⟩
    · exact hE L hK he H M hM π hπ hU ⟨i, hi, e⟩

end CFSG.RankThree.PartOne.N143
