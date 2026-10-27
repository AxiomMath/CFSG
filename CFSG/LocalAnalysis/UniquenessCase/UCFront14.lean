module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.RankThreeUC.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F14

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def FunSet (IsFundamental : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Prop)
    (X : Type) [Group X] (S : Subgroup X) : Set (Subgroup X) :=
  {Kb | IsFundamental (⊤ : Subgroup X) Kb ∧ CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ Kb) Kb}

end CFSG.LocalAnalysis.UniquenessCase.UC22.F14
