module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def twoElemGp {G : Type*} [Group G] (M : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ M ∧ ∃ k : ℕ, orderOf x = 2 ^ k}

end CFSG.StandardType.LieCore
