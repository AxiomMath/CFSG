module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedDefs

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def GGA6CharTwoLie (J : Type) [Group J] : Prop :=
  ∃ (t' : StatedLieTag) (k e : ℕ), LieModel (J ⧸ Subgroup.center J) t' k 2 e

end CFSG.StandardType.A6Red
