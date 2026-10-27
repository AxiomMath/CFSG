module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGResTwoNodeLE3Input : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs x L _ J y K =>
    (GGResRowAt ggRowTwoNodeLarge p J L ∧ x ∉ L ∧ GGResLeviSideDatumLE3 p Bs K J) ∨
      (GGResRowAt ggRowTwoNodeLarge p J K ∧ y ∉ K ∧ GGResLeviSideDatumLE3 p Bs L J)

end CFSG.StandardType

end
