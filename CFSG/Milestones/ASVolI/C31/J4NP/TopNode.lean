module

public import CFSG.Milestones.ASVolI.C31.J4NP.TreeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.J4Tree.Native
open CFSG.Quasithin.J4Loc (omegaZ)

@[expose] noncomputable def burnsideJ4NP_topRepElts (k : ℕ) : List J :=
  (treeBasis k).map burnsideJ4NP_treeElt

theorem burnsideJ4NP_top_Rep_eq (k : ℕ) :
    burnsideJ4NP_Rep k = Subgroup.closure {g | g ∈ burnsideJ4NP_topRepElts k} := rfl

end CFSG.ASVolI
