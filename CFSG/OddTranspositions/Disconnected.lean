module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.Bridge.Asc72YU3

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72

attribute [local instance] CFSG.LocalCores.layer_characteristic

variable {G : Type} [Group G] [Finite G] {D : Set G}

end CFSG.OddTranspositions
