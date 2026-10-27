module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly CFSG.StandardType

@[expose] def AmbientMarkedOverTwo : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting 3 B Bs x L D J →
      ∃ lab : LargeEvenLabel, lab.n = 1 ∧
        GGInnerDiagOnLabel (fun _ l => l = lab) 3 Bs (ggG0 3 B x L D J)

end CFSG.StandardType.GGQ2Frame
