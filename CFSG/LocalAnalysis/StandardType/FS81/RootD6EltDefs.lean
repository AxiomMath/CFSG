module

public import CFSG.LocalAnalysis.StandardType.FS81.RootD6ModelDefs

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley

@[expose] def E7TorusRootLines : Prop :=
  ∀ A : Subgroup ↥(adjointGroup .E7 (ZMod 2)), IsElemAbelian 3 A → Nat.card A = 3 ^ 7 →
    ∃ Q : Subgroup ↥(adjointGroup .E7 (ZMod 2)), IsPGroup 2 Q ∧
      Q ≤ Subgroup.normalizer (A : Set ↥(adjointGroup .E7 (ZMod 2))) ∧
      ∀ a ∈ A, a ≠ 1 →
        Q ≤ Subgroup.normalizer (Subgroup.zpowers a : Set ↥(adjointGroup .E7 (ZMod 2))) →
        ∃ g : ↥(adjointGroup .E7 (ZMod 2)),
          ((g * a * g⁻¹ : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) ∈
            CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2)

end CFSG.StandardType.FrameRoute.FS81
