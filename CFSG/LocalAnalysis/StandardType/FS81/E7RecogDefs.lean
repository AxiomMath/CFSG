module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Assembly.QuasithinDefs

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Blueprint.Chevalley CFSG.QuasithinUnique

@[expose] def E7RootRecog : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y R : Subgroup X) (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y)
    (r : ↥(adjointGroup .E7 (ZMod 2))) (b : X),
    (r : ModGL .E7 (ZMod 2)) ∈ CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2) →
    orderOf r = 3 → (∃ y ∈ Y, ((ψ r : ↥Y) : X) = y * b * y⁻¹) →
    R ≤ Subgroup.centralizer (Y : Set X) → ¬ 3 ∣ Nat.card R →
    Subgroup.centralizer ({b} : Set X) = R ⊔ (Subgroup.centralizer ({b} : Set X) ⊓ Y) →
    (∀ g : X, g * b * g⁻¹ ∈ Y → ∃ y ∈ Y, g * b * g⁻¹ = y * b * y⁻¹) →
    (∀ t ∈ R, orderOf t = 2 → CharTwo (Subgroup.centralizer ({t} : Set X))) →
    (∀ s : ↥(adjointGroup .E7 (ZMod 2)),
      (s : ModGL .E7 (ZMod 2)) ∈ CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2) →
      orderOf s = 2 → CharTwo (Subgroup.centralizer ({((ψ s : ↥Y) : X)} : Set X))) →
    Y = ⊤

end CFSG.StandardType.FrameRoute.FS81
