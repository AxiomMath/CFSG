module

public import CFSG.LocalAnalysis.StandardType.FS81.RootE8Defs
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRoots

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley

theorem RootSetting.torus_le {G : Type} [Group G] [Finite G] {r : Row} {b₀ : G}
    {K E : Subgroup G} {B : Basis3 G (r.n + 1)} {Y : Subgroup G}
    (h : RootSetting r b₀ K E B Y) : E ≤ Y := by
  have hKY : Subgroup.zpowers b₀ ⊔ K ≤ Y := by
    rw [← h.cap]
    exact inf_le_right
  rw [← h.std.2.2.2.2.1]
  exact sup_le (le_sup_left.trans hKY) (inf_le_right.trans (le_sup_right.trans hKY))

@[expose] def IsEmSevenModel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y : Subgroup G), IsEm 7 Y →
    Nonempty (↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y)

@[expose] def D6RootEltAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G) (B : Basis3 G (Row.D6.n + 1))
    (Y : Subgroup G), RootSetting Row.D6 b₀ K E B Y →
    ∀ ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥Y, ∃ r : ↥(adjointGroup .E7 (ZMod 2)),
      (r : ModGL .E7 (ZMod 2)) ∈ CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2) ∧
      ∃ y ∈ Y, ((ψ r : ↥Y) : G) = y * b₀ * y⁻¹

end CFSG.StandardType.FrameRoute.FS81
