module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGResTwoNodeNineDepTwoRestInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs _ L _ J y K =>
    GGResRowAt ggRowTwoNodeNine p J K ∧ y ∈ K ∧ y ∉ (ggBstarComm K Bs).map Bs.subtype ∧
      GGResTwoNodeSideDatum p Bs L J

@[expose] def GGNineDepKFixLine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G),
    GGResHyp p B Bs x L D J y K →
    ¬ GGCoxeterForkDatum p Bs L K → ¬ GGCoxeterStdDatum p Bs L K →
    ¬ GGE6DepPerpCfg p Bs L K →
    GGResRowAt ggRowTwoNodeNine p J K →
    y ∉ (ggBstarComm K Bs).map Bs.subtype →
    GGResTwoNodeSideDatum p Bs L J → GGResXDatumA p Bs K 8 →
    ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers y

end CFSG.StandardType

end
