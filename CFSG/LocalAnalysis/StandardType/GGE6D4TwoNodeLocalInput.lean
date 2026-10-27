module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGE6D4TwoNodeLocalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp 3 B Bs x L D J y K →
    ∀ (X : Subgroup G) (z : G), (X = L ∧ z = x) ∨ (X = K ∧ z = y) →
      ∀ labJ labX : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labX →
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) → GGHasLabel labX (↥X ⧸ Subgroup.center ↥X) →
        ggRowTwoNode 3 labJ labX → (labX.tag = .E6 ∨ labX.tag = .twE6) →
        (Nat.card Bs = 3 ^ 6 ∨ Nat.card Bs = 3 ^ 7) ∧ Nat.card (Bs ⊓ J : Subgroup G) = 3 ^ 4 ∧
          GGReflGenerated 3 (ggAutomizer J Bs) ∧ GGResXDatumE6x 3 Bs X z ∧
          Nat.card ↥(ggAutomizer J Bs) = 192 ∧ GGResTwoNodeSideDatum 3 Bs X J

@[expose] def GGE6D4TwoNodeLocalRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp 3 B Bs x L D J y K →
    ∀ (X : Subgroup G) (z : G), (X = L ∧ z = x) ∨ (X = K ∧ z = y) →
      ∀ labJ labX : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labX →
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) → GGHasLabel labX (↥X ⧸ Subgroup.center ↥X) →
        ggRowTwoNode 3 labJ labX → (labX.tag = .E6 ∨ labX.tag = .twE6) →
        (labX.tag = .twE6 → GGResXDatumE6x 3 Bs X z) ∧ GGResTwoNodeSideDatum 3 Bs X J

@[expose] def GGE6D4TwoNodeTwXDatum : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp 3 B Bs x L D J y K →
    ∀ (X : Subgroup G) (z : G), (X = L ∧ z = x) ∨ (X = K ∧ z = y) →
      ∀ labJ labX : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labX →
        GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) → GGHasLabel labX (↥X ⧸ Subgroup.center ↥X) →
        ggRowTwoNode 3 labJ labX → labX.tag = .twE6 → GGResXDatumE6x 3 Bs X z

end CFSG.StandardType

end
