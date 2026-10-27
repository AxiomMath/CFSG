module

public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGResRows
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGWeylCasePrime

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTBFixNbrXInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGReflGenerated p (ggAutomizer K Bs) → GGScalarsOrWeyl' p B Bs x D J →
      ∀ b : Bs, (b : G) ∈ Subgroup.zpowers x → (∀ φ ∈ ggAutomizer K Bs, φ b = b) → (b : G) = 1

@[expose] def ggRowTwoNodeLarge (p : ℕ) (J X : LargeEvenLabel) : Prop :=
  ggRowTwoNode p J X ∧ 10 ≤ X.rank

@[expose] def GGTBFixNbrLargeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G),
    GGResHyp p B Bs x L D J y K → GGResRowAt ggRowTwoNodeLarge p J K →
    ∀ b : Bs, (∀ φ ∈ ggAutomizer K Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers y

@[expose] def GGTBFixNbrInput : Prop :=
  GGTBFixNbrXInput ∧ GGTBFixNbrLargeInput

end CFSG.StandardType

end
