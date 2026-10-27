module

public import CFSG.LocalAnalysis.StandardType.GGTWLowStmt

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGPZE6Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime]
    (labJ labX : LargeEvenLabel) (X : Subgroup G) (m : ℕ), (X = L ∨ X = K) →
    LargeEvenInLambda2 labJ →
    LargeEvenInLambda2 labX → GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) →
    GGHasLabel labX (↥X ⧸ Subgroup.center ↥X) → ggRowTwoNodeSmall p labJ labX →
    ((labX.tag = .E6 ∨ labX.tag = .twE6) ∧ m = 6) → Nat.card ↥Bs = p ^ m →
    Nat.card ↥(Bs ⊓ J) = p ^ labJ.rank → GGReflGenerated p (ggAutomizer J Bs) →
    ∀ z : ↥Bs, (z : G) ∈ D → (z : G) ∉ Subgroup.zpowers x →
    (z : G) ∉ Subgroup.zpowers y →
      ∃ r n c : ℕ, GGWeylTypeData r n c ∧ labJ.rank ≤ r ∧ r ≤ m ∧
        Nat.card ↥(Subgroup.closure (ggPZOrbit p (ggAutomizer J Bs)
          (ggAutomizer L Bs ⊔ ggAutomizer K Bs) z)) ∣ n ∧
        (Nat.card ↥(Subgroup.closure (ggPZOrbit p (ggAutomizer J Bs)
            (ggAutomizer L Bs ⊔ ggAutomizer K Bs) z)) = n →
          Nat.card ↥(Subgroup.center ↥(Subgroup.closure (ggPZOrbit p (ggAutomizer J Bs)
            (ggAutomizer L Bs ⊔ ggAutomizer K Bs) z))) = c)

end CFSG.StandardType

end
