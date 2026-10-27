module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGTWRowData
public import CFSG.LocalAnalysis.StandardType.GGTWRowDataL
public import CFSG.LocalAnalysis.StandardType.GGResXDatumAHLK
public import CFSG.LocalAnalysis.StandardType.GGHLNbrInput
public import CFSG.LocalAnalysis.StandardType.GGTWRowGenDefs
public import CFSG.LocalAnalysis.StandardType.GGResXDatumARankFrom
public import CFSG.LocalAnalysis.StandardType.GGResXDatumAHLFrom

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTWTwA5Open : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    ∀ (X : Subgroup G) (z : G), (X = L ∧ z = x) ∨ (X = K ∧ z = y) → p = 3 →
      ∀ labX : LargeEvenLabel, LargeEvenInLambda2 labX → GGHasLabel labX (↥X ⧸ Subgroup.center ↥X) →
        (labX.tag = .twA ∧ labX.rank = 5 ∧ 3 ∣ 2 ^ labX.n + 1) →
        Nonempty (↥(ggAutomizer X Bs) ≃* Equiv.Perm (Fin 6)) ∧
          ((X = L ∧ z = x) → GGTWHLAt p Bs X z) ∧
          ((X = K ∧ z = y) → y ∉ K → Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y →
            GGTWHLAt p Bs X z)

end CFSG.StandardType

end
