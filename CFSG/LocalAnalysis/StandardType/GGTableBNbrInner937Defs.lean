module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRound13Label
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerClassicalModel
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrInner937F4Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .F4 ∧ p = 3 ∧ p ∣ 2 ^ lab.n + 1

@[expose] def GGNbrInner937ExcPlusLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E7 ∨ lab.tag = .E8) ∧ (p = 3 ∨ p = 5) ∧ p ∣ 2 ^ lab.n + 1

@[expose] def GGNbrInner937TwE6Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ p = 3 ∧ p ∣ 2 ^ lab.n - 1

@[expose] def GGNbrInner937U63Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twA ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1) ∧ lab.rank = 5 ∧ p = 3

@[expose] def GGNbrKGExcPlusSCWeylIrred : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), (p = 3 ∨ p = 5) → p ∣ Nat.card K + 1 →
    GGSCWeylIrred p 6 (TableBExc.RecipeGroup .E7 K) ∧
      GGSCWeylIrred p 7 (TableBExc.RecipeGroup .E8 K)

@[expose] def GGNbrKGTwE6ThreeSubSCWeylIrred : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → 3 ∣ 2 ^ n - 1 →
    GGSCWeylIrred 3 4 (TwE6Delta.RecipeR K n)

@[expose] def GGUnitDvd63NbrRankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
        GGInnerDiagOnLabel GGNbrInner937U63Label p Bs K → p ^ 4 ≤ Nat.card (ggGamma K hN).range

@[expose] def GGTableBNbrInnerRound14ExcLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGTableBNbrInnerRound13ExcLabel p lab ∧
    ¬ (GGNbrInner937F4Label p lab ∨ GGNbrInner937ExcPlusLabel p lab ∨
      GGNbrInner937TwE6Label p lab ∨ GGNbrInner937U63Label p lab)

end CFSG.StandardType

end
