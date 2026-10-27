module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteFSInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LargeExtraspecial.BridgeConclusion
public import CFSG.LargeExtraspecial.S14C12Lit
public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs
public import CFSG.Blueprint.Catalog
public import CFSG.GroupTheory.GLnTwoSplitting.Transvection
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S14Claims
public import CFSG.LargeExtraspecial.S4EightA
public import CFSG.LargeExtraspecial.S4EightB
public import CFSG.LargeExtraspecial.S4EightC
public import CFSG.LargeExtraspecial.S4EightD
public import CFSG.LargeExtraspecial.S4EightE
public import CFSG.LargeExtraspecial.S4EightF4
public import CFSG.LargeExtraspecial.S4EightMain
public import CFSG.LargeExtraspecial.S4SevenB3
public import CFSG.LargeExtraspecial.S5Comp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.Blueprint FrameRoute
open scoped MatrixGroups

@[expose] def GGSecFiveE6QTwoEndInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 3 B Bs x L D J → GGSecFiveWeylCase 3 B Bs x D J →
      GGSecFiveE6QTwoCfg 3 B Bs x L D J →
      LargeEvenMarking L (fun lab _ _ _ _ _ =>
        ((lab.tag = .twA ∧ lab.rank = 5) ∨ (lab.tag = .D ∧ lab.rank = 4) ∨
          (lab.tag = .twD ∧ lab.rank = 5)) ∧ lab.n = 1)

@[expose] def GGSecFiveE6QTwoFS81Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → KProper InCatalog X →
    ∀ (b₀ : X) (K E : Subgroup X), orderOf b₀ = 3 →
      K ≤ Subgroup.centralizer ({b₀} : Set X) →
      (K.subgroupOf (Subgroup.centralizer ({b₀} : Set X))).Normal → Subgroup.center K = ⊥ →
      LargeEvenMarking K (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 5 ∧ lab.n = 1) →
      (∀ S : Subgroup X, S ≤ Subgroup.centralizer (K : Set X) → IsPGroup 3 S → IsCyclic S) →
      twoLocalPrimeRank 3 (Subgroup.centralizer ({b₀} : Set X)) = twoLocalPrimeRank 3 X →
      (∃ g : X, g * b₀ * g⁻¹ ∈ Subgroup.centralizer ({b₀} : Set X) ∧
        g * b₀ * g⁻¹ ∉ Subgroup.zpowers b₀) →
      IsMaxElemAb3 (Subgroup.centralizer ({b₀} : Set X)) E → b₀ ∈ E → Nat.card E = 3 ^ 6 →
      2 ^ 6 * Nat.factorial 6 < Nat.card (ggAutomizer ⊤ E) → ¬ IsCharTwoType X

section MaxEleven

variable {X : Type} [Group X] [Finite X]

@[expose] def GGTwistedE6MaxElevenProp (M : Subgroup X) : Prop :=
  (∀ E : Subgroup X, E ≤ M → IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 4) ∨
    (∃ N : Subgroup X, N ≤ M ∧ Nat.card N = 9196830720 ∧
      ∀ P : Subgroup X, P ≤ M → ⁅P, P⁆ = P → P ≤ N) ∨
    (∀ y ∈ M, orderOf y = 3 → ¬ 11 ∣ Nat.card (M ⊓ Subgroup.centralizer {y} : Subgroup X)) ∨
    ¬ 3 ^ 7 ∣ Nat.card M

end MaxEleven

@[expose] def GGTwistedE6MaxElevenInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X], ChevalleyExceptionalModel X .twistedE6 2 1 →
    KProper InCatalog X →
    ∀ M : Subgroup X, IsCoatom M → 11 ∣ Nat.card M → GGTwistedE6MaxElevenProp M

@[expose] def GGSecFiveE6QTwoTimmesfeldInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveE6QTwoCfg 3 B Bs x L D J → CFSG.LargeExtraspecial.Bridge.OrderMainFor G

@[expose] def GGSecFiveE6QTwoBridgeInput : Prop :=
  GGSecFiveE6QTwoFS81Input ∧ GGTwistedE6MaxElevenInput

end CFSG.StandardType

end
