module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGStdPair {G : Type} [Group G] (p : ℕ) (Bs : Subgroup G) (w : G) (X : Subgroup G) :
    Prop :=
  w ∈ Bs ∧ w ≠ 1 ∧ LargeEvenPComponent p (Subgroup.centralizer ({w} : Set G)) X ∧
    Bs ≤ Subgroup.normalizer (X : Set G) ∧
    (∀ b ∈ Bs, ⁅X, Subgroup.zpowers b⁆ ≤ LargeEvenPPrimeCoreOf p X ↔ b ∈ Subgroup.zpowers w) ∧
    ggAutomizer X Bs ≠ ⊥

@[expose] def GGQTwoK1 {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (D J : Subgroup G) : Prop :=
  ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → ∀ b ∈ Bs,
    ⁅K, Subgroup.zpowers b⁆ ≤ LargeEvenPPrimeCoreOf p K → b ∈ Subgroup.zpowers y

@[expose] def GGQTwoI1 {G : Type} [Group G] (Bs D J : Subgroup G) : Prop :=
  ∀ b ∈ Bs, (∀ j ∈ J, b * j = j * b) → b ∈ D

end CFSG.StandardType

end
