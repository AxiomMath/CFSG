module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFAt

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.RCKRP
open CFSG.Open (StatedLieTag)

@[expose] def RCKIIpAt
    (P : StatedLieTag → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L K : Subgroup X) (e : X), P t → GGSixRCKJRow .IIp J →
    RCKCompConfig t n f ψ p G₀ A B₁ D J L K e → K = J ∨ SLFourEmbed K J ∨ OmegaSixEmbed K J

@[expose] def RCKLemmaFIIp :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K J B : Subgroup X) (d : X),
    p.Prime → p ≠ 2 → IsElemAbelian p B → d ∈ B → B ≤ Subgroup.normalizer (K : Set X) →
    B ≤ Subgroup.normalizer (J : Set X) →
    p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B →
    RCKClassicalModelID K B → Odd (Nat.card (Subgroup.center ↥K)) →
    IsComponentOf J (K ⊓ Subgroup.centralizer {d}) → Odd (Nat.card (Subgroup.center ↥J)) →
    GGSixRCKJRow .IIp J → K = J ∨ SLFourEmbed K J ∨ OmegaSixEmbed K J

@[expose] def RCKLemmaFIIpAt
    (t : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) (K J B : Subgroup X) (d : X),
    p.Prime → p ≠ 2 → IsElemAbelian p B → d ∈ B → B ≤ Subgroup.normalizer (K : Set X) →
    B ≤ Subgroup.normalizer (J : Set X) →
    p ^ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) ≤ Nat.card B →
    RCKClassicalModelIDAt t K B → Odd (Nat.card (Subgroup.center ↥K)) →
    IsComponentOf J (K ⊓ Subgroup.centralizer {d}) → Odd (Nat.card (Subgroup.center ↥J)) →
    GGSixRCKJRow .IIp J → K = J ∨ SLFourEmbed K J ∨ OmegaSixEmbed K J

end CFSG.StandardType.RCKC1
