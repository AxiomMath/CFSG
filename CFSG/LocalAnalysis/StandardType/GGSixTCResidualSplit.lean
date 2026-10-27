module

public import CFSG.LocalAnalysis.StandardType.GGSixKnownRemainingBridge

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def GGSixTCResidual {X : Type} [Group X] (p : ℕ) (L J : Subgroup X) (f : ℕ) : Prop :=
  p = 3 ∧ f = 1 ∧ LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 6 2 1 ∧
    LieModel (↥J ⧸ Subgroup.center ↥J) .PSL 2 2 3

section KnownLie

@[expose] def GGSixFieldExtTableCTwistedE6Res : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU .twistedE6 n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .twistedE6 n f).D .twistedE6 n f ψ →
    Subgroup.centralizer (D : Set G) ≤ ggM p B x L D J →
    Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) →
    (∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d})) →
    (∀ d ∈ D, d ≠ 1 → Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d)))) →
    ¬ GGSixLSevenA3Case J → ¬ GGSixLSevenE6Case p L J .twistedE6 f →
    GGSixLSevenFieldExtCase J .twistedE6 f →
      GGSixTCResidual p L J f ∧ Nat.card B = 3 ^ 4 ∧
        ∀ R : Subgroup G, IsPGroup 2 R → R ≤ ggG0 p B x L D J →
          B ≤ Subgroup.normalizer (R : Set G) → R = ⊥

@[expose] def GGSixFieldExtTableCRemainingRes : Prop :=
  GGSixFieldExtTableCAt .PSL ∧ GGSixFieldExtTableCAt .PSU ∧ GGSixFieldExtTableCAt .PSp ∧
    GGSixFieldExtTableCAt .POmegaPlus ∧ GGSixFieldExtTableCAt .POmegaMinus ∧
    GGSixFieldExtTableCAt .F4 ∧ GGSixFieldExtTableCAt .E6 ∧ GGSixFieldExtTableCAt .E7 ∧
    GGSixFieldExtTableCAt .E8 ∧ GGSixFieldExtTableCTwistedE6Res

@[expose] def GGSixTCResidualExcluded : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU .twistedE6 n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .twistedE6 n f).D .twistedE6 n f ψ →
    Subgroup.centralizer (D : Set G) ≤ ggM p B x L D J →
    Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) →
    (∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d})) →
    (∀ d ∈ D, d ≠ 1 → Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d)))) →
    ¬ GGSixLSevenA3Case J → ¬ GGSixLSevenE6Case p L J .twistedE6 f →
    GGSixLSevenFieldExtCase J .twistedE6 f → GGSixTCResidual p L J f → Nat.card B = 3 ^ 4 →
    (∀ R : Subgroup G, IsPGroup 2 R → R ≤ ggG0 p B x L D J →
      B ≤ Subgroup.normalizer (R : Set G) → R = ⊥) → False

theorem ggSixFieldExtTableCRemaining_of_res (h : GGSixFieldExtTableCRemainingRes)
    (hR : GGSixTCResidualExcluded) : GGSixFieldExtTableCRemaining := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_⟩
  intro G _ _ p B Bs x L D J n f ψ hc hD hodd hcomp hz hA3 hE6 hF
  obtain ⟨hres, hB4, hR2⟩ := h10 G p B Bs x L D J n f ψ hc hD hodd hcomp hz hA3 hE6 hF
  exact (hR G p B Bs x L D J n f ψ hc hD hodd hcomp hz hA3 hE6 hF hres hB4 hR2).elim

theorem ggSixFieldExtTableCInput_of_res (h : GGSixFieldExtTableCRemainingRes)
    (hR : GGSixTCResidualExcluded) : GGSixFieldExtTableCInput :=
  ggSixFieldExtTableCInput_of_remaining (ggSixFieldExtTableCRemaining_of_res h hR)

end KnownLie

end CFSG.StandardType

end
