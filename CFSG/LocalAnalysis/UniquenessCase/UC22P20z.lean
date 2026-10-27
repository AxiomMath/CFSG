module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

@[expose] def uc22pwCartanRankOne : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X → ∀ n : ℕ, 2 < n →
    (IsSz X n ∨ IsL2 X n ∨ IsSU3 X n) →
    ∀ (U : Sylow 2 X) (P : Type) [Group P], IsPGroup 2 P → ∀ ψ : P →* MulAut X,
      (∀ (g : P) (x : X), x ∈ (U : Subgroup X) ↔ ψ g x ∈ (U : Subgroup X)) →
      ∀ e m' : ℕ, Odd m' → n = 2 ^ e * m' →
      ∃ E : Subgroup X, E ≤ normalizer ((U : Subgroup X) : Set X) ∧ IsCyclic E ∧
        Squarefree (Nat.card E) ∧ Odd (Nat.card E) ∧ piSet E = etaSet n ∧
        (∀ (g : P), ∀ x ∈ E, ψ g x ∈ E ⊔ (U : Subgroup X)) ∧
        (∀ (g : P), ∀ x ∈ oPi {p | p.Prime ∧ p ∣ 2 ^ m' - 1} E, ψ g x * x⁻¹ ∈ (U : Subgroup X)) ∧
        ∃ w : X, w ^ 2 = 1 ∧ (∀ x ∈ E, w * x * w⁻¹ = x⁻¹) ∧
          normalizer ((U : Subgroup X) : Set X) ⊔ Subgroup.zpowers w = ⊤

@[expose] def uc22pwCartanGraph : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X → ∀ n : ℕ, 2 < n →
    (IsSL3 X n ∨ IsSp4 X n) →
    ∀ (U : Sylow 2 X) (P : Type) [Group P], IsPGroup 2 P → ∀ ψ : P →* MulAut X,
      (∀ (g : P) (x : X), x ∈ (U : Subgroup X) ↔ ψ g x ∈ (U : Subgroup X)) →
      ∀ e m' : ℕ, Odd m' → n = 2 ^ e * m' →
      ∃ E : Subgroup X, E ≤ normalizer ((U : Subgroup X) : Set X) ∧ IsMulCommutative E ∧
        Odd (Nat.card E) ∧
        (∀ p : ℕ, p.Prime → ∃ Q : Sylow p E, IsElemAbelian p (Q : Subgroup E) ∧ Nat.card Q ≤ p ^ 2) ∧
        piSet E = etaSet n ∧
        (∀ (g : P), ∀ x ∈ E, ψ g x ∈ E ⊔ (U : Subgroup X)) ∧
        (∀ (g : P), ∀ x ∈ oPi {p | p.Prime ∧ p ∣ 2 ^ m' - 1} E, ψ g x * x⁻¹ ∈ (U : Subgroup X)) ∧
        ∃ w : X, w ^ 2 = 1 ∧ (∀ x ∈ E, w * x * w⁻¹ = x⁻¹) ∧
          normalizer ((U : Subgroup X) : Set X) ⊔ Subgroup.zpowers w = ⊤

end CFSG.LocalAnalysis.UniquenessCase.UC22
