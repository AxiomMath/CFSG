module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeFacts
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Config

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

@[expose] def L34GFResidue (k : Sec7Core4 G) : Prop :=
  Gls3StronglyThreeEmbeddedPlus → CFSG.AGLEmbedding.KFactReeInvolution → StronglyEmbeddedThree →
  k.p = 3 → 4 ≤ CFSG.Open.pRank k.p k.M →
  ∀ Y ∈ calC k.M, ∀ X : Subgroup G, X ≤ Y → ∀ q : ℕ, q.Prime → 5 ≤ q → Nat.card X = q →
    CFSG.Open.pRank q k.M ≤ 3 → (F08.Thin8 Y ∨ ∃ n : ℕ, IsSU3 (Bar2 Y) n ∧ q ∣ 2 ^ n - 1) →
    Sec7Core4.Config k (normalizer (X : Set G)) →
    ∀ B₁ : Subgroup G, B₁ ≤ k.M → IsElemAbelian k.p B₁ → Nat.card B₁ = k.p ^ 2 →
      B₁ ≤ centralizer (X : Set G) →
      (∀ b ∈ B₁, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 k.M) →
    ∀ t : G, t ∈ Y ⊓ normalizer (X : Set G) → orderOf t = 2 → (∀ b ∈ B₁, t * b = b * t) →
    IsoLie ↥(CFSG.generalizedFitting (↥(normalizer (X : Set G)) ⧸
        CFSG.pPrimeCore k.p ↥(normalizer (X : Set G))))
      (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩) → False

@[expose] def L34GFResidueAt (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) : Prop :=
  ∀ (hp : 3 ∈ uniqueFourSigma S.M) (hsp : IsStronglyPEmbedded 3 S.M),
    L34GFResidue (Sec7Core4.ofUnique hS hU S.M S.maxLocal 3 hp hsp)

end CFSG.LocalAnalysis.UniquenessCase.UC22
