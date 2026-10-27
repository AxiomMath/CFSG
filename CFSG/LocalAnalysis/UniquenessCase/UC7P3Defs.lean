module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Input

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Yardstones.Mf4cdcdf2e013 (Setup4)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree (gammaCore)

@[expose] def StronglyEmbeddedThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → CFSG.pPrimeCore 3 X = ⊥ →
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) → ∀ N : Subgroup X, IsStronglyPEmbedded 3 N →
      CoverActsTriviallyOnSmall 3 ↥(CFSG.generalizedFitting X) ∧
        Nat.card ↥(CFSG.pPrimeCore 3 ↥N) ≤ 2 ∧
        CentralizerHasPElementOutside 3 N ∧
        IsSolvable ↥N

@[expose] def BadNoStrongThree : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → CFSG.pPrimeCore p X = ⊥ →
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) → ∀ N : Subgroup X, IsStronglyPEmbedded p N →
        CoverHasLargeTwoLocal ↥(CFSG.generalizedFitting X) →
        ∀ R : Sylow 3 ↥(CFSG.generalizedFitting X),
          gammaCore 3 1 ⊤ (R : Subgroup ↥(CFSG.generalizedFitting X)) = ⊤

variable {G : Type} [Group G] [Finite G]

@[expose] def C76ThreeN1 (S : Setup4 G) : Prop :=
  S.InMSigma → 3 ∈ CFSG.Open.uniqueFourBeta G → IsStronglyPEmbedded 3 S.M →
    Conclusion76 S.M 3

@[expose] def C76ThreeN2 (S : Setup4 G) : Prop :=
  S.InMSigma → 3 ∈ CFSG.Open.uniqueFourBeta G →
    ∀ p ∈ CFSG.Open.uniqueFourSigma S.M, 5 ≤ p → IsStronglyPEmbedded p S.M →
      Conclusion76 S.M p

@[expose] def C76Three (S : Setup4 G) : Prop :=
  S.InMSigma → 3 ∈ CFSG.Open.uniqueFourBeta G →
    ∀ p ∈ CFSG.Open.uniqueFourSigma S.M, IsStronglyPEmbedded p S.M → Conclusion76 S.M p

theorem C76Three_of_N1_N2 (S : Setup4 G) (h1 : C76ThreeN1 S) (h2 : C76ThreeN2 S) :
    C76Three S := by
  intro hσ h3 p hp hsp
  by_cases hp3 : p = 3
  · subst hp3
    exact h1 hσ h3 hsp
  · exact h2 hσ h3 p hp (Nat.Prime.five_le_of_ne_two_of_ne_three hp.1.1 hp.1.2.1 hp3) hsp

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
