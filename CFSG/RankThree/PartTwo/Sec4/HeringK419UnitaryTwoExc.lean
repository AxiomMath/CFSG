module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryCfg
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofD4Odd
public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProof
public import CFSG.RankThree.PartOne.RF4.FinalKFacts

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace HeringUnitary

section Exc


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {a : G}
  {haN : a ∈ Subgroup.normalizer (L : Set G)} {m : ℕ}

theorem chevTwo_trialityD4 (hD4 : Sec21.TrialityD4EvenThreeRankTwo) (ha3 : a ^ 3 = 1)
    (c : UCfg L a haN m) {f : ℕ}
    (hX : Blueprint.ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L) .trialityD4 2 f) :
    InducesStdKind L a .field ∨ InducesStdKind L a .graphField := by
  obtain ⟨K, _, _, _, σ, hK, hσ, -, hf, -, ⟨e⟩⟩ :=
    Res417Seven.exists_graphFixedRootGroup_of_trialityD4 hX
  by_cases hout : InducesOuterTheta a L
  · exact Or.inr (InducesStdKind.triality f hf K hK σ hσ
      (KFacts.inducesKindTriality_graphField (L := L) hf hK hσ ha3 hout e))
  · exfalso
    have hin : thetaQuotMulAut L (compAction L ⟨a, haN⟩) ∈
        (MulAut.conj : _ →* MulAut (L ⧸ aschbacherSolvableCore 3 L)).range := by
      by_contra h
      exact hout ⟨haN, h⟩
    exact c.false_of_inner hin (MulEquiv.refl _) (hD4 _ f hX)

theorem chevTwo_twistedF4 (hF4 : Sec21.TwistedF4EvenThreeRankTwo) (ha3 : a ^ 3 = 1)
    (c : UCfg L a haN m) {f : ℕ}
    (hX : Blueprint.ReeTitsModel (L ⧸ aschbacherSolvableCore 3 L) .twistedF4 2 f) :
    InducesStdKind L a .field ∨ InducesStdKind L a .graphField := by
  obtain ⟨-, b, hb, -, K, _, _, hcharK, hK, ⟨e⟩⟩ := exists_mulEquiv_reeGamma hX
  by_cases hout : InducesOuterTheta a L
  · exact Or.inl (InducesStdKind.largeRee b hb K hK
      (KFacts.inducesKindLargeRee_field (L := L) hb hK
        (CFSG.RankThree.PartOne.RF4.largeReeOrderThreeFieldConj b K hK) ha3 hout e))
  · exfalso
    have hin : thetaQuotMulAut L (compAction L ⟨a, haN⟩) ∈
        (MulAut.conj : _ →* MulAut (L ⧸ aschbacherSolvableCore 3 L)).range := by
      by_contra h
      exact hout ⟨haN, h⟩
    exact c.false_of_inner hin (MulEquiv.refl _) (hF4 _ f hX)

end Exc

end HeringUnitary

end CFSG.RankThree.PartTwo.Sec4
