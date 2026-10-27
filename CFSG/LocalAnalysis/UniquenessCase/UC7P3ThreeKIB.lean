module

public import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeBOC
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeOCSetup
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeOCSmall
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeOCRee
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeOCL34
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.LinTwo
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Unitary
import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.AGLEmbedding
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus Gls3ConclusionPlus gammaCore)
open CFSG.LocalAnalysis.ComponentInitial
  (unique_field_nine_projective_linear_alternating_six_isomorphism)

@[expose] def StronglyEmbeddedThreeKIB : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → CFSG.pPrimeCore 3 X = ⊥ →
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) → ∀ N : Subgroup X, IsStronglyPEmbedded 3 N →
      CoverActsTriviallyOnSmall 3 ↥(CFSG.generalizedFitting X)

set_option linter.unusedSectionVars false

theorem oc_of_gls3ConclusionPlus {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore 3 X = ⊥)
    (h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) {N : Subgroup X}
    (hN : IsStronglyPEmbedded 3 N)
    (hrow : ∀ P : Sylow 3 X, 2 ≤ CFSG.Open.pRank 3 (P : Subgroup X) →
      gammaCore 3 1 ⊤ (P : Subgroup X) < ⊤ →
        Gls3ConclusionPlus X (CFSG.generalizedFitting X) (P : Subgroup X)) :
    Nat.card ↥(CFSG.pPrimeCore 3 ↥N) ≤ 2 ∧ CentralizerHasPElementOutside 3 N := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hgood : SEFive.Good 3 N →
      Nat.card ↥(CFSG.pPrimeCore 3 ↥N) ≤ 2 ∧ CentralizerHasPElementOutside 3 N :=
    fun h => ⟨by rw [h.1, Subgroup.card_bot]; norm_num, h.2⟩
  obtain ⟨hKs, hKnab, hKn, hKC⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar Nat.prime_three hO hN
  set K := CFSG.generalizedFitting X
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKs
  have hK1 : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance
  obtain ⟨P, hPN, hPK, T, hT, -⟩ := exists_sylow_glbCore_ne_top_of_isStronglyPEmbedded hO hK1 hN
  have hrk : 2 ≤ CFSG.Open.pRank 3 (P : Subgroup X) := by
    rw [(CFSG.SectionRank.pRank_sylow P).1]
    exact h2
  have hΓX : gammaCore 3 1 ⊤ (P : Subgroup X) < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hN.1 (top_le_iff.1 ?_)
    rw [← h]
    exact CFSG.LocalAnalysis.UniquenessCase.UCK.gammaCore_le_of_isStronglyPEmbedded hN P.isPGroup'
      hPN
  obtain ⟨-, hmax, hrows⟩ := hrow P hrk hΓX
  have hQN : (P : Subgroup X) ⊓ K ≤ N := inf_le_left.trans hPN
  rcases hrows with ⟨q, hq3, ⟨hv, ⟨e⟩⟩, -⟩ | ⟨q, hq3, ⟨hv, ⟨e⟩⟩, -⟩ | ⟨m, hI, -⟩ |
      ⟨-, hidx, hQc, h9, hΓ, hD, -⟩ | ⟨⟨φ, -⟩, -⟩ |
      ⟨hI, hidx, -, -, h9, hΓ, S, hS, hQS, hsup, hQ8, -⟩ |
      ⟨-, hKt, hE, h9, hΓ, S, hS, hsup, h16, -, hC, -⟩
  ·
    obtain ⟨f⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex
      (show IsLinTwoIndex 3 q.exponent ⟨.A 1 q, hv⟩ from ⟨q, rfl, hq3, rfl⟩)
    exact hgood (SEFive.good_psl2GF (by norm_num) q.exponent_pos hO hN (e.trans f))
  ·
    exact hgood (SEFive.good_unitary (p := 3) (d := ⟨.twistedA 2 q, hv⟩) ⟨q, hq3, rfl⟩ hO hN e)
  ·
    exact hgood (good_of_isoLie_reeG2 hO hN hI)
  ·
    obtain ⟨hNK, hnorm⟩ := ThreeOC.inf_eq_and_le_normalizer hN P hPN hPK T hT hmax hΓ
    exact hgood (ThreeOC.good_l28Row hQN inf_le_right hnorm hNK hidx hQc h9 (hΓ ▸ hD))
  ·
    have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
    have hcard : Fintype.card (GaloisField 3 2) = 9 := by
      rw [Fintype.card_eq_nat_card, GaloisField.card 3 2 (by norm_num)]
      norm_num
    obtain ⟨f⟩ :=
      unique_field_nine_projective_linear_alternating_six_isomorphism (GaloisField 3 2) hcard
    exact hgood (SEFive.good_psl2GF (p := 3) (n := 2) (by norm_num) (by norm_num) hO hN
      (φ.trans f.symm))
  ·
    obtain ⟨hNK, hnorm⟩ := ThreeOC.inf_eq_and_le_normalizer hN P hPN hPK T hT hmax hΓ
    exact ThreeOC.oc_l34Row hKC hI hQN inf_le_right hnorm hNK hidx h9 (hS.trans hΓ.le) hQS
      (hsup.trans hΓ) hQ8
  ·
    obtain ⟨hNK, hnorm⟩ := ThreeOC.inf_eq_and_le_normalizer hN P hPN hPK T hT hmax hΓ
    exact hgood (ThreeOC.good_m11Row hQN hnorm hNK hKt hE h9 (hS.trans hΓ.le) (hsup.trans hΓ)
      h16 hC)

theorem oc_of_isStronglyPEmbedded_three (hG3 : Gls3StronglyThreeEmbeddedPlus) {X : Type}
    [Group X] [Finite X] (hX : CFSG.Open.IsKGroup X) (hO : CFSG.pPrimeCore 3 X = ⊥)
    (h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) {N : Subgroup X}
    (hN : IsStronglyPEmbedded 3 N) :
    Nat.card ↥(CFSG.pPrimeCore 3 ↥N) ≤ 2 ∧ CentralizerHasPElementOutside 3 N := by
  obtain ⟨hKs, hKnab, hKn, hKC⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar Nat.prime_three hO hN
  exact oc_of_gls3ConclusionPlus hO h2 hN fun P hP hΓ => hG3 X hX _ hKn hKs hKnab hKC P hP hΓ

theorem StronglyEmbeddedThreeBOC_of_KIB (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hKIB : StronglyEmbeddedThreeKIB) : StronglyEmbeddedThreeBOC :=
  fun X _ _ hX hO h2 N hN => ⟨hKIB X hX hO h2 N hN, oc_of_isStronglyPEmbedded_three hG3 hX hO h2 hN⟩

theorem StronglyEmbeddedThree_of_KIB (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hSch : KFactCatalogSchreier) (hKIB : StronglyEmbeddedThreeKIB) : StronglyEmbeddedThree :=
  StronglyEmbeddedThree_of_BOC hG3 hSch (StronglyEmbeddedThreeBOC_of_KIB hG3 hKIB)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
