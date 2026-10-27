module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Alt
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclCard
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
import CFSG.GH74.GLS.Stage2.Final.ModelOrd
import CFSG.LieType.CurtisTits.SpecialLinear
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCaseTwoCMSection
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatAlt
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactPiece
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s168e3_exists_tensor_of_isOmegaPlus_two {W : Type} [CommGroup W]
    {A L : Subgroup (MulAut W)} {t : MulAut W} (hW : Conc4_136W A t L)
    (hΩ : IsOmegaPlus ↥L 4 2) :
    ∃ K : Subgroup (MulAut W), IsComponentOf K A ∧ ∃ g ∈ A,
      K ≠ K.map (MulAut.conj g).toMonoidHom ∧ L = K ⊔ K.map (MulAut.conj g).toMonoidHom ∧
        UC22.IsL2 ↥K 2 ∧ NatTensor L (commSub ⊤ L) ⊥ 2 2 := by
  have hcard : Nat.card ↥L = 3600 :=
    (Om8Excl.card_isOmegaPlus_four (by norm_num) hΩ).trans (by norm_num)
  haveI : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  rcases hW.2.2 with h1 | ⟨K, hK, g, hg, hne, hL, hc⟩ | h3 | h4
  ·
    obtain ⟨p, hp, hLp, -⟩ := h1
    haveI : Fact p.Prime := ⟨hp⟩
    have hpG : IsPGroup p ↥(pCoreOf p A) :=
      (CFSG.pCore_isPGroup (p := p) (G := ↥A)).map A.subtype
    have hpL : IsPGroup p ↥L := hpG.to_le hLp
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hpL
    have h2dvd : 2 ∣ p ^ k := by rw [← hk, hcard]; norm_num
    have hp2 : p = 2 :=
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
        ((Nat.Prime.dvd_of_dvd_pow Nat.prime_two) h2dvd)).symm
    have h3dvd : 3 ∣ 2 ^ k := by
      have h' : 3 ∣ Nat.card ↥L := by rw [hcard]; norm_num
      rwa [hk, hp2] at h'
    exact absurd ((Nat.Prime.dvd_of_dvd_pow Nat.prime_three) h3dvd) (by norm_num)
  · rcases hc with ⟨-, hT⟩ | ⟨hK2, hT⟩ | ⟨-, hT⟩
    ·
      obtain ⟨F, _, _, hF, π, hπ⟩ := hT
      haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
      have hF2 : Nat.card F = 2 := by rw [hF]; norm_num
      have hdvd : Nat.card ↥L ∣ Nat.card (↥(StatedSL 3 F) × ↥(StatedSL 3 F)) :=
        Subgroup.card_dvd_of_surjective hπ.1
      rw [Nat.card_prod, CFSG.Open.StatedAPI.card_statedSL_three_of_card_eq_two hF2] at hdvd
      have h5 : 5 ∣ Nat.card ↥L := by rw [hcard]; norm_num
      have h5' : 5 ∣ 168 * 168 := h5.trans hdvd
      norm_num at h5'
    · exact ⟨K, by simpa using hK, g, hg, hne, hL, hK2, hT⟩
    ·
      obtain ⟨F, _, _, hF, π, hπ⟩ := hT
      haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
      have hF8 : Nat.card F = 8 := by rw [hF]; norm_num
      have hdvd : Nat.card ↥L ∣ Nat.card (↥(StatedSL 2 F) × ↥(StatedSL 2 F)) :=
        Subgroup.card_dvd_of_surjective hπ.1
      rw [Nat.card_prod, CFSG.Open.StatedAPI.card_statedSL_two F, hF8] at hdvd
      have h5 : 5 ∣ Nat.card ↥L := by rw [hcard]; norm_num
      have h5' : 5 ∣ (8 * (8 ^ 2 - 1)) * (8 * (8 ^ 2 - 1)) := h5.trans hdvd
      norm_num at h5'
  ·
    exact (C163.not_isQuasisimple_of_isOmegaPlus_four (by norm_num) hΩ h3.1.2.2).elim
  ·
    exact (C163.not_isQuasisimple_of_isOmegaPlus_four (by norm_num) hΩ h4.2.2.1.2.2).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
