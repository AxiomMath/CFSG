module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Cover
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LieType.Multipliers.U42

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo


theorem rSchurOm6_holds : RSchurOm6 := by
  intro X _ _ hq hU4
  obtain ⟨-, ⟨eM⟩⟩ :=
    CFSG.LieType.Multipliers.U42.multiplier_PSU_four_two (X ⧸ Subgroup.center X) hU4
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier ⟨hq.1⟩
    (MulEquiv.refl (X ⧸ Subgroup.center X))
  rwa [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
