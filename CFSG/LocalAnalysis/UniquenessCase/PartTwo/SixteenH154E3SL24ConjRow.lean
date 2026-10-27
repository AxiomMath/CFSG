module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ConjRowA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24ConjRowB
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_sl24_conj_row {L : Subgroup (MulAut W)} (σ : MulAut W)
    (hrow : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ L ⊓ fixV L)) :
    s16h_H5RowSL2 (L.map (MulAut.conj σ).toMonoidHom)
      (commSub ⊤ (L.map (MulAut.conj σ).toMonoidHom))
      (commSub ⊤ (L.map (MulAut.conj σ).toMonoidHom) ⊓
        fixV (L.map (MulAut.conj σ).toMonoidHom)) 2 ∧
    2 < Nat.card ↥(commSub ⊤ (L.map (MulAut.conj σ).toMonoidHom) ⊓
      fixV (L.map (MulAut.conj σ).toMonoidHom)) := by
  have hrow' := s16h_H5RowSL2_conj L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2 σ hrow
  refine ⟨?_, ?_⟩
  · rw [s16h_commSub_fixV_conj L σ, s16h_commSub_conj L σ]
    exact hrow'
  · rw [s16h_commSub_fixV_conj L σ, Subgroup.card_map_of_injective σ.injective]
    exact hZ4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
