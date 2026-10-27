module

public import CFSG.Quasithin.Background.G2A5Iso
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

theorem s16h_sl4_isAlt_of_rowSL2 {L : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hrow : s16h_H5RowSL2 L U Z 2) : IsAlt ↥L 5 := by
  obtain ⟨hSLn, -⟩ := hrow
  obtain ⟨K, hKf, hKfin, hKcard, ⟨eLK⟩⟩ := hSLn
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : Fintype K := Fintype.ofFinite K
  have hK4 : Nat.card K = 4 := by rw [hKcard]; norm_num
  have hK4' : Fintype.card K = 4 := by rwa [← Nat.card_eq_fintype_card]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (R := K) (p := 2) (f := 2) (by rw [hK4']; norm_num)
  have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 60 := by
    rw [← CFSG.Open.StatedAPI.card_statedSL 2 K, CFSG.Open.StatedAPI.card_statedSL_two K, hK4]
    norm_num
  obtain ⟨eAlt⟩ := CFSG.Quasithin.A5Model.sl2_four_equiv_alt5 K hK4 hcardSL
  exact ⟨(eLK.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm).trans
    eAlt⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
