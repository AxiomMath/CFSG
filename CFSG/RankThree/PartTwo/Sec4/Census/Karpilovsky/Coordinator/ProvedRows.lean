module

public import CFSG.Sporadic.Recognition.McLMultiplierCert
public import CFSG.Sporadic.Recognition.HeMultiplierCert
public import CFSG.Sporadic.Recognition.M23MultiplierCert
public import CFSG.Sporadic.Recognition.RuMultiplier
public import CFSG.LocalAnalysis.SteinbergCCHSMultiplier
public import CFSG.Quasithin.Background.SmithB45HM22Cover
public import Certificates.Certificate15024
public import Certificates.Certificate15025
public import Certificates.Certificate15026
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.Blueprint CFSG.RankThree.PerfectCover

theorem card_hopfMultiplier_eq_card_griessHopfMultiplier (S : Type) [Group S] :
    Nat.card (hopfMultiplier S) = Nat.card (CFSG.Open.griessHopfMultiplier S) :=
  (Nat.card_congr (hopfMultiplierEquivGriess S).toEquiv).symm

theorem nativeRow_McL :
    Nat.card (hopfMultiplier (NativeSporadic.Carrier .McL)) = sporadicMultiplierOrder .McL :=
  (card_hopfMultiplier_eq_card_griessHopfMultiplier _).trans
    CFSG.Sporadic.Recognition.McLMultiplier.card_griessHopfMultiplier_McL_of_certificate

theorem nativeRow_He :
    Nat.card (hopfMultiplier (NativeSporadic.Carrier .He)) = sporadicMultiplierOrder .He :=
  (card_hopfMultiplier_eq_card_griessHopfMultiplier _).trans
    CFSG.Sporadic.Recognition.HeMultiplier.card_griessHopfMultiplier_He_of_certificate

theorem nativeRow_M23 :
    Nat.card (hopfMultiplier (NativeSporadic.Carrier .M23)) = sporadicMultiplierOrder .M23 :=
  (card_hopfMultiplier_eq_card_griessHopfMultiplier _).trans
    CFSG.Sporadic.Recognition.M23Multiplier.card_griessHopfMultiplier_M23_of_certificate

theorem nativeRow_Ru :
    Nat.card (hopfMultiplier (NativeSporadic.Carrier .Ru)) = sporadicMultiplierOrder .Ru :=
  (card_hopfMultiplier_eq_card_griessHopfMultiplier _).trans
    (CFSG.Sporadic.Recognition.RuMultiplier.card_griessHopfMultiplier_Ru
      Certificates.certificate15024 Certificates.certificate15025
      Certificates.certificate15026)

theorem nativeRow_HS :
    Nat.card (hopfMultiplier (NativeSporadic.Carrier .HS)) = sporadicMultiplierOrder .HS :=
  CFSG.LocalAnalysis.HigmanSimsCover.card_hopfMultiplier

theorem nativeRow_M22 :
    Nat.card (hopfMultiplier (NativeSporadic.Carrier .M22)) = sporadicMultiplierOrder .M22 := by
  have e := CFSG.LieType.Multipliers.hopfMultiplierEquivKer CFSG.Quasithin.HM22.isPresentation_m22
    (fun i => CFSG.LieType.Multipliers.mk_commWords_mem_commutator
      (CFSG.Sporadic.Recognition.M22Multiplier.m22Comm i))
    (CFSG.Sporadic.Recognition.M22Multiplier.lift_m22CommWord
      CFSG.Sporadic.Recognition.M22Multiplier.m22TabCheck_eq_true)
  exact (Nat.card_congr e.toEquiv).trans CFSG.Quasithin.HM22.m22Pi_ker.2

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
