module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9Core
public import Certificates.Certificate2111
public import Certificates.Certificate2112
public import Certificates.Certificate2118
public import Certificates.Certificate2223
public import Certificates.Certificate2224
public import Certificates.Certificate2225
public import Certificates.Certificate2240
public import Certificates.Certificate2241
public import Certificates.Certificate2242
public import Certificates.Certificate2243
public import Certificates.Certificate2244
public import Certificates.Certificate2245
public import Certificates.Certificate2284
public import Certificates.Certificate2285
public import Certificates.Certificate2288
public import Certificates.Certificate3168
public import Certificates.Certificate3170
public import Certificates.Certificate8057
public import Certificates.Certificate9118
public import Certificates.Certificate9125
public import Certificates.Certificate9126
public import Certificates.Certificate9210
public import Certificates.Certificate9216
public import Certificates.Certificate12635
public import Certificates.Certificate12636
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThree
import CFSG.Quasithin.Background.A318POutHe
import CFSG.RankThree.PartTwo.KFacts.K426RestMcL
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9CritJ2
import CFSG.RankThree.PartTwo.Sec4.Item47Native
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp
import CFSG.Sporadic.Bridge.HeSurj
import CFSG.Sporadic.HeldB.CertPBridge
import CFSG.Sporadic.Presentation.McLExact
import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Certificates.CosetTableCompactPresented
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47LThree
public import CFSG.RankThree.PartTwo.Sec4.Item47SpFour
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.Bridge.McLSurj
public import CFSG.Sporadic.He
public import CFSG.Sporadic.Presentation.HeExact
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate2225Base
import CFSG.GH74.GLS.Balance.SolvAPIDefs
import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
import CFSG.Open.SplitBNPair
import CFSG.Quasithin.Vol2.Ch10StatementsE
import CFSG.Quasithin.Vol2.Ch10StatementsInputs
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
import CFSG.RankThree.PartTwo.Sec11.Item119K
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
import CFSG.RankThree.PartTwo.Sec20.OneSteps
import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
import CFSG.RankThree.PartTwo.Sec4.Item41NarrowGriess
import CFSG.Walter.J1Props
import Certificates.Certificate8166

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG.RankThree.PartTwo.Sec4 (Spor)
open CFSG.RankThree.PartTwo.Sec4.RonanK429H
  (center_eq_bot_of_simple_nonab not_three_dvd_outer_of_le_two not_three_dvd_outer_of_mulEquiv)

theorem rowOfK9_mcl :
    RowOfK9 (Spor .McL) := by
  refine rowOfK9_spor CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv ?_
  intro S _ _ _ hna ⟨e⟩
  haveI : Finite (Blueprint.NativeSporadic.Carrier .McL) := Finite.of_equiv S e.toEquiv
  refine noCfgJ2_of_model (G' := Blueprint.NativeSporadic.McL) e
    (center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv e (not_three_dvd_outer_of_le_two Sec4.card_outer_McL))
    fun y hy => goodJ2_of_not_dvd_twentyFive ?_
  rcases KFacts.K426Rest.mclThreeCentralizerCard y hy with h | h <;> rw [h] <;> norm_num

theorem rowOfK9_he :
    RowOfK9 (Spor .He) := by
  refine rowOfK9_spor CFSG.Sporadic.Bridge.He.nonempty_mulEquiv ?_
  intro S _ _ _ hna ⟨e⟩
  refine noCfgJ2_of_subgroupModel (e.trans CFSG.Sporadic.HeldB.heEquivP)
    (center_eq_bot_of_simple_nonab hna)
    (CFSG.Quasithin.A318P.not_dvd_outer_He e Nat.prime_three (by norm_num)) fun x hx hx3 =>
      goodJ2_of_not_dvd_twentyFive ?_
  have hcard : Nat.card ↥(CFSG.Sporadic.Schreier.centralizerIn CFSG.Sporadic.HeldB.heP x) = 7560 ∨
      Nat.card ↥(CFSG.Sporadic.Schreier.centralizerIn CFSG.Sporadic.HeldB.heP x) = 504 := by
    rcases CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He.three_conj_cases hx hx3 with
      ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
    · left
      rw [CFSG.Sporadic.Schreier.centralizerIn_conj _ hc,
        Subgroup.card_map_of_injective (MulAut.conj c).injective]
      exact CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He.card_cent_A
    · right
      rw [CFSG.Sporadic.Schreier.centralizerIn_conj _ hc,
        Subgroup.card_map_of_injective (MulAut.conj c).injective]
      exact CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He.card_cent_B
  rw [inf_comm]
  rcases hcard with h | h <;> (change ¬ 25 ∣ Nat.card ↥(CFSG.Sporadic.Schreier.centralizerIn
    CFSG.Sporadic.HeldB.heP x); rw [h]; norm_num)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
