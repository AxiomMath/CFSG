module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9Core
public import Certificates.Certificate2096
public import Certificates.Certificate2097
public import Certificates.Certificate2098
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2103
public import Certificates.Certificate2104
public import Certificates.Certificate2107
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate2247
public import Certificates.Certificate2249
public import Certificates.Certificate2250
public import Certificates.Certificate2251
public import Certificates.Certificate2252
public import Certificates.Certificate2253
public import Certificates.Certificate2254
public import Certificates.Certificate2255
public import Certificates.Certificate2256
public import Certificates.Certificate2258
public import Certificates.Certificate2259
public import Certificates.Certificate2260
public import Certificates.Certificate3166
public import Certificates.Certificate3172
public import Certificates.Certificate9114
public import Certificates.Certificate9129
public import Certificates.Certificate9208
public import Certificates.Certificate9218
public import Certificates.Certificate16041
public import Certificates.Certificate24945
public import Certificates.Certificate24946
import CFSG.GroupTheory.CentralizerSup
import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeCent
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9CritJ2
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHCore
import CFSG.Sporadic.Bridge.HNSurj
import CFSG.Sporadic.Bridge.RuSurj
import CFSG.Sporadic.HNSchreier.Faithful
import CFSG.Sporadic.HNSchreier.FullAut
import CFSG.Sporadic.HNSchreier.Intrinsic
import CFSG.Sporadic.Schreier.RuAutInner
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
public import CFSG.Sporadic.Schreier.RuLOdd
public import CFSG.Sporadic.Schreier.RuZClass
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate2254Base
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
open CFSG.RankThree.PartTwo.Sec4.RonanK429H (center_eq_bot_of_simple_nonab)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

section Ru

open CFSG.EvenSporadicStandard.RuStd.S2 (ruThreeX0 exists_conj_ruThree card_centralizer_ruThreeX0)
open CFSG.Sporadic.RuSchreier (ruP ruEquivP card_outer_ruP)

private theorem goodJ2_ruP
    (y : ruP) (hy : orderOf y = 3) : GoodJ2 (Subgroup.centralizer ({y} : Set ruP)) := by
  obtain ⟨c, hc⟩ := exists_conj_ruThree y hy
  have h0 : GoodJ2 (Subgroup.centralizer ({ruThreeX0} : Set ruP)) :=
    goodJ2_of_not_dvd_twentyFive (by rw [card_centralizer_ruThreeX0]; norm_num)
  have h1 := GoodJ2.of_isConj (isConj_iff.mpr ⟨c, rfl⟩ :
    IsConj ruThreeX0 (c * ruThreeX0 * c⁻¹)) h0
  have hcent : Subgroup.centralizer ({y} : Set ruP) =
      Subgroup.centralizer ({c * ruThreeX0 * c⁻¹} : Set ruP) := by
    rw [← CFSG.centralizer_zpowers_eq_centralizer_singleton y, ← hc,
      CFSG.centralizer_zpowers_eq_centralizer_singleton]
  rw [hcent]
  exact h1

theorem rowOfK9_ru :
    RowOfK9 (Spor .Ru) := by
  refine rowOfK9_spor (s := .Ru) CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv ?_
  intro S _ _ hs hna ⟨e⟩
  haveI := hs
  let eP : S ≃* ruP := e.trans ruEquivP
  refine noCfgJ2_of_model eP (center_eq_bot_of_simple_nonab hna) ?_ goodJ2_ruP
  rw [Nat.card_congr (equivalence eP).toEquiv,
    card_outer_ruP]
  norm_num

end Ru

section HN

open CFSG.Sporadic.HNSchreier (JH hnEquivJ card_outer_HN
  ctuc_hn_intrinsic_three_class_and_alternating_localization)

private theorem goodJ2_JH
    (y : JH) (hy : orderOf y = 3) : GoodJ2 (Subgroup.centralizer ({y} : Set JH)) := by
  obtain ⟨h3, -, -, -, h544, h29160, -⟩ :=
    ctuc_hn_intrinsic_three_class_and_alternating_localization
  rcases (h3 y).1 hy with h | h
  · exact goodJ2_of_not_dvd_twentyFive (by rw [h544 y h]; norm_num)
  · exact goodJ2_of_not_dvd_twentyFive (by rw [h29160 y h]; norm_num)

theorem rowOfK9_hn :
    RowOfK9 (Spor .HN) := by
  refine rowOfK9_spor (s := .HN) CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv ?_
  intro S _ _ hs hna ⟨e⟩
  haveI := hs
  have hnat : ∀ x : Blueprint.NativeSporadic.HN, orderOf x = 3 →
      GoodJ2 (Subgroup.centralizer ({x} : Set Blueprint.NativeSporadic.HN)) := fun x hx =>
    @GoodJ2.of_mulEquiv_centralizer Blueprint.NativeSporadic.HN ↥JH Units.instGroup
      (Subgroup.toGroup JH) hnEquivJ x
      (goodJ2_JH (hnEquivJ x) (by rw [MulEquiv.orderOf_eq]; exact hx))
  have hout : Nat.card (Outer (Blueprint.NativeSporadic.Carrier .HN)) = 2 := card_outer_HN
  refine noCfgJ2_of_model (G' := Blueprint.NativeSporadic.Carrier .HN) e
    (center_eq_bot_of_simple_nonab hna) ?_ hnat
  rw [Nat.card_congr (equivalence e).toEquiv, hout]
  norm_num

end HN

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
