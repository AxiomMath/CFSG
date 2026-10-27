module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150SporCore
public import Certificates.Certificate2022
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
public import Certificates.Certificate2120
public import Certificates.Certificate2121
public import Certificates.Certificate2122
public import Certificates.Certificate2123
public import Certificates.Certificate2125
public import Certificates.Certificate2127
public import Certificates.Certificate2211
public import Certificates.Certificate2212
public import Certificates.Certificate2213
public import Certificates.Certificate2214
public import Certificates.Certificate2215
public import Certificates.Certificate2216
public import Certificates.Certificate2217
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
public import Certificates.Certificate3171
public import Certificates.Certificate3172
public import Certificates.Certificate8139
public import Certificates.Certificate9114
public import Certificates.Certificate9127
public import Certificates.Certificate9129
public import Certificates.Certificate9208
public import Certificates.Certificate9217
public import Certificates.Certificate9218
public import Certificates.Certificate9590
public import Certificates.Certificate9702
public import Certificates.Certificate16041
public import Certificates.Certificate24945
public import Certificates.Certificate24946
import CFSG.GroupTheory.CentralizerSup
import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuThreeCent
import CFSG.RankThree.Native.ONThreeCentralizer
import CFSG.RankThree.Native.ONThreeFusion
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp
import CFSG.Sporadic.Bridge.HNSurj
import CFSG.Sporadic.Bridge.ONSurj
import CFSG.Sporadic.Bridge.RuSurj
import CFSG.Sporadic.HNSchreier.Faithful
import CFSG.Sporadic.HNSchreier.FullAut
import CFSG.Sporadic.HNSchreier.Intrinsic
import CFSG.Sporadic.Schreier.RuAutInner
import CFSG.Sporadic.Schreier.SteinbergBIONOuterTwo
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.RankThreeDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourGroupSpec
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.Native.ONSevenDefs
public import CFSG.RankThree.Native.ONSevenRestrict
public import CFSG.RankThree.Native.ONTripleNorm
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs
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
public import Certificates.Certificate2022Base
public import Certificates.Certificate2254Base
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

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

section Ru

open CFSG.EvenSporadicStandard.RuStd.S2 (ruThreeX0 exists_conj_ruThree card_centralizer_ruThreeX0)
open CFSG.Sporadic.RuSchreier (ruP ruEquivP card_outer_ruP)

private theorem k150s_goodFor_ruP {J : Type} [Group J] (hJ : K150sTgt J)
    (y : ruP)
    (hy : orderOf y = 3) : GoodFor J (Subgroup.centralizer ({y} : Set ruP)) := by
  obtain ⟨c, hc⟩ := exists_conj_ruThree y hy
  have h0 : GoodFor J (Subgroup.centralizer ({ruThreeX0} : Set ruP)) :=
    k150s_goodFor_of_not_dvd (hJ.not_dvd (by rw [card_centralizer_ruThreeX0]; norm_num)
      (by rw [card_centralizer_ruThreeX0]; norm_num))
  have h1 := k150s_goodFor_of_isConj (isConj_iff.mpr ⟨c, rfl⟩ :
    IsConj ruThreeX0 (c * ruThreeX0 * c⁻¹)) h0
  have hcent : Subgroup.centralizer ({y} : Set ruP) =
      Subgroup.centralizer ({c * ruThreeX0 * c⁻¹} : Set ruP) := by
    rw [← CFSG.centralizer_zpowers_eq_centralizer_singleton y, ← hc,
      CFSG.centralizer_zpowers_eq_centralizer_singleton]
  rw [hcent]
  exact h1

theorem k150s_ru {J : Type} [Group J] (hJ : K150sTgt J) :
    RowOfK150 J (Spor .Ru) := by
  refine k150s_row_of_native (s := .Ru) CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv ?_
  intro S _ _ hs hna ⟨e⟩
  have := hs
  let eP : S ≃* ruP := e.trans ruEquivP
  refine k150s_noCfg_of_model eP (RonanK429H.center_eq_bot_of_simple_nonab hna) ?_
    (k150s_goodFor_ruP hJ)
  rw [Nat.card_congr (equivalence eP).toEquiv, card_outer_ruP]
  norm_num

end Ru

section ON

open CFSG.RankThree.Native (onThree_fusion onThreeElt orderOf_onThreeElt
  card_centralizer_onThreeElt)

theorem k150s_goodFor_on {J : Type} [Group J] (hJ : K150sTgt J)
    (y : Blueprint.NativeSporadic.ON) (hy : orderOf y = 3) :
    GoodFor J (Subgroup.centralizer ({y} : Set Blueprint.NativeSporadic.ON)) := by
  obtain ⟨k, hk⟩ := onThree_fusion orderOf_onThreeElt hy
  refine k150s_goodFor_of_isConj (isConj_iff.mpr ⟨k, hk⟩) ?_
  exact k150s_goodFor_of_not_dvd (hJ.not_dvd (by rw [card_centralizer_onThreeElt]; norm_num)
    (by rw [card_centralizer_onThreeElt]; norm_num))

theorem k150s_on {J : Type} [Group J] (hJ : K150sTgt J) :
    RowOfK150 J (Spor .ONan) := by
  refine k150s_row_of_native (s := .ONan) CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv ?_
  intro S _ _ hs hna ⟨e⟩
  have := hs
  have hout : ¬ 3 ∣ Nat.card (Outer S) := fun h3 => by
    have h2 := h3.trans (CFSG.Sporadic.SteinbergBI.cti_on_outer_order_divides_two ⟨e⟩)
    norm_num at h2
  exact k150s_noCfg_of_model (G' := Blueprint.NativeSporadic.ON) e
    (RonanK429H.center_eq_bot_of_simple_nonab hna) hout (k150s_goodFor_on hJ)

end ON

section HN

open CFSG.Sporadic.HNSchreier (JH hnEquivJ card_outer_HN sJ L1J CJ_s1_structure commutator_CJ_s1
  iotaA iotaA_injective alt3 alt3_simple card_alt3
  ctuc_hn_intrinsic_three_class_and_alternating_localization)

private theorem k150s_goodFor_JH_three_A {J : Type} [Group J] (hJ : K150sTgt J) :
    GoodFor J (Subgroup.centralizer ({sJ 0} : Set JH)) := by
  have := hJ.simple.toNontrivial
  obtain ⟨hC, -, -⟩ := CJ_s1_structure
  have : IsSimpleGroup alt3 := alt3_simple
  have e : ↥(alt3.map iotaA) ≃* alt3 := (alt3.equivMapOfInjective iotaA iotaA_injective).symm
  have : IsSimpleGroup ↥(alt3.map iotaA) := MulEquiv.isSimpleGroup e
  refine k150s_goodFor_of_perfect_le_simple (E := alt3.map iotaA) ?_ inferInstance ?_ ?_
  · change alt3.map iotaA ≤ CFSG.Sporadic.HNSchreier.CJ (sJ 0)
    rw [hC]
    exact le_sup_right
  · intro P hPC hP
    have h1 := (Subgroup.isPerfect_iff.mp hP).ge
    exact h1.trans ((Subgroup.commutator_mono hPC hPC).trans commutator_CJ_s1.le)
  · rw [Nat.card_congr e.toEquiv, card_alt3]
    rcases hJ.card with hc | hc <;> rw [hc] <;> norm_num

private theorem k150s_goodFor_JH {J : Type} [Group J] (hJ : K150sTgt J)
    (y : JH) (hy : orderOf y = 3) :
    GoodFor J (Subgroup.centralizer ({y} : Set JH)) := by
  obtain ⟨h3, -, -, -, -, h29160, -⟩ :=
    ctuc_hn_intrinsic_three_class_and_alternating_localization
  rcases (h3 y).1 hy with h | h
  · exact k150s_goodFor_of_isConj h (k150s_goodFor_JH_three_A hJ)
  · refine k150s_goodFor_of_not_dvd (hJ.not_dvd ?_ ?_) <;> rw [h29160 y h] <;> norm_num

theorem k150s_hn {J : Type} [Group J] (hJ : K150sTgt J) :
    RowOfK150 J (Spor .HN) := by
  refine k150s_row_of_native (s := .HN) CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv ?_
  intro S _ _ hs hna ⟨e⟩
  have := hs
  have hnat : ∀ x : Blueprint.NativeSporadic.HN, orderOf x = 3 →
      GoodFor J (Subgroup.centralizer ({x} : Set Blueprint.NativeSporadic.HN)) := fun x hx =>
    @k150s_goodFor_of_mulEquiv_centralizer J _ Blueprint.NativeSporadic.HN ↥JH Units.instGroup
      (Subgroup.toGroup JH) hnEquivJ x
      (k150s_goodFor_JH hJ (hnEquivJ x) (by rw [MulEquiv.orderOf_eq]; exact hx))
  have hout : Nat.card (Outer (Blueprint.NativeSporadic.Carrier .HN)) = 2 := card_outer_HN
  refine k150s_noCfg_of_model (G' := Blueprint.NativeSporadic.Carrier .HN) e
    (RonanK429H.center_eq_bot_of_simple_nonab hna) ?_ hnat
  rw [Nat.card_congr (equivalence e).toEquiv, hout]
  norm_num

end HN

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150
