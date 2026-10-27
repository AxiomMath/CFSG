module

public import CFSG.LocalAnalysis.StandardType.GGSporKF1F4At
public import CFSG.HardMathSupport.Dickson.BMRows.CensusM3
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BM2Census
public import CFSG.HardMathSupport.MathTwE6.MonsterThreeBComponents
import CFSG.LocalAnalysis.StandardType.GGSporKCommDataF
import CFSG.LocalAnalysis.StandardType.GGSporKProdComp
import CFSG.LocalAnalysis.StandardType.GGSporKCompConj
import CFSG.LocalAnalysis.StandardType.GGSporKF1F4Conj
import CFSG.Assembly.LargeEvenGLABridge
import CFSG.Sporadic.Th.Certificate
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeALocalBase
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabBThreeL1Orb
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMDownMGmat
public import CFSG.HardMathSupport.Foote.E27.OrbitF3
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Main
public import CFSG.HardMathSupport.Timmesfeld.Balance.DeltaLocal
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableT2
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreAssembly
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreDFour
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.PiGenOrthProved
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.TransvFinal
public import CFSG.HardMathSupport.Timmesfeld.Proving.OmegaMinusEightOrderThree
public import CFSG.HardMathSupport.Timmesfeld.Proving.OmegaPiGroup
public import CFSG.HardMathSupport.Timmesfeld.Proving.OmegaSmallPiGroup
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Main
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Final
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.TFA
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Kernel
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Main
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S5Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltThreeRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwo
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ScalarTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Survivor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ThreeStrong
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm47Statement
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOCoords
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightSwap
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOKlein
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusLevi
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoJ3
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoONan
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
public import CFSG.LocalAnalysis.GLTheoremA.S4.ModCore
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.RankThree.PartOne.Mult.Sec68
public import CFSG.RankThree.PartOne.S11d.OddOutPSL2
public import CFSG.RankThree.PartOne.S11d.OutEsix
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.OrderCheckF
public import CFSG.RankThree.PartTwo.Sec4.Item47
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.Sporadic.Fi24
public import CFSG.Sporadic.Recognition.HNMultiplier
public import CFSG.Sporadic.Recognition.LyonsAmalgamModelYAut
public import CFSG.Sporadic.Recognition.LyonsFinalDist2
public import CFSG.Sporadic.Suz
public import Certificates.Certificate13622Base
public import Certificates.Data.TabCo1ThreeE
import CFSG.Assembly.OpenBridges

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint
open CFSG.Monster.Generated CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.B.Pinned
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF (QQ tbL tbL_conj QQ_le_tbL
  not_three_pow_21_dvd factorization_tbL le_zpowers_of_le_CQ)
open CFSG.HardMathSupport.MathTwE6.M3BIrr (tbL_le_normalizer_zpowers)
open CFSG.HardMathSupport.MathTwE6.M3BIrr
open CFSG.Open CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.BMRows
  CFSG.HardMathSupport.Dickson.Sec6.BM2 CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

private theorem gkm3_F1F4_tbw
    
    (hno : ∀ C : Subgroup Gmat,
      ¬ LargeEvenPComponent 3 (Subgroup.centralizer ({tbw} : Set Gmat)) C) :
    BMPCentralF1At 3 tbw ∧ BMPCentralF4At 3 tbw := by
  have hcardG : Nat.card Gmat = CFSG.Open.monsterOrder :=
    CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder
  have hirr := Certificates.certificate136207
  have hsyl := Certificates.certificate136201
  have hzo : orderOf tbw = 3 := tbCommData.orderOf_z
  have hLQ : tbL ≤ Subgroup.normalizer (QQ : Set Gmat) := fun b hb =>
    mem_normalizer_of_conj (tbL_conj b hb)
  have hL3 : (Nat.card Gmat).factorization 3 ≤ (Nat.card tbL).factorization 3 := by
    rw [factorization_tbL hsyl]
    by_contra h
    exact not_three_pow_21_dvd (hcardG ▸ (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
      Nat.card_pos.ne').2 (by omega))
  have hCQ := CFSG.HardMathSupport.MathTwE6.card_le_three_of_le_centralizer tbw tbw_pow_three QQ
    tbL hLQ hL3 (le_zpowers_of_le_CQ hsyl)
  have hz : bcomm (tbq ⟨1, by norm_num⟩) (tbq ⟨0, by norm_num⟩) = tbw := by
    have h := tbCommData.bcomm_q ⟨1, by norm_num⟩ ⟨0, by norm_num⟩
    rw [tbM_val, pow_one] at h
    exact h
  have hLz : ∀ l ∈ tbL, l * tbw * l⁻¹ ∈ Subgroup.zpowers tbw := fun l hl =>
    (Subgroup.mem_normalizer_iff.1 (tbL_le_normalizer_zpowers hl) tbw).1 (Subgroup.mem_zpowers _)
  have hB3 : OPrimeCoreTrivialAt 3 NativeSporadic.B :=
    BThreeFi23.oPrimeCoreTrivialAt_B_three
  have hM3 : OPrimeCoreTrivialAt 3 Gmat :=
    oPrimeCoreTrivialAt_gmat_of_uninverted Nat.prime_three (by norm_num)
      (uninvertedOPrimeTrivial_gmat_of_twoAPureKlein Nat.prime_three (by norm_num) hB3
        ThreeBNF.twoAPureKlein_three_Gmat)
  have hg1 : LargeEvenPPrimeCore 3 ↥(Subgroup.centralizer ({tbw} : Set Gmat)) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp (hM3 tbw hzo)
  exact bmPCentralF1At_F4At_of_commData Nat.prime_three (by norm_num) tbCommData hz tbL
    QQ_le_tbL hLQ hLz hL3 hCQ (m := (10 : ℕ).factorial) (by decide)
    (fun N hN hnorm => tbL_dichotomy hirr N hN hnorm) hg1 hno

private theorem gkm3_comp_transport {Q Q' : Type} [Group Q] [Finite Q] [Group Q'] (e : Q ≃* Q')
    {s : Q}
    (h : ∃ J : Subgroup Q, GLAPComponent 3 (Subgroup.centralizer ({s} : Set Q)) J) :
    ∃ J' : Subgroup Q', GLAPComponent 3 (Subgroup.centralizer ({e s} : Set Q')) J' := by
  obtain ⟨J, hJ⟩ := h
  refine ⟨J.map e.toMonoidHom, ?_⟩
  rw [← CFSG.Fischer.Classification.Recognition.map_centralizer_singleton e s]
  exact glaPComponent_map_equiv Nat.prime_three e hJ

private theorem gkm3_component_of_inverted
    {s : Gmat} (hs : orderOf s = 3)
    (hinv : InvertedByTwoA s) :
    ∃ J : Subgroup Gmat, LargeEvenPComponent 3 (Subgroup.centralizer ({s} : Set Gmat)) J := by
  have hE : MonsterExistenceStatement MGriess :=
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  haveI : Finite MGriess := hE.1.1
  let φ : Gmat ≃* MGriess :=
    (CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth).symm
  have hs' : orderOf (φ s) = 3 := by rwa [MulEquiv.orderOf_eq]
  have hSpM : CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.SporadicMultipliers :=
    sporadicMultipliers_of_census
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
  have hBr : SporadicBridges := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hA : CentThreeA MGriess := TabMThreeA.centThreeA_MGriess tabBThreeACard_thm
  have hC : CentThreeC MGriess := centThreeC_MGriess
  obtain ⟨α, hα2, hαc, hαk, i, hi, hsh⟩ :=
    invertedByTwoA_data_twoA hE Nat.prime_three (by norm_num) hs' (hinv.map φ)
  have hi34 : i = 3 ∨ i = 4 := by
    clear hsh
    revert i
    decide
  have h1 : ∃ J : Subgroup MGriess,
      GLAPComponent 3 (Subgroup.centralizer ({φ s} : Set MGriess)) J := by
    rcases hi34 with rfl | rfl
    · obtain ⟨hq, ⟨e⟩⟩ := hA (φ s) α hs' hα2 hαc hαk hsh
      have eS : ↥(Subgroup.centralizer ({φ s} : Set MGriess)) ⧸
          Subgroup.center ↥(Subgroup.centralizer ({φ s} : Set MGriess)) ≃*
          (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group := e.trans (hBr .Fi24Prime).some
      have hZ := card_center_dvd_multiplier hSpM hq .Fi24Prime eS
      obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.card ↥(Subgroup.center ↥(Subgroup.centralizer
          ({φ s} : Set MGriess))) = 3 ^ n := by
        rcases (Nat.dvd_prime Nat.prime_three).1 hZ with h | h
        · exact ⟨0, by simpa using h⟩
        · exact ⟨1, by simpa using h⟩
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact bmPComponent_of_quasisimple_centralizer Nat.prime_three hs' hq (IsPGroup.of_card hn)
    · obtain ⟨e⟩ := hsh
      have hbound := hC (φ s) α hs' hα2 hαc hαk ⟨e⟩
      set H : Subgroup MGriess := Subgroup.centralizer ({α} : Set MGriess) ⊓
        Subgroup.centralizer ({φ s} : Set MGriess) with hH
      have hcard : Nat.card ↥H = 90745943887872000 := by
        rw [Nat.card_congr e.toEquiv]
        exact CFSG.RankThree.PartOne.CTP.card_Th
      have hsimple : IsSimpleGroup ↥H :=
        @MulEquiv.isSimpleGroup ↥H _ NativeSporadic.Th Units.instGroup
          (CFSG.Sporadic.Th.Kernel.isSimpleGroup_Th CFSG.Sporadic.Th.th_kernel_facts) e
      have hnab : ∃ a b : ↥H, a * b ≠ b * a := by
        by_contra hcon
        push Not at hcon
        letI : CommGroup ↥H := { (inferInstance : Group ↥H) with mul_comm := hcon }
        have hpr := IsSimpleGroup.prime_card (α := ↥H)
        rw [hcard] at hpr
        norm_num at hpr
      exact bmPComponent_of_inverted_prod Nat.prime_three (by norm_num) hs' hαk inf_le_left
        inf_le_right hsimple hnab (by rw [hcard]; norm_num) (by rw [hcard]; exact hbound)
  have h2 := gkm3_comp_transport φ.symm h1
  rw [MulEquiv.symm_apply_apply] at h2
  obtain ⟨J, hJ⟩ := h2
  exact ⟨J, (CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent 3 _ _).2 hJ⟩

theorem ggSporK_bmPCentralF1F4_gmat_three
    : BMPCentralF1 3 Gmat ∧ BMPCentralF4 3 Gmat := by
  have hzo : orderOf tbw = 3 := tbCommData.orderOf_z
  have key : ∀ s : Gmat, orderOf s = 3 →
      (∀ C : Subgroup Gmat, ¬ LargeEvenPComponent 3 (Subgroup.centralizer ({s} : Set Gmat)) C) →
      BMPCentralF1At 3 s ∧ BMPCentralF4At 3 s := by
    intro s hs hno
    by_cases hinv : InvertedByTwoA s
    · obtain ⟨J, hJ⟩ := gkm3_component_of_inverted hs hinv
      exact (hno J hJ).elim
    · obtain ⟨c, hc⟩ := isConj_iff.1 (m3bClass_holds s hs hinv)
      have hc' : c * s * c⁻¹ = tbw ^ 1 := by rw [pow_one]; exact hc
      have hno' : ∀ C : Subgroup Gmat,
          ¬ LargeEvenPComponent 3 (Subgroup.centralizer ({tbw} : Set Gmat)) C := by
        intro C hC
        obtain ⟨J, hJ⟩ := bmPComponent_of_conj_pow Nat.prime_three hzo (by norm_num) hc' ⟨C, hC⟩
        exact hno J hJ
      exact bmPCentralF1At_F4At_of_conj_pow Nat.prime_three hzo (by norm_num) hc'
        (gkm3_F1F4_tbw hno')
  exact ⟨fun s hs hno => (key s hs hno).1, fun s hs hno => (key s hs hno).2⟩

end CFSG.StandardType.SporadicShape
