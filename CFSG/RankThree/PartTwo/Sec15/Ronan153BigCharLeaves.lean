module

public import CFSG.RankThree.PartTwo.Sec15.F153U33
public import CFSG.RankThree.PartTwo.Sec15.F153L3KOut
public import CFSG.RankThree.PartTwo.Sec15.F153L3KCent
public import CFSG.RankThree.PartTwo.Sec15.F153A10KHolds
import CFSG.RankThree.PartTwo.Sec16.Item163StepsAltProofTools
public import CFSG.RankThree.PartTwo.Sec14.Item143Proof
public import CFSG.RankThree.PartTwo.Sec15.F153L3C2Core
public import CFSG.RankThree.PartTwo.Sec15.F153L3C2HJ
public import CFSG.RankThree.PartTwo.Sec15.F153L3C2Inn
public import CFSG.RankThree.PartTwo.Sec15.F153L3C2Order

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan153Big

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15
open CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.Assembly.RankThreeEven (projSU)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}

theorem concl153Push_of_noFFModule_at (hR : Sec15R G A c L) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) (hF : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y)
    {S : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2))
    (hno : ¬ CharNormal153 Y S) (hFF : FF153 Y S) (hSY : S ≤ Subgroup.normalizer (Y : Set G))
    {T : Type} [Group T] (hT : NoFFModule T)
    (e : (↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃* T) :
    Concl153Push A Y S := by
  exfalso
  have hh := hR.toSec14Std
  have hY3 : Y = oPrimeResidualOf 3 Y := hY.prop.1.2.1
  have hYq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.prop.1.2.2.2
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hO2 : CFSG.Open.pCoreOf 2 Y ≠ ⊥ := hY.prop.2.2
  have hKP : CFSG.Open.IsKProper G := hh.toTheoremFourHyp.kProper
  have hKH : CFSG.Open.IsKGroup ↥(Y ⊔ S) :=
    hKP.isKGroup (Y ⊔ S) (F153.sup_ne_top_of_pCoreOf_ne_bot hh.toTheoremFourHyp hSY hO2)
  exact F153.leaf_false_of_noFFModule hKH hF hY3 hYq hS2 hSY hFF hno hT e

theorem exists_hyp315_of_listed_at (h149 : Sec16.Item149S14) (hR : Sec15R G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hF : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y) {S : Subgroup G}
    (hS : S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2))
    (hSY : S ≤ Subgroup.normalizer (Y : Set G)) (hT : Listed315 (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hA' : InvA315 (Y ⊔ S) S) :
    ∃ H : Subgroup G, Y ⊔ S ≤ H ∧ H ≤ n155 A Y ∧
      (((oResidual 2 ↥H).map H.subtype).subgroupOf (n155 A Y)).IsSubnormal ∧ Hyp315 H S := by
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hY3 : Y = oPrimeResidualOf 3 Y := hY.prop.1.2.1
  obtain ⟨-, hYX, hXN, -⟩ := facts153 hR.toSec14Std (h149 G A c L hR.toSec14Std) hY
  refine ⟨Y ⊔ S, le_rfl, sup_le (hYX.trans Subgroup.le_normalizer) hS.prop.1.2, ?_, ?_⟩
  · rw [Push153.oResidual_sup_eq hS2 hSY hY3, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr le_sup_left]
    exact Push153.isSubnormal_subgroupOf_normalizer hYX hXN
  · obtain ⟨e⟩ := Push153.nonempty_oResidual_quotient_equiv hS2 hSY hY3
    exact ⟨le_sup_right, Push153.generalizedFitting_sup_eq hF hS2 hSY,
      Push153.listed315_of_mulEquiv e hT, hA'⟩

open CFSG.HardMathSupport.Cooperstein.Proving (noIrrFFOffender_J2) in
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic (noIrrFFOffender_transfer) in
theorem concl153Push_of_j2_at
    (hR : Sec15R G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hF : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y) {S : Subgroup G}
    (hS : S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2)) (hno : ¬ CharNormal153 Y S)
    (hFF : FF153 Y S) (hSY : S ≤ Subgroup.normalizer (Y : Set G))
    (hJ : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    Concl153Push A Y S := by
  obtain ⟨e⟩ := hJ
  have hYq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.prop.1.2.2.2
  obtain ⟨e'⟩ :=
    F153.nonempty_centerQuotient_equiv_of_simple hYq CFSG.Sporadic.J2.isSimpleGroup_J2 e
  have hirr : NoIrrFFOffender CFSG.Blueprint.NativeSporadic.J2 :=
    noIrrFFOffender_transfer noIrrFFOffender_J2
      ⟨(CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv.some).symm⟩
  exact concl153Push_of_noFFModule_at hR hY hF hS hno hFF hSY
    (noFFModule_of_noIrrFFOffender hirr) e'

open CFSG.HardMathSupport.Cooperstein.Proving (noIrrFFOffender_M22) in
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic (noIrrFFOffender_transfer) in
theorem concl153Push_of_m22_at
    (hR : Sec15R G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hF : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y) {S : Subgroup G}
    (hS : S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2)) (hno : ¬ CharNormal153 Y S)
    (hFF : FF153 Y S) (hSY : S ≤ Subgroup.normalizer (Y : Set G))
    (hT : IsM22Type153 (↥Y ⧸ CFSG.pCore 2 ↥Y)) : Concl153Push A Y S := by
  have hYq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.prop.1.2.2.2
  have hirr : NoIrrFFOffender CFSG.Blueprint.NativeSporadic.M22 :=
    noIrrFFOffender_transfer noIrrFFOffender_M22
      ⟨(CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv.some).symm⟩
  have hNo := noFFModule_of_noIrrFFOffender hirr
  rcases hT with hT | hT
  · obtain ⟨e⟩ := hT
    obtain ⟨e'⟩ := F153.nonempty_centerQuotient_equiv_of_simple hYq
      (CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2) e
    exact concl153Push_of_noFFModule_at hR hY hF hS hno hFF hSY hNo e'
  · obtain ⟨-, ⟨e⟩⟩ := hT
    exact concl153Push_of_noFFModule_at hR hY hF hS hno hFF hSY hNo e

theorem concl153Push_of_rest_at
    (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8) (hR : Sec15R G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hF : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y) {S : Subgroup G}
    (hS : S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2)) (hno : ¬ CharNormal153 Y S)
    (hFF : FF153 Y S) (hSY : S ≤ Subgroup.normalizer (Y : Set G))
    (hnL : ¬ Listed315 (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hJ : IsEmpty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hL3 : ¬ IsL3Type153 (↥Y ⧸ CFSG.pCore 2 ↥Y)) (hM22 : ¬ IsM22Type153 (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hM12 : IsEmpty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.M12))
    (hA10 : IsEmpty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10))) :
    Concl153Push A Y S := by
  rcases F153.type153_of_item148R h148 h134 h48 hR hY with
    h | ⟨⟨φ⟩⟩ | h | h | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | hON
  · exact (hnL h).elim
  · exact (hJ.false φ).elim
  · exact (hL3 h).elim
  · exact (hM22 h).elim
  · exact (hM12.false φ).elim
  · exact (hA10.false φ).elim
  · obtain ⟨-, ⟨e⟩⟩ := hON
    exact concl153Push_of_noFFModule_at hR hY hF hS hno hFF hSY
      (noFFModule_of_noIrrFFOffender FFSporadic.noIrrFFOffender_ONan_native) e

theorem concl153Push_of_l3Char2_at
    (h134 : Item134) (h48 : Sec4.Item4_8) (h148HJ : Item148HJS14) (hR : Sec15R G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hF : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y) {S : Subgroup G}
    (hS : S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2)) (hno : ¬ CharNormal153 Y S)
    (hFF : FF153 Y S) (hSY : S ≤ Subgroup.normalizer (Y : Set G)) {f : ℕ} (hf : 1 ≤ f)
    (hε : IsLThreeEpsAt ((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) 2 f) :
    Concl153Push A Y S := by
  exfalso
  by_cases hHJ : AllPointsHJ A
  · exact F153L3C2.false_of_hj_stage h134 h48 h148HJ F153L3C2.kL3Char2NotList148_holds hR hHJ
      (scriptY0Star_subset A (lB A) hY) hf hε
  · have hh := hR.toSec14Std
    have hLB : ∀ B, IsHyperplane A B → lB A B = ⊥ := fun B hB =>
      lB_eq_bot_of_not_allPointsHJ' h134 h48 hh hHJ hB
    have hY3 : Y = oPrimeResidualOf 3 Y := hY.prop.1.2.1
    have hYq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.prop.1.2.2.2
    have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
    have hO2 : CFSG.Open.pCoreOf 2 Y ≠ ⊥ := hY.prop.2.2
    have hKP : CFSG.Open.IsKProper G := hh.toTheoremFourHyp.kProper
    have hKH : CFSG.Open.IsKGroup ↥(Y ⊔ S) :=
      hKP.isKGroup (Y ⊔ S) (F153.sup_ne_top_of_pCoreOf_ne_bot hh.toTheoremFourHyp hSY hO2)
    have hInn := F153L3C2.inner_trivial_153 F153L3K.kFactL3CentOdd_holds hf hh.isE27 hLB
      hS.prop.1.1 hS2 hY.prop.1.1.2 hSY hYq hε
    exact F153L3C2.leaf_false_of_noOuterFFOffender hKH hF hY3 hYq hS2 hSY hFF hno hInn
      (F153L3K.kFactL3NoOuterOffender_holds _ f hf hε) (MulEquiv.refl _)

theorem concl153Push_of_l3_at
    (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8) (h148HJ : Item148HJS14)
    (hR : Sec15R G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hF : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y) {S : Subgroup G}
    (hS : S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2)) (hno : ¬ CharNormal153 Y S)
    (hFF : FF153 Y S) (hSY : S ≤ Subgroup.normalizer (Y : Set G))
    (hT : IsL3Type153 (↥Y ⧸ CFSG.pCore 2 ↥Y)) : Concl153Push A Y S := by
  have hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.prop.1.2.2.2
  obtain ⟨p, n, hp, hn, hε⟩ := F153.exists_isLThreeEpsAt_quot_of_isL3Type153 hq hT
  by_cases hp2 : p = 2
  · subst hp2
    exact concl153Push_of_l3Char2_at h134 h48 h148HJ hR hY hF hS hno hFF hSY hn hε
  · by_cases hU : p = 3 ∧ n = 1 ∧ Nonempty
        (((↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) ≃* projSU 3 p n)
    · obtain ⟨rfl, rfl, hU'⟩ := hU
      exact F153.step153PushU33R_of_inputs h148 h134 h48 G A c L hR Y hY S hS hno hFF hSY hU'
    · exact concl153Push_of_noFFModule_at hR hY hF hS hno hFF hSY
        (F153.noFFModule_of_isLThreeEpsAt_odd hp2 hn hU hε) (MulEquiv.refl _)

theorem concl153Push_of_a10_at (hR : Sec15R G A c L) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) (hF : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y)
    {S : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2))
    (hno : ¬ CharNormal153 Y S) (hFF : FF153 Y S) (hSY : S ≤ Subgroup.normalizer (Y : Set G))
    (hA : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10))) :
    Concl153Push A Y S := by
  obtain ⟨φA⟩ := hA
  exfalso
  have hh := hR.toSec14Std
  have hY3 : Y = CFSG.GH74.GLS.oPrimeResidualOf 3 Y := hY.prop.1.2.1
  have hYq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.prop.1.2.2.2
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hO2 : CFSG.Open.pCoreOf 2 Y ≠ ⊥ := hY.prop.2.2
  have hKP : CFSG.Open.IsKProper G := hh.toTheoremFourHyp.kProper
  have hKH : CFSG.Open.IsKGroup ↥(Y ⊔ S) :=
    hKP.isKGroup (Y ⊔ S) (F153.sup_ne_top_of_pCoreOf_ne_bot hh.toTheoremFourHyp hSY hO2)
  have hD := hR.toSec13Data
  have hFE : CFSG.RankThree.LocalRank.partTwoF G = CFSG.RankThree.LocalRank.partTwoE G :=
    (hD.toTheoremFourHyp.partTwoF_eq_partTwoE hD.partTwoS_eq).1
  have hmax : ∀ E ∈ CFSG.RankThree.LocalRank.partTwoE G, ∀ B : Subgroup G,
      CFSG.Assembly.IsElemAbelian 3 B → E ≤ B → B = E :=
    fun E hE B hB hEB => (hFE ▸ hE : E ∈ CFSG.RankThree.LocalRank.partTwoF G).2.1 B hB hEB
  have hAN : A ≤ Subgroup.normalizer (Y : Set G) := hY.prop.1.1.2
  have hAY : A ≤ Y := Sec16.Step163Alt.le_of_alternating_ten hmax hD.isElemAbelian hAN hO2 φA
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
  exact F153.leaf_false_of_a10 hKH hF hY3 hYq hS2 hSY hFF hno φA hAY hD.card_eq
    (fun x hx y hy => congrArg Subtype.val (hD.isElemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    (fun x hx => hD.isElemAbelian.2 x hx) hAS F153A10K.a10NoV4Offender_holds

end CFSG.RankThree.PartTwo.Sec15.Ronan153Big
