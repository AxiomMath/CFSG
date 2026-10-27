module

public import CFSG.RankThree.PartTwo.Sec16.Item166Proof
public import CFSG.RankThree.PartTwo.Sec16.Item166CtrKcdA5
public import CFSG.RankThree.PartTwo.Sec16.Item166CtrS6Push
public import CFSG.RankThree.PartTwo.Sec17.Item1712StepsProofClaims
public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofDefs
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof
import CFSG.RankThree.PartTwo.Sec16.Item166CtrPair
import CFSG.RankThree.PartTwo.Sec16.Item166CtrQ
import CFSG.RankThree.PartTwo.Sec16.Item166CtrS6
import CFSG.RankThree.PartTwo.Sec16.Item166CtrJ2Q
import CFSG.RankThree.PartTwo.Sec16.Item166CtrS5
public import CFSG.RankThree.PartTwo.Sec16.Item166CtrFac
public import CFSG.RankThree.PartTwo.Sec16.Item166CtrStar

public section

namespace CFSG.RankThree.PartTwo.Sec16.Ctr166

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

private theorem le_M_of_step13
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2))
    (h146 : Item146S14) (h149 : Item149S14) (hK : KFacts.KS166J2A5)
    (hRead : Sec15.Y4CoreReadR) (hMem : Sec15.Y4CoreMemR) (h1523 : Item1523R)
    (h155 : Item155R) (h143 : Ronan148Q.Item143QS14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets)
    (hKcd : Step166KcdA5) (hData : Step166A5Data)
    (hKd : Step166KCommD) {X J S C XC : Subgroup G} (hM : Max166 A c L Y₀ X J S C XC)
    (hZ : omegaOneZ S ≤ Subgroup.centralizer (Y₀ : Set G)) :
    delta A (lB A) (pPrimeCoreOf 3 X) ≤ Subgroup.normalizer (Y₀ : Set G) := by
  have hTQ : delta A (lB A) (pPrimeCoreOf 3 X) ∈ scriptQ A (lB A) :=
    mem_scriptQ_delta hM.conf h146
  have hTsol : Group.IsSolvable ↥(delta A (lB A) (pPrimeCoreOf 3 X)) := by
    haveI := hM.conf.solvable_core
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (Sec14.delta_le (pPrimeCoreOf 3 X)))
      (Subgroup.inclusion_injective _)
  have h146' : Item146 A (lB A) := h146 G A c L hM.conf.std.toSec14Std
  have h149' : Item149 A (lB A) := h149 G A c L hM.conf.std.toSec14Std
  have hXT : X ≤ Subgroup.normalizer
      (delta A (lB A) (pPrimeCoreOf 3 X) : Set G) :=
    CTrick.le_normalizer_delta_pPrimeCore hM.conf.std h146' hM.conf.mem_y3Star
  have hF : generalizedFitting ↥(deltaZero A (lB A) X) =
      CFSG.pCore 2 ↥(deltaZero A (lB A) X) :=
    CTrick.generalizedFitting_deltaZero_eq hM.conf.std h149' hM.conf.mem_y3Star
  have hO : pPrimeCoreOf 2 (delta A (lB A) (pPrimeCoreOf 3 X)) ≤
      Subgroup.normalizer (Y₀ : Set G) :=
    (pPrimeCoreOf_two_delta_le_centralizer hM.conf.std h146 hM.conf.mem_y3Star hXT hF).trans
      ((Subgroup.centralizer_le_normalizer (A : Set G)).trans hM.conf.std.normalizer_le)
  have hJY : J ≤ Y₀ := hM.conf.le_y0
  have hJperf : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hM.conf.mem_theta
  have hJA5 := hM.conf.quot_a5
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) := hM.conf.mem_y0.1.1.2
  have hMY : X ∈ scriptY2 A := hM.conf.mem_y3Star.prop.1
  have hJM : J ≤ X := hM.conf.le_X
  have hMJ : X ≤ Subgroup.normalizer (J : Set G) :=
    hM.conf.le_normalizer (hM.conf.comp3In_eq_of_ks hRead hMem h1523 hK)
  have hTle : delta A (lB A) (pPrimeCoreOf 3 X) ≤ pPrimeCoreOf 3 X :=
    Sec14.delta_le (A := A) (LB := lB A) (pPrimeCoreOf 3 X)
  have hTM : delta A (lB A) (pPrimeCoreOf 3 X) ≤ X := hTle.trans (pPrimeCoreOf_le 3 X)
  have hTJ : ⁅delta A (lB A) (pPrimeCoreOf 3 X), J⁆ ≤ CFSG.Open.pCoreOf 2 J := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono le_rfl hTle).trans hM.conf.commutator_pPrimeCore_le
  have hJQ : J ⊓ CFSG.Open.pCoreOf 2 Y₀ = CFSG.Open.pCoreOf 2 J :=
    le_antisymm hM.conf.inf_pCoreOf_le
      (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 J)
        (pCoreOf_le_pCoreOf_y0 h hJ h1523 hK hJY hJperf hJA5 hAJ))
  exact le_M_of_omegaOneZ_le_centralizer h hJ h155 h143 h134 h48 h1514 hMeets hKcd
    hData hKd hJY hJperf hJA5 hAJ hMY hJM hMJ hTM hTJ hJQ hTQ hTsol hM.sylow_le
    hM.sylow_isPGroup hM.sylow_not_dvd hM.sylow_inv hO hZ

private theorem delta_normalizer_le_of_step11_12
    (h : Sec17Std G A c L Y₀)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Blueprint.NativeSporadic.J2))
    (hbot : Item145BotS17) (hRead : Sec15.Y4CoreReadR) (hMem : Sec15.Y4CoreMemR)
    (h146 : Item146S14) (h1523 : Item1523R) (hK : KFacts.KS166J2A5) (hQ0 : Claim17Q0)
    (hsol : Step166SolHJ) (hΩ : Step166OmegaHJ) (hOmg : Step166OmgNotA5HJ)
    (h152 : Item152R) (h155 : Item155R) (h142 : Concl142S14) (h153 : Item153MainR)
    (h322 : Item3_22Two) {X J S C XC : Subgroup G} (hM : Max166 A c L Y₀ X J S C XC)
    (hZ : ¬ omegaOneZ S ≤ Subgroup.centralizer (Y₀ : Set G)) :
    delta A (lB A) (Subgroup.normalizer (jOf S : Set G)) ≤
        Subgroup.normalizer (Y₀ : Set G) ∧
      delta A (lB A) (Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G)) ≤
        Subgroup.normalizer (Y₀ : Set G) := by
  have hperf : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hM.conf.mem_theta
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) := hM.conf.mem_y0.1.1.2
  have hSQ : S ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le (mem_scriptQ_delta hM.conf h146) hM.sylow_le hM.sylow_inv
  have hspade := hM.spade hbot hRead hMem h146 h1523 hK hQ0 hsol hΩ hOmg h152 h155
  have hSJ' : ⁅S, J⁆ ≤ CFSG.Open.pCoreOf 2 J := hM.commutator_le
  have hQS : CFSG.Open.pCoreOf 2 (Y₀ ⊔ S) ≤ S :=
    pCoreOf_sup_le_of_spade h hJ h1523 h142 hQ0 hM.conf.le_y0 hM.sylow_isPGroup hSQ hSJ'
      hspade
  have hSM : S ≤ Subgroup.normalizer (Y₀ : Set G) :=
    HeadProof.le_M_of_mem_scriptQPi_two h
      ⟨⟨hSQ, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two S).mpr hM.sylow_isPGroup⟩
  have hSJ : ⁅S, J⁆ ≤ CFSG.Open.pCoreOf 2 Y₀ :=
    hSJ'.trans
      (pCoreOf_le_pCoreOf_y0 h hJ h1523 hK hM.conf.le_y0 hperf hM.conf.quot_a5 hAJ)
  obtain ⟨hQY, hCen⟩ :=
    pCoreOf_y0_eq_inf_and_quotientCentralizer_eq h hJ h1523 hM.sylow_isPGroup hSM hQS
  have hcov := exists_mem_inf_inv_mul_mem h hJ h1523 hK hM.conf.le_y0 hperf hM.conf.quot_a5
    hAJ hSM hQS hSJ hCen
  obtain ⟨ψ, hψ⟩ := exists_quotient_mulEquiv_y0 hSM hQY hcov
  have himg := map_star_inf_eq hcov ψ hψ
  have hdich := inf_le_pCoreOf_or_nonempty h hJ h1523 hK hM.conf.le_y0 hperf hM.conf.quot_a5
    hAJ hM.sylow_isPGroup hM.sylow_inv hSJ ψ himg
  have hY : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
    have h1 := (h1523 G A c L h.toSec15R hJ Y₀ h.mem_y0Star).1
    rwa [inf_of_le_right h.le_y0] at h1
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec17.PropU.nonempty_quotient_J2 h hJ hY
  exact delta_normalizer_le_of_dichotomy h h153 h322 hM.sylow_isPGroup hSM hM.sylow_inv hQS
    hQY hcov ⟨ψ.symm.trans e⟩ hdich hZ

theorem step166CtrA5HJ_of
    (hbot : Item145BotS17) (hRead : Sec15.Y4CoreReadR) (hMem : Sec15.Y4CoreMemR)
    (h146 : Item146S14) (h149 : Item149S14) (h1523 : Item1523R) (hK : KFacts.KS166J2A5)
    (hQ0 : Claim17Q0) (hsol : Step166SolHJ) (hΩ : Step166OmegaHJ) (hOmg : Step166OmgNotA5HJ)
    (h152 : Item152R) (h155 : Item155R) (h142 : Concl142S14) (h153 : Item153MainR)
    (h322 : Item3_22Two) (h143 : Ronan148Q.Item143QS14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h1514 : Item1514S17) (hMeets : Claim1715Meets)
    (hKcd : Step166KcdA5) (hData : Step166A5Data)
    (hKd : Step166KCommD) : Step166CtrA5HJ := by
  intro G _ _ A c L Y₀ h hJ
  refine ctr166A5_of_forall_not h hJ fun X J hC => ?_
  obtain ⟨X, J, S, C, XC, hM, hCM, hCor⟩ :=
    exists_max166 hbot hRead hMem h146 h149 h1523 hK ⟨X, J, hC⟩
  by_cases hZ : omegaOneZ S ≤ Subgroup.centralizer (Y₀ : Set G)
  · exact hM.conf.false_of_delta_le hbot hRead h146 h1523
      (hM.conf.comp3In_eq_of_ks hRead hMem h1523 hK)
      (le_M_of_step13 h hJ h146 h149 hK hRead hMem h1523 h155 h143 h134 h48
        h1514 hMeets hKcd hData hKd hM hZ)
  · obtain ⟨hN0, hN1⟩ :=
      delta_normalizer_le_of_step11_12 h hJ hbot hRead hMem h146 h1523 hK hQ0 hsol hΩ hOmg
        h152 h155 h142 h153 h322 hM hZ
    rcases hCor with rfl | rfl
    · exact hCM hN0
    · exact hCM hN1

end CFSG.RankThree.PartTwo.Sec16.Ctr166
