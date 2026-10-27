module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofPassage
public import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofTrans
public import CFSG.RankThree.PartTwo.Sec19.Item194Inputs
public import CFSG.RankThree.PartTwo.Sec15.Item158Res2ProofInner

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.LocalRank
  CFSG.GH74.GLS

theorem step1515HJVTail_of (hF : Step1515HJVFour) (hR : Step1515HJVR)
    (hB : Step1515HJVBlock) : Step1515HJVTail := by
  intro G _ _ A c L hR' hJ Y hY hm hYL hLY hΩ d hdA hd1 hdZ hV hP
  have h : Conf1515HJ A c L Y := ⟨hR', hJ, hY, hm, hYL, hLY, hΩ⟩
  by_cases hV1 : ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ = ⊥
  · intro x hx
    have hxc := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hV1) hx
    rw [Subgroup.mem_centralizer_iff] at hxc
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hxc c (Subgroup.mem_zpowers c)).symm
  · have h4 := hF G A c L Y h d hdA hd1 hdZ hV hP hV1
    have hle := hR G A c L Y h d hdA hd1 hdZ hV hP h4
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hOO : CFSG.Open.pCoreOf 2 Y ≤
        CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans Subgroup.le_normalizer)
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
    have hRV : ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y : Set G)), Subgroup.zpowers c⁆ =
        ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ :=
      le_antisymm hle (Subgroup.commutator_mono hOO le_rfl)
    exact (hB G A c L Y h d hdA hd1 hdZ hV hP h4 hRV).elim

theorem step1515HJEndTail_of (hX : Step1515HJEndX) (hT : Step1515HJEndT0) :
    Step1515HJEndTail := by
  intro G _ _ A c L hR' hJ Y hY hm hYL hLY hΩ d hdA hd1 hdZ hP hYc
  have h : Conf1515HJ A c L Y := ⟨hR', hJ, hY, hm, hYL, hLY, hΩ⟩
  exact hT G A c L Y h d hdA hd1 hdZ hP hYc (hX G A c L Y h d hdA hd1 hdZ hP hYc)

@[expose] noncomputable def Step1515HJVBlockM : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y : Subgroup G),
    Conf1515HJ A c L Y → ∀ d ∈ A, d ≠ 1 → IsZCentral L d →
    ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ ≤ Subgroup.centralizer ({d} : Set G) →
    Odd (Nat.card ↥(Subgroup.normalizer (Y : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)))) →
    Nat.card ↥⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ = 4 →
    ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y : Set G)), Subgroup.zpowers c⁆ =
      ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers c⁆ →
        ∃ M K : Subgroup G, CFSG.IsMaximalTwoLocal M ∧ IsScriptLBlock M K

theorem step1515HJVBlock_of (h316 : Sec19.Item316) (h : Step1515HJVBlockM) :
    Step1515HJVBlock := by
  intro G _ _ A c L Y hc d hdA hd1 hdZ hV hP h4 hR
  obtain ⟨M, K, hM, hK⟩ := h G A c L Y hc d hdA hd1 hdZ hV hP h4 hR
  have hS := hc.sec13Data
  exact hS.not_inCatalog
    (h316 G hS.isSimpleGroup hS.nonabelian hS.kProper hS.charTwoType hS.evenRank_eq M K hM hK)

theorem step1515HJVTail_of_res4 (h316 : Sec19.Item316) (hF : Step1515HJVFour)
    (hR : Step1515HJVR) (hB : Step1515HJVBlockM) : Step1515HJVTail :=
  step1515HJVTail_of hF hR (step1515HJVBlock_of h316 hB)

theorem step158CartanCore_of (h : Step158CartanP) : Step158CartanCore := by
  intro G _ _ A c L hR p e _ he hL3 Y hY hmeet P hAP hP hΩ
  obtain ⟨E, F, hEP, hFP, hE3, hE27, hEC, hEtype, hF3, hF27, hFcL, hF9, hFfus, hFE⟩ :=
    h G A c L hR p e he hL3 Y hY hmeet P hAP hP hΩ
  have hcE : c ∈ E := by
    have hc : c ∈ (Subgroup.zpowers c : Set G) := Subgroup.mem_zpowers c
    rw [← hEC] at hc
    exact hc.1
  refine ⟨E, F, hEP, hE3, hE27, hEC, hEtype, ⟨⟨?_, hF3, hF27, hFfus, hFE⟩, hF9⟩, ?_⟩
  · exact hFcL.trans (sup_le_sup_right (Subgroup.zpowers_le.mpr hcE) L)
  · exact hFP.trans (hP.le.trans inf_le_right)

section HJ

theorem step1515HJD_of_res4 (h134 : Item134) (h48 : Sec4.Item4_8) (hC : Step1515HJConj)
    (hQN : Step1515HJQN) (hloc : Claim1411LocalR) : Step1515HJD :=
  step1515HJD_of (step1515HJTrans_of h134 h48) hC hQN hloc Proof15Res4.passage1515

theorem step1515HJ_of_res4 (h134 : Item134) (h48 : Sec4.Item4_8) (hloc : Claim1411LocalR)
    (h316 : Sec19.Item316) (hC : Step1515HJConj) (hQN : Step1515HJQN) (hF : Step1515HJVFour)
    (hR : Step1515HJVR) (hB : Step1515HJVBlockM) (hX : Step1515HJEndX)
    (hT : Step1515HJEndT0) : Step1515HJ :=
  step1515HJ_of_tails (step1515HJD_of_res4 h134 h48 hC hQN hloc)
    (step1515HJVTail_of_res4 h316 hF hR hB) (step1515HJEndTail_of hX hT)

end HJ

end CFSG.RankThree.PartTwo.Sec15
