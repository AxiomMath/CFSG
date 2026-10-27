module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThreeOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTenCalV1
import CFSG.Quasithin.Background.HTransport
import CFSG.Quasithin.Background.E3CentASet

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

open TwelveShort

theorem commutator_conjClosure_le_centralizer_of_add_lt {D : Data G} {V U : Subgroup G}
    (hV : IsElemAbelian 2 V) (hU : IsElemAbelian 2 U) (hMU : D.M ≤ normalizer (U : Set G))
    {L : Subgroup G} (hLM : CFSG.Open.IsSubnormal L D.M) {i : ℕ}
    (hb : i + bBar (UC22.conjClosure D.M L) D.M ⊥ U hU < E3.sParam hV) :
    ∀ A ∈ E3.gammaSet V i D.T, ∀ x ∈ UC22.conjClosure D.M L, ∀ a ∈ A,
      ⁅x, a⁆ ∈ D.M ⊓ centralizer (U : Set G) := by
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hXM : UC22.conjClosure D.M L ≤ D.M := TwelveTwentyThree.conjClosure_le hLM.le
  have hMS : D.M ≤ stabTil ⊥ U :=
    le_stabTil hMU (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  intro A hA x hxX a ha
  have hAM : A ≤ D.M := hA.1.trans hTM
  have hbar : ⁅barSub ⊥ U hU (UC22.conjClosure D.M L), barSub ⊥ U hU A⁆ = ⊥ := by
    by_cases hA1 : autI hU A = ⊥
    · have h0 : barSub ⊥ U hU A = ⊥ := by
        rw [TwelveTwentyThree.barSub_bot_eq_map_autI U hU A, hA1, Subgroup.map_bot]
      rw [h0, Subgroup.commutator_bot_right]
    · have hmem := E3.autI_mem_aSet_of_mem_gammaSet_of_add_lt hV hTM hMU hU hb hA hA1
      have hA' : barSub ⊥ U hU A ∈
          calABar (bBar (UC22.conjClosure D.M L) D.M ⊥ U hU + 1) D.M ⊥ U hU := by
        show barSub ⊥ U hU A ∈ E3.aSet
          (bBar (UC22.conjClosure D.M L) D.M ⊥ U hU + 1) (barSub ⊥ U hU D.M)
        rw [TwelveTwentyThree.barSub_bot_eq_map_autI U hU D.M,
          TwelveTwentyThree.barSub_bot_eq_map_autI U hU A]
        exact (H.map_mem_aSet_iff _).2 hmem
      exact (bBar_lt_iff hU (Nat.succ_pos _)).1 (Nat.lt_succ_self _) _ hA'
  have hxS : x ∈ stabTil ⊥ U := hMS (hXM hxX)
  have haS : a ∈ stabTil ⊥ U := hMS (hAM ha)
  have hmem : ⁅actTil ⊥ U hU ⟨x, hxS⟩, actTil ⊥ U hU ⟨a, haS⟩⁆ ∈
      ⁅barSub ⊥ U hU (UC22.conjClosure D.M L), barSub ⊥ U hU A⁆ :=
    Subgroup.commutator_mem_commutator (actTil_mem_barSub ⊥ U hU hxX hxS)
      (actTil_mem_barSub ⊥ U hU ha haS)
  rw [hbar, Subgroup.mem_bot, ← map_commutatorElement,
    TwelveTwentyThree.actTil_bot_eq_one_iff] at hmem
  refine ⟨?_, hmem⟩
  rw [commutatorElement_def]
  exact D.M.mul_mem (D.M.mul_mem (D.M.mul_mem (hXM hxX) (hAM ha)) (D.M.inv_mem (hXM hxX)))
    (D.M.inv_mem (hAM ha))

theorem twelve_twentyThree_one_of_inCalW (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h126 : R126 D) (h111 : W3Thm111 G)
    (h124 : ∃ H₀ ∈ CFSG.LocalAnalysis.RankThreeUC.hSet D.T D.M,
      CFSG.LocalAnalysis.RankThreeUC.Hyp124 D.M H₀)
    {V : Subgroup G} (hW : InCalW D.M D.T V) (hV : IsElemAbelian 2 V)
    {L : Subgroup G} (hLM : CFSG.Open.IsSubnormal L D.M)
    (hLq : CFSG.Open.IsQuasisimple (UC22.Bar2 L)) (hL1 : barSub ⊥ V hV L ≠ ⊥)
    (hU : UniqueMax D.M (UC22.conjClosure D.M L ⊔ D.T)) :
    mBar D.M ⊥ V hV ≤ bBar (UC22.conjClosure D.M L) D.M ⊥ V hV + D.k := by
  by_contra hlt
  rw [not_le] at hlt
  have hV1 : InCalV1 D.M D.T V := hW.1
  have hVV : InCalV D.M V := hW.1.1
  have hMN : D.M ≤ normalizer (V : Set G) := hVV.2.2.1
  have hbot : D.M ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hm : MBarGT D.M ⊥ V (D.k + bBar (UC22.conjClosure D.M L) D.M ⊥ V hV) :=
    (mBarGT_iff_lt_mBar D.M ⊥ V hV bot_le hMN hbot _).2 (by omega)
  have hm0 : MBarGT D.M ⊥ V (D.k + 0) :=
    (mBarGT_iff_lt_mBar D.M ⊥ V hV bot_le hMN hbot _).2 (by omega)
  have h10 := twelve_ten_two_of_inCalV1 D hx h61 h126 h111 h124 hV1 hW.2.1 hm0
  have hrk := mBar_le_rk (M := D.M) hV (bot_le : (⊥ : Subgroup G) ≤ V)
  have hlt0 : D.k + bBar (UC22.conjClosure D.M L) D.M ⊥ V hV < E3.sParam hV := by
    by_cases hm2 : MBarGT D.M ⊥ V 2
    · exact TwelveShort.lt_sParam_of_mBarGT D h111 hV1 hm2 hm
    · have hki : D.k + bBar (UC22.conjClosure D.M L) D.M ⊥ V hV = 1 := by
        have h1 := TwelveShort.one_le_k D
        by_contra hc
        exact hm2 (TwelveShort.mBarGT_mono hm (by omega))
      have hr : ((D.k + bBar (UC22.conjClosure D.M L) D.M ⊥ V hV : ℕ) : ℕ∞) <
          E3.rParam V := by
        have h1 := TwelveTen.one_lt_rMV D hx h61 hVV (by have := hW.2.1; omega)
        rw [rMV_eq_rParam_of_inCalV D hVV] at h1
        rw [hki]
        exact_mod_cast h1
      exact E3.lt_sParam_of_lt hV hr ((TwelveShort.mBarGT_bot_iff_lt_mParam_autI D hVV _).1 hm)
  have hcomm := commutator_conjClosure_le_centralizer_of_add_lt hV hV hMN hLM (i := D.k) hlt0
  set X := UC22.conjClosure D.M L
  set b := bBar X D.M ⊥ V hV
  have hred : TwoReduced D.M V := hW.2.2
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hTS : IsSylowIn 2 D.T D.M := TwelveShort.isSylowIn_of_le D hTM
  have hT2 : IsPGroup 2 D.T := hTS.isPGroup
  have hXM : X ≤ D.M := TwelveTwentyThree.conjClosure_le hLM.le
  have hKn : D.M ≤ normalizer ((D.M ⊓ centralizer (V : Set G) : Subgroup G) : Set G) :=
    A1a.le_normalizer_inf Subgroup.le_normalizer (A1a.le_normalizer_centralizer hMN)
  have hPK : pCoreOf 2 D.M ≤ D.M ⊓ centralizer (V : Set G) :=
    le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)
      (TwelveTwentyThree.pCoreOf_le_centralizer_of_twoReduced hMN hred)
  have hLK : ¬ L ≤ D.M ⊓ centralizer (V : Set G) := by
    intro hle
    apply hL1
    refine le_bot_iff.1 fun φ hφ => ?_
    obtain ⟨g, hgL, rfl⟩ := (mem_barSub ⊥ V _ L φ).1 hφ
    rw [Subgroup.mem_bot, TwelveTwentyThree.actTil_bot_eq_one_iff]
    exact (hle hgL).2
  have hPT : pCoreOf 2 D.M ≤ D.T := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact hTS.le_of_normal (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)).2
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M)
  have hN : X ≤ normalizer (E3.wClos V D.k D.T : Set G) := by
    refine TwelveTwentyThree.le_normalizer_wClos fun x hxX A hA a ha => hPT ?_
    exact TwelveTwentyThree.commutator_mem_pCoreOf hLM hLq inf_le_left hKn hPK hLK
      (hA.1.trans hTM) (hcomm A hA) x hxX a ha
  have hTNW : D.T ≤ normalizer (E3.wClos V D.k D.T : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos (V := V) (i := D.k) D.T)
  have hUN : InCalU D.M (D.M ⊓ normalizer (E3.wClos V D.k D.T : Set G)) :=
    InCalU.mono D.maxLocal hU (le_inf (sup_le hXM hTM) (sup_le hN hTNW)) inf_le_left
  have hk : D.k < rk ↥V := by omega
  obtain ⟨h1, h2⟩ := six_fifteen_three hV D.maxLocal hT2 (TwelveShort.wClos_zero_ne_bot D hVV)
    hk hUN
  rcases h10 with h10 | h10
  · exact h10 (h1 0 (by omega))
  · exact h10 (by simpa using h2 0 (Nat.zero_le _))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
