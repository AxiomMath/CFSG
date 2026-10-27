module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyTwoSteps
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyTwoRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4CartanRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4CartanRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.G2CartanRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4CartanPlus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4CartanPlusHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.RootLine
public import CFSG.GH74.Uniqueness.Section14Lem47A
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Local.Prop27Cfg
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvEngLift
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SurvU4Core
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvDefs
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.TorusBound
public import CFSG.LieType.SeitzGeneration.ExcPlaneFamilies
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Rank2
public import CFSG.Quasithin.Vol2.Ch10SecD33
public import CFSG.Quasithin.Vol2.Ch10SecDClA
public import CFSG.Quasithin.Vol2.Ch10SecKHK3C
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA11Main
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
public import CFSG.Quasithin.Vol2.Ch11SecAViN13
public import CFSG.Quasithin.Vol2.Ch11SecDFacts
public import CFSG.Quasithin.Vol2.Ch11SecDFacts3
public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartD
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4E
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4F
public import CFSG.Quasithin.Vol2.Ch11SecSMain
public import CFSG.Quasithin.Vol2.Ch11SecSShape2
public import CFSG.Quasithin.Vol2.Ch11SecSSym2
public import CFSG.Quasithin.Vol2.Ch11SecSSym3
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.KGNatSL3NatFixed
public import CFSG.Quasithin.Vol2.KGNatSp4Sim

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

local notation "pRank" => CFSG.Open.pRank

variable {G : Type} [Group G] [Finite G]

private theorem seventeen_fiftytwo_exists_rank_two
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (h49 : R17_49At D V₀ V) (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hKT : Inputs1719.K_LieBorelTorus)
    (hZ : Subgroup.center (Bar2 L) = ⊥)
    (hshape : IsU4 (Bar2 L) n ∨ IsSp4 (Bar2 L) n ∨ IsG2 (Bar2 L) n)
    (hq : 2 < 2 ^ n) (hndvd : ¬ p ∣ 2 ^ n - 1) :
    ∃ (r : ℕ) (R : Subgroup G), r.Prime ∧ r ≠ 2 ∧ r ≠ p ∧ r ∣ 2 ^ n - 1 ∧
      CFSG.ABGLocalTools.IsSylowOf r R C ∧ 2 ≤ pRank r R := by
  classical
  have hn : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp at hq
    · exact h
  obtain ⟨r, hr, hrdvd⟩ := uc22p20v_exists_prime_dvd_sub_one hn
  have hr2 : r ≠ 2 :=
    CFSG.GH74.Uniqueness.Sec147.ne_two_of_dvd_two_pow_sub_one (by omega) hrdvd
  have hrp : r ≠ p := by
    intro h
    exact hndvd (h ▸ hrdvd)
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨R, hR⟩ := CFSG.ABGLocalTools.exists_isSylowOf r C
  haveI : ((pCoreOf 2 L).subgroupOf C).Normal :=
    seventeen_fiftyone_cartan_pCore_normal h49 ctx
  have hcomm := (seventeen_fiftyone_cartan_comm_card hKT h49 ctx hZ hshape hq hr hrdvd).1
  have hcardOmega :=
    (seventeen_fiftyone_cartan_comm_card hKT h49 ctx hZ hshape hq hr hrdvd).2.1
  have hRcomm := (seventeen_fiftyone_R_abelian ctx hr hq hrdvd hR hcomm).1
  have hexp := (seventeen_fiftyone_R_abelian ctx hr hq hrdvd hR hcomm).2.1
  have hΩle : F11.Omega1p r R ≤ R :=
    (Subgroup.closure_le R).mpr (by rintro z ⟨hz, -⟩; exact hz)
  have hcard := seventeen_fiftyone_R_omega1p_card ctx hr hq hrdvd hR hcomm hcardOmega
  have hΩel : IsElemAbelian r (F11.Omega1p r R) := by
    refine ⟨?_, hexp⟩
    refine IsMulCommutative.mk ⟨fun a b => ?_⟩
    apply Subtype.ext
    have h := hRcomm.is_comm.comm (⟨(a : G), hΩle a.2⟩ : ↥R) (⟨(b : G), hΩle b.2⟩ : ↥R)
    simpa using congrArg (fun z : ↥R => (z : G)) h
  have hRr : 2 ≤ pRank r R := by
    have hcardEq : Nat.card (F11.Omega1p r R) = r ^ pRank r (F11.Omega1p r R) :=
      CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hr hΩel
    have h2 : 2 ≤ pRank r (F11.Omega1p r R) := by
      rw [hcardEq] at hcard
      exact (Nat.pow_le_pow_iff_right hr.one_lt).1 hcard
    exact h2.trans (CFSG.SectionRank.pRank_mono hr.one_lt hΩle)
  exact ⟨r, R, hr, hr2, hrp, hrdvd, hR, hRr⟩

theorem seventeen_fiftytwo
    (D : Data G) (V₀ V : Subgroup G) (h49 : R17_49At D V₀ V) (h50 : R17_50At D V₀ V)
    (h51 : R17_51At D V₀ V) (hSg : UC6S846.SigmaStd D) (hDE : DataExt D)
    (h76 : F07.R76 D) (h638 : UC6.R6_38 D)
    (hT : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankChev) :
    R17_52At D V₀ V := by
  classical
  have hKT : Inputs1719.K_LieBorelTorus :=
    Inputs1719.K_LieBorelTorus_of_parts Inputs1719.k_U4CartanRank_holds
      Inputs1719.k_Sp4CartanRank_holds Inputs1719.k_G2CartanRank_holds
  have h3at : R17_52_3At D V₀ V := by
    intro L X p n l C Dc Gamma ctx
    have hLX : L = X := h49 L X p n l C Dc Gamma ctx
    have hq : 2 < 2 ^ n := (h50 L X p n l C Dc Gamma ctx).2
    have hshape : IsU4 (Bar2 L) n ∨ IsSp4 (Bar2 L) n ∨ IsG2 (Bar2 L) n := by
      have h := (h50 L X p n l C Dc Gamma ctx).1
      rwa [← hLX] at h
    have hZ : Subgroup.center (Bar2 L) = ⊥ := Inputs1719.center_eq_bot_of_rootLineShape hq hshape
    have hOut : IsCyclic (Outer (Bar2 L)) := by
      rcases hshape with hU4 | hSp4 | hG2
      · exact Inputs1719.isCyclic_outer_of_lieModel_PSU4 hU4
      · exact Inputs1719.isCyclic_outer_of_lieModel_PSp4 hSp4
      · exact Inputs1719.isCyclic_outer_of_lieModel_G2 hG2
    have hp : p.Prime := (D.sig_prime p ctx.p_mem).1
    have hp2 : p ≠ 2 := (D.sig_prime p ctx.p_mem).2
    have hndvd : ¬ p ∣ 2 ^ n - 1 := Ctx17_42.not_dvd_two_pow_sub_one ctx h51 hSg
    obtain ⟨r, R, hr, hr2, hrp, hrdvd, hR, hRr⟩ :=
      seventeen_fiftytwo_exists_rank_two h49 ctx hKT hZ hshape hq hndvd
    by_contra hnot
    have hpl : ¬ p ∣ 2 ^ n + 1 := by
      intro hd
      exact hnot (zmod_of_dvd_two_pow_add_one hd)
    have hn : 2 ≤ n := by
      rcases Nat.lt_or_ge n 2 with h | h
      · interval_cases n <;> simp at hq
      · exact h
    have hle1 : pRank p (⊤ : Subgroup (Bar2 L)) ≤ 1 :=
      pRank_le_one_of_rootLineShape_of_not_dvd hT ctx.mem_calC.2.2 hZ hn hshape hp hp2 hndvd hpl
    have hM3 : 3 ≤ pRank p D.M := hDE.three_le p ctx.p_mem
    exact Ctx17_42.false_of_pRank_add_two_le ctx h49 h51 h76 hSg h638 hZ hOut
      hr hr2 hrp hrdvd hR hRr (by omega)
  have h2at : R17_52_2At D V₀ V := by
    intro L X p n l C Dc Gamma ctx
    have hLX : L = X := h49 L X p n l C Dc Gamma ctx
    have hq : 2 < 2 ^ n := (h50 L X p n l C Dc Gamma ctx).2
    have hshape : IsU4 (Bar2 L) n ∨ IsSp4 (Bar2 L) n ∨ IsG2 (Bar2 L) n := by
      have h := (h50 L X p n l C Dc Gamma ctx).1
      rwa [← hLX] at h
    have hp : p.Prime := (D.sig_prime p ctx.p_mem).1
    have hp2 : p ≠ 2 := (D.sig_prime p ctx.p_mem).2
    have hcong : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] := h3at L X p n l C Dc Gamma ctx
    by_cases h2 : pRank p L = 2
    · exact Or.inl h2
    · refine Or.inr ⟨?_, hcong⟩
      have hn : 2 ≤ n := by
        rcases Nat.lt_or_ge n 2 with h | h
        · interval_cases n <;> simp at hq
        · exact h
      have hpdvd : p ∣ 2 ^ n + 1 := by
        obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.mp hcong
        have hd : (p : ℤ) ∣ (2 : ℤ) ^ n + 1 := by
          refine ⟨-c, ?_⟩
          linear_combination -hc
        exact Int.natCast_dvd_natCast.mp (by simpa using hd)
      have hZ : Subgroup.center (Bar2 L) = ⊥ := Inputs1719.center_eq_bot_of_rootLineShape hq hshape
      have hEq : pRank p (⊤ : Subgroup (Bar2 L)) = pRank p L :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.pRank_bar2_eq_of_odd hp hp2
      rcases hshape with hU4 | hSp4 | hG2
      · exact hU4
      · exfalso
        have hrank : pRank p (⊤ : Subgroup (Bar2 L)) = 2 :=
          (pRank_of_dvd_add_one hT ctx.mem_calC.2.2 hZ hn hp hp2 hpdvd).1 (Or.inl hSp4)
        exact h2 (hEq.symm.trans hrank)
      · exfalso
        have hrank : pRank p (⊤ : Subgroup (Bar2 L)) = 2 :=
          (pRank_of_dvd_add_one hT ctx.mem_calC.2.2 hZ hn hp hp2 hpdvd).1 (Or.inr hG2)
        exact h2 (hEq.symm.trans hrank)
  have h1at : R17_52_1At D V₀ V := by
    intro L X p n l C Dc Gamma ctx
    have hLX : L = X := h49 L X p n l C Dc Gamma ctx
    have hq : 2 < 2 ^ n := (h50 L X p n l C Dc Gamma ctx).2
    have hshape : IsU4 (Bar2 L) n ∨ IsSp4 (Bar2 L) n ∨ IsG2 (Bar2 L) n := by
      have h := (h50 L X p n l C Dc Gamma ctx).1
      rwa [← hLX] at h
    have hZ : Subgroup.center (Bar2 L) = ⊥ := Inputs1719.center_eq_bot_of_rootLineShape hq hshape
    have hOut : IsCyclic (Outer (Bar2 L)) := by
      rcases hshape with hU4 | hSp4 | hG2
      · exact Inputs1719.isCyclic_outer_of_lieModel_PSU4 hU4
      · exact Inputs1719.isCyclic_outer_of_lieModel_PSp4 hSp4
      · exact Inputs1719.isCyclic_outer_of_lieModel_G2 hG2
    have hp : p.Prime := (D.sig_prime p ctx.p_mem).1
    have hp2 : p ≠ 2 := (D.sig_prime p ctx.p_mem).2
    have hndvd : ¬ p ∣ 2 ^ n - 1 := Ctx17_42.not_dvd_two_pow_sub_one ctx h51 hSg
    obtain ⟨r, R, hr, hr2, hrp, hrdvd, hR, hRr⟩ :=
      seventeen_fiftytwo_exists_rank_two h49 ctx hKT hZ hshape hq hndvd
    have hn : 2 ≤ n := by
      rcases Nat.lt_or_ge n 2 with h | h
      · interval_cases n <;> simp at hq
      · exact h
    have h3eM : 3 ≤ eM D.M := by
      have hbdd : BddAbove {k : ℕ | ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ k = pRank q D.M} :=
        ⟨Nat.card G, by
          rintro k ⟨q, hq, hq2, rfl⟩
          exact CFSG.SectionRank.pRank_le_card_of_one_lt hq.one_lt D.M⟩
      have hle : pRank p D.M ≤ eM D.M := by
        unfold eM
        exact le_csSup hbdd ⟨p, hp, hp2, rfl⟩
      exact (hDE.three_le p ctx.p_mem).trans hle
    refine le_antisymm ?_ h3eM
    by_contra hne
    have hlt : 3 < eM D.M := lt_of_not_ge hne
    have hG4 : 3 < evenRank G := lt_of_lt_of_le hlt (eM_le_evenRank D)
    have hM4 : 4 ≤ pRank p D.M := hDE.four_le hG4 p ctx.p_mem
    by_cases hpadd : p ∣ 2 ^ n + 1
    · rcases hshape with hU4 | hSp4 | hG2
      · have hU4rank : pRank p (⊤ : Subgroup (Bar2 L)) = 3 :=
          (pRank_of_dvd_add_one hT ctx.mem_calC.2.2 hZ hn hp hp2 hpadd).2 hU4
        exact Ctx17_42.false_of_u4_rank ctx h49 h51 h76 hSg h638 hKT
          Inputs1719.k_U4CartanPlus_holds hZ hOut hU4 hq
          hpadd hr hr2 hrdvd hR hRr (by omega)
      · have hrank : pRank p (⊤ : Subgroup (Bar2 L)) = 2 :=
          (pRank_of_dvd_add_one hT ctx.mem_calC.2.2 hZ hn hp hp2 hpadd).1 (Or.inl hSp4)
        exact Ctx17_42.false_of_pRank_add_two_le ctx h49 h51 h76 hSg h638 hZ hOut
          hr hr2 hrp hrdvd hR hRr (by omega)
      · have hrank : pRank p (⊤ : Subgroup (Bar2 L)) = 2 :=
          (pRank_of_dvd_add_one hT ctx.mem_calC.2.2 hZ hn hp hp2 hpadd).1 (Or.inr hG2)
        exact Ctx17_42.false_of_pRank_add_two_le ctx h49 h51 h76 hSg h638 hZ hOut
          hr hr2 hrp hrdvd hR hRr (by omega)
    · have hle1 : pRank p (⊤ : Subgroup (Bar2 L)) ≤ 1 :=
        pRank_le_one_of_rootLineShape_of_not_dvd hT ctx.mem_calC.2.2 hZ hn hshape hp hp2 hndvd hpadd
      exact Ctx17_42.false_of_pRank_add_two_le ctx h49 h51 h76 hSg h638 hZ hOut
        hr hr2 hrp hrdvd hR hRr (by omega)
  exact ⟨h1at, h2at, h3at⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
