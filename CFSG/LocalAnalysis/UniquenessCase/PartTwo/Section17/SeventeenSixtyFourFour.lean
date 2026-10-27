module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20g
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.PRankSmall
public import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
public import CFSG.GroupTheory.ConjActionModPCore
public import CFSG.Holt.General.NoRelevantBasic
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.GL83PartI.I713.Extension
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bar13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.E9O2Normal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsD
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure
public import CFSG.Walter.Bender1970.S1.Rank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem two_le_of_P17_64_2 {D : Data G} {p n : ℕ} (hn : P17_64_2 D p n) : 2 ≤ n := by
  rcases hn with ⟨⟨A, B, gA, gB, e, hA, hB⟩, -⟩ | ⟨⟨A, B, gA, gB, e, hA, hB⟩, -⟩
  · exact uc22p20g_two_le_of_isL2 hA
  · exact uc22p20g_two_le_of_isL2 hA

theorem pRank_le_two_of_isU3 {X : Type} [Group X] [Finite X] {n r : ℕ}
    (h : IsU3 X n) (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup X) ≤ 2 := by
  have hn1 : 1 ≤ n := h.admissible.2.1
  have hSC : StatedClassicalModel X .PSU 3 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.projSU_of_statedClassicalModel hSC
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e]
  exact CFSG.RankThree.PartOne.LIT.pRank_projSU_three_le hn1 hr hr2

theorem center_eq_bot_of_isU3 {X : Type} [Group X] {n : ℕ} (h : IsU3 X n) :
    Subgroup.center X = ⊥ := by
  haveI := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_PSU3 h
  obtain ⟨a, b, hab⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_PSU3 h
  exact TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
    fun hc => hab (hc.is_comm.comm a b)

theorem center_eq_bot_bar2_lp {D : Data G} {p n : ℕ}
    (hn : P17_64_2 D p n) : Subgroup.center (Bar2 (Lp D p)) = ⊥ := by
  rcases hn with ⟨⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩, -⟩ |
    ⟨⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩, -⟩
  · haveI : Finite A := CFSG.LieType.Simplicity.finite_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hA)
    haveI : Finite B := CFSG.LieType.Simplicity.finite_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hB)
    refine CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e ?_
    rw [Subgroup.center_prod, center_eq_bot_of_lieModel_psl2 hA,
      center_eq_bot_of_lieModel_psl2 hB, Subgroup.bot_prod_bot]
  · haveI : Finite A := CFSG.LieType.Simplicity.finite_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hA)
    haveI : Finite B := CFSG.LieType.Simplicity.finite_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hB)
    refine CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e ?_
    rw [Subgroup.center_prod, center_eq_bot_of_lieModel_psl2 hA, center_eq_bot_of_isU3 hB,
      Subgroup.bot_prod_bot]

@[expose] def K_OutL2U3Product : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n → IsPowTwo n →
    (IsL2Square X n ∨ IsL2U3Product X n) → IsPGroup 2 (Outer X)

theorem pRank_bar2_lp_le_two {D : Data G} {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : IsL2Square (Bar2 (Lp D p)) n) :
    CFSG.Open.pRank p (⊤ : Subgroup (Bar2 (Lp D p))) ≤ 2 := by
  obtain ⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩ := h
  haveI : Finite A := CFSG.LieType.Simplicity.finite_of_statedClassicalModel
    (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hA)
  haveI : Finite B := CFSG.LieType.Simplicity.finite_of_statedClassicalModel
    (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hB)
  have hA1 : CFSG.Open.pRank p (⊤ : Subgroup A) ≤ 1 :=
    CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_even
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hA) hp hp2
  have hB1 : CFSG.Open.pRank p (⊤ : Subgroup B) ≤ 1 :=
    CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_even
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hB) hp hp2
  have hprod := CFSG.Quasithin.H13.NQBlock.pRank_prod_le (S := A) (T := B) hp
  have hbar : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 (Lp D p))) =
      CFSG.Open.pRank p (⊤ : Subgroup (A × B)) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
  omega

theorem pRank_bar2_lp_le_three' {D : Data G} {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : IsL2U3Product (Bar2 (Lp D p)) n) :
    CFSG.Open.pRank p (⊤ : Subgroup (Bar2 (Lp D p))) ≤ 3 := by
  obtain ⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩ := h
  haveI : Finite A := CFSG.LieType.Simplicity.finite_of_statedClassicalModel
    (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hA)
  haveI : Finite B := CFSG.LieType.Simplicity.finite_of_statedClassicalModel
    (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hB)
  have hA1 : CFSG.Open.pRank p (⊤ : Subgroup A) ≤ 1 :=
    CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_even
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hA) hp hp2
  have hB2 : CFSG.Open.pRank p (⊤ : Subgroup B) ≤ 2 :=
    pRank_le_two_of_isU3 hB hp hp2
  have hprod := CFSG.Quasithin.H13.NQBlock.pRank_prod_le (S := A) (T := B) hp
  have hbar : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 (Lp D p))) =
      CFSG.Open.pRank p (⊤ : Subgroup (A × B)) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
  omega

theorem pRank_eq_three_of_P17_64_2 {D : Data G}
    {V₀ V : Subgroup G} {p n : ℕ} (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h57 : R17_57At D V₀ V) (hKOut : K_OutL2U3Product) (hp : Hyp1754 D p)
    (hn : P17_64_2 D p n) (hpow : IsPowTwo n) : CFSG.Open.pRank p D.M = 3 := by
  have hp' := D.sig_prime p hp.1
  have hp1 : 1 < p := hp'.1.one_lt
  refine le_antisymm ?_ (hSg.three_le p hp.1)
  have hLM : Lp D p ≤ D.M := Lp_le_M D p
  have hNM : D.M ≤ normalizer (Lp D p : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp (s13_Lp_normal D.M p)
  have hrank := CFSG.GroupTheory.pRank_le_pRank_map_ker_add_pRank_range 2 p hp'.1
    (Lp D p) D.M hNM
  have hker : CFSG.Open.pRank p
      ((CFSG.GroupTheory.conjModPCore 2 (Lp D p) D.M hNM).ker.map D.M.subtype) ≤
        CFSG.Open.pRank p (Sp D p) := by
    have hle : (CFSG.GroupTheory.conjModPCore 2 (Lp D p) D.M hNM).ker.map D.M.subtype ≤
        centSection D.M (Lp D p) (pCoreOf 2 (Lp D p)) := by
      intro m hm
      obtain ⟨hmM, hcomm⟩ :=
        (CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 (Lp D p) D.M hNM).mp hm
      exact ⟨hmM, hNM hmM, (hNM.trans (CFSG.Holt.General.NoRelevant.normalizer_le_normalizer_map
        (M := Lp D p) (K := CFSG.pCore 2 ↥(Lp D p)))) hmM, hcomm⟩
    calc CFSG.Open.pRank p
          ((CFSG.GroupTheory.conjModPCore 2 (Lp D p) D.M hNM).ker.map D.M.subtype)
        ≤ CFSG.Open.pRank p (centSection D.M (Lp D p) (pCoreOf 2 (Lp D p))) :=
          CFSG.SectionRank.pRank_mono hp1 hle
      _ = CFSG.Open.pRank p (Sp D p) :=
          (s13_pRank_pElementSubgroup hp'.1 _).symm
  have hrange : CFSG.Open.pRank p
      (CFSG.GroupTheory.conjModPCore 2 (Lp D p) D.M hNM).range ≤
        CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Bar2 (Lp D p)))) :=
    CFSG.SectionRank.pRank_mono hp1 le_top
  have haut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Bar2 (Lp D p)))) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (Bar2 (Lp D p))) +
        CFSG.Open.pRank p (⊤ : Subgroup (Outer (Bar2 (Lp D p)))) :=
    GL83.I713.pRank_mulAut_le hp'.1 (center_eq_bot_bar2_lp hn)
  have hout : CFSG.Open.pRank p (⊤ : Subgroup (Outer (Bar2 (Lp D p)))) = 0 :=
    CFSG.Walter.pRank_eq_zero_of_isPGroup Nat.prime_two hp'.1 hp'.2
      ((hKOut (Bar2 (Lp D p)) n (two_le_of_P17_64_2 hn) hpow
        (Or.imp And.left And.left hn)).to_subgroup ⊤)
  have hMle : CFSG.Open.pRank p D.M ≤
      CFSG.Open.pRank p (Sp D p) + CFSG.Open.pRank p (⊤ : Subgroup (Bar2 (Lp D p))) := by
    have h1 := hrank
    have h2 := hrange
    have h3 := haut
    rw [hout, add_zero] at h3
    omega
  rcases hn with ⟨hsq, hspne⟩ | ⟨hu3, hspbot⟩
  · have hbar := pRank_bar2_lp_le_two hp'.1 hp'.2 hsq
    have hsp := h57 p hp
    omega
  · have hbar := pRank_bar2_lp_le_three' hp'.1 hp'.2 hu3
    have hsp : CFSG.Open.pRank p (Sp D p) = 0 := by
      rw [hspbot]
      refine CFSG.LocalAnalysis.GLTheoremA.pRank_eq_zero_of_not_dvd_card hp'.1 (H := ⊥) ?_
      rw [Subgroup.card_bot]
      exact hp'.1.not_dvd_one
    omega

theorem inf_centSection_Lp_le_pCore {D : Data G} {p n : ℕ}
    (hn : P17_64_2 D p n) :
    (centSection D.M (Lp D p) (pCoreOf 2 (Lp D p)) ⊓ Lp D p) ≤ pCoreOf 2 (Lp D p) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro m hm
  obtain ⟨hmC, hmL⟩ := hm
  have hcenter : (QuotientGroup.mk' (CFSG.pCore 2 ↥(Lp D p)) ⟨m, hmL⟩) ∈
      Subgroup.center (Bar2 (Lp D p)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨a, haL, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(Lp D p)) y
    have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥(Lp D p)))
        (⟨m, hmL⟩ * ⟨a, a.2⟩ * ⟨m, hmL⟩⁻¹ * ⟨a, a.2⟩⁻¹) = 1 := by
      refine (QuotientGroup.eq_one_iff _).mpr ?_
      obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp (hmC.2.2.2 a a.2)
      rw [show (⟨m, hmL⟩ * ⟨a, a.2⟩ * ⟨m, hmL⟩⁻¹ * ⟨a, a.2⟩⁻¹ : ↥(Lp D p)) = y from
        Subtype.ext (by simpa using hyeq.symm)]
      exact hy
    have h2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥(Lp D p)) ⟨m, hmL⟩) *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(Lp D p)) ⟨a, a.2⟩) *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(Lp D p)) ⟨m, hmL⟩)⁻¹ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(Lp D p)) ⟨a, a.2⟩)⁻¹ = 1 := by
      simpa only [map_mul, map_inv] using h1
    rw [← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2.symm
  have hbot : Subgroup.center (Bar2 (Lp D p)) = ⊥ := center_eq_bot_bar2_lp hn
  rw [hbot, Subgroup.mem_bot] at hcenter
  have hmk : (QuotientGroup.mk' (CFSG.pCore 2 ↥(Lp D p)) ⟨m, hmL⟩) = 1 := hcenter
  have hmem : (⟨m, hmL⟩ : ↥(Lp D p)) ∈ CFSG.pCore 2 ↥(Lp D p) :=
    (QuotientGroup.eq_one_iff _).mp hmk
  exact Subgroup.mem_map.mpr ⟨⟨m, hmL⟩, hmem, rfl⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
