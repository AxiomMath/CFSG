module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyTwoSteps
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRankBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PRankModPCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4CartanPlus
public import CFSG.GroupTheory.CoprimeCentralizerCover
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GF2Type.Smith1979.IdxFourCoset
public import CFSG.GroupTheory.PGroup.OmegaComm
public import CFSG.GroupTheory.SylowNormalElements
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S3Asch
public import CFSG.LargeExtraspecial.S5Defs
public import CFSG.LargeExtraspecial.S5Gen2
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5FusionTwoBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyTwo
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.HMathieuStatements
public import CFSG.Quasithin.Background.HSecQuot
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.H13.StatementsL6
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS4
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Lie
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatTen
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QConj
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QHat
public import CFSG.Quasithin.Vol2.Ch6Defs
public import CFSG.Quasithin.Vol2.Ch6Vocab
public import CFSG.Quasithin.Vol2.Ch7Inputs
public import CFSG.Quasithin.Vol2.Ch7Setup
public import CFSG.Quasithin.Vol2.Ch8Inputs
public import CFSG.Quasithin.Vol2.Ch8InputsB
public import CFSG.Quasithin.Vol2.Ch8Sec2Defs
public import CFSG.Quasithin.Vol2.Ch8Sec2Statements
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartTwo.KFacts.K72OutL2
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.StabilizerLift
public import CFSG.Timmesfeld.Bridge.RootSetsConn5
public import CFSG.Timmesfeld.Moufang.Three
public import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise commutatorElement

local notation "pRank" => CFSG.Open.pRank

variable {G : Type} [Group G] [Finite G]

theorem Ctx17_42.false_of_pRank_add_two_le {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G} (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (h49 : R17_49At D V₀ V) (h51 : R17_51At D V₀ V) (h76 : F07.R76 D)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h638 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_38 D)
    (hZ : Subgroup.center (Bar2 L) = ⊥)
    (hOut : IsCyclic (Outer (Bar2 L)))
    {r : ℕ} {R : Subgroup G} (hr : r.Prime) (hr2 : r ≠ 2) (hrp : r ≠ p)
    (hrdvd : r ∣ 2 ^ n - 1) (hR : CFSG.ABGLocalTools.IsSylowOf r R C)
    (hRr : 2 ≤ pRank r R)
    (hgap : pRank p (⊤ : Subgroup (Bar2 L)) + 2 ≤ pRank p D.M) : False := by
  have hp : p.Prime := (D.sig_prime p ctx.p_mem).1
  have hp2 : p ≠ 2 := (D.sig_prime p ctx.p_mem).2
  have hLM : L ≤ D.M := ctx.mem_calC.1.le
  have hMN : D.M ≤ Subgroup.normalizer (L : Set G) := seventeen_fiftyone_normalizer_le h49 ctx
  have hOp : UC22.F10.OpRes p D.M = D.M := h638 p hp hp2 (Or.inl ctx.p_mem)
  have hRL : R ≤ L := hR.le.trans ctx.cartan.1
  have hbound := pRank_le_pRank_bar2_add_pRank_centOverO2 hLM hMN hZ hOut hp hp2 hOp
  have hcover := pRank_centOverO2_le_pRank_inf_centralizer hLM hMN hp hp2 hr hr2 hrp hRL hR.isPGroup
  have hcent : 2 ≤ pRank p (F08.CentOverO2 D.M L) := by omega
  exact false_of_two_le_pRank_inf_centralizer ctx h51 h76 hSg hr hrdvd hR hRr
    (le_trans hcent hcover)

theorem Ctx17_42.false_of_u4_rank {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G} (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (h49 : R17_49At D V₀ V) (h51 : R17_51At D V₀ V) (h76 : F07.R76 D)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h638 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_38 D)
    (hKT : Inputs1719.K_LieBorelTorus) (hK9 : Inputs1719.K_U4CartanPlus)
    (hZ : Subgroup.center (Bar2 L) = ⊥)
    (hOut : IsCyclic (Outer (Bar2 L))) (hU4 : IsU4 (Bar2 L) n) (hq : 2 < 2 ^ n)
    (hpdvd : p ∣ 2 ^ n + 1) {r : ℕ} {R : Subgroup G} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrdvd : r ∣ 2 ^ n - 1) (hR : CFSG.ABGLocalTools.IsSylowOf r R C)
    (hRr : 2 ≤ pRank r R)
    (hrank : pRank p (⊤ : Subgroup (Bar2 L)) < pRank p D.M) : False := by
  classical
  have hp : p.Prime := (D.sig_prime p ctx.p_mem).1
  have hp2 : p ≠ 2 := (D.sig_prime p ctx.p_mem).2
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hLM : L ≤ D.M := ctx.mem_calC.1.le
  have hMN : D.M ≤ Subgroup.normalizer (L : Set G) := seventeen_fiftyone_normalizer_le h49 ctx
  have hOp : UC22.F10.OpRes p D.M = D.M := h638 p hp hp2 (Or.inl ctx.p_mem)
  have hRL : R ≤ L := hR.le.trans ctx.cartan.1
  have hshape : IsU4 (Bar2 L) n ∨ IsSp4 (Bar2 L) n ∨ IsG2 (Bar2 L) n := Or.inl hU4
  haveI : ((pCoreOf 2 L).subgroupOf C).Normal :=
    seventeen_fiftyone_cartan_pCore_normal h49 ctx
  have hSbar : IsSylowTwoOf (((D.T ⊓ L).subgroupOf L).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) ⊤ := seventeen_fiftyone_sylow_bar h49 ctx
  have hpNq : p ∣ Nat.card (TauCeti.Subgroup.normalizerQuotient
      (((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))) :=
    hK9 (Bar2 L) n hU4 hq _ hSbar p hp hpdvd
  obtain ⟨e⟩ := seventeen_fiftyone_cartan_normalizer_equiv h49 ctx hZ
  have hpQuot : p ∣ Nat.card (↥C ⧸ (pCoreOf 2 L).subgroupOf C) := by
    rw [Nat.card_congr e.toEquiv]
    exact hpNq
  have hpC : p ∣ Nat.card ↥C := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((pCoreOf 2 L).subgroupOf C)]
    exact dvd_mul_of_dvd_left hpQuot _
  have hcommC := (seventeen_fiftyone_cartan_comm_card hKT h49 ctx hZ hshape hq hr hrdvd).1
  have hcomm : ⁅C, R⁆ ≤ pCoreOf 2 L := by
    rw [Subgroup.commutator_le]
    intro c hc r hrR
    rw [commutatorElement_def]
    have hrC : r ∈ C := hR.le hrR
    have hq1 : (QuotientGroup.mk' ((pCoreOf 2 L).subgroupOf C))
        (⁅(⟨c, hc⟩ : ↥C), (⟨r, hrC⟩ : ↥C)⁆) = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hcommC.is_comm.comm _ _)
    have hmem : ⁅(⟨c, hc⟩ : ↥C), (⟨r, hrC⟩ : ↥C)⁆ ∈ (pCoreOf 2 L).subgroupOf C :=
      (QuotientGroup.eq_one_iff _).mp hq1
    have hmem' : ((⁅(⟨c, hc⟩ : ↥C), (⟨r, hrC⟩ : ↥C)⁆ : ↥C) : G) ∈ pCoreOf 2 L :=
      Subgroup.mem_subgroupOf.mp hmem
    rwa [show ((⁅(⟨c, hc⟩ : ↥C), (⟨r, hrC⟩ : ↥C)⁆ : ↥C) : G) = c * r * c⁻¹ * r⁻¹ from by
      simp [commutatorElement_def]] at hmem'
  have hQleC : pCoreOf 2 L ≤ C := by
    rw [← oinf_eq_pCoreOf ctx.mem_calC.2.2 hZ]
    exact ctx.cartan.2.1
  have hQC : R ≤ Subgroup.normalizer (C : Set G) :=
    hR.le.trans Subgroup.le_normalizer
  have hRN : R ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hRL.trans (Subgroup.le_normalizer.trans
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.normalizer_le_normalizer_pCoreOf L))
  have hQr : ¬ r ∣ Nat.card (pCoreOf 2 L) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.isPGroup_pCoreOf L) hr hr2
  have hQp : ¬ p ∣ Nat.card (pCoreOf 2 L) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.isPGroup_pCoreOf L) hp hp2
  obtain ⟨P, hPsyl, hPcent⟩ :=
    CFSG.GroupTheory.exists_isSylowOf_le_centralizer_of_commutator_le
      (p := r) (q := p) (X := C) (N := pCoreOf 2 L) (R := R)
      hQleC hQC hRN hR.isPGroup hQr hcomm hQp
  have hfacpos : 0 < (Nat.card ↥C).factorization p :=
    hp.factorization_pos_of_dvd Nat.card_pos.ne' hpC
  have hPcard : Nat.card P = p ^ (Nat.card ↥C).factorization p := hPsyl.card_eq
  have hpP : p ∣ Nat.card P := by
    rw [hPcard]
    exact dvd_pow_self p hfacpos.ne'
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) p hpP
  have hyG : orderOf (y : G) = p := (Subgroup.orderOf_coe y).trans hy
  have hyC : (y : G) ∈ C := hPsyl.le y.2
  have hyL : (y : G) ∈ L := ctx.cartan.1 hyC
  have hyCR : (y : G) ∈ Subgroup.centralizer (R : Set G) := hPcent y.2
  obtain ⟨S, hSle, hSp, hSne, hSc⟩ :=
    exists_isPGroup_le_centralizer_centOverO2 hLM hMN hZ hOut hp hp2 hOp hrank
      hr hr2 hRL hR.isPGroup
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hSp
  have hkpos : k ≠ 0 := by
    intro h0
    apply hSne
    rw [Subgroup.eq_bot_iff_card, hk, h0]
    norm_num
  have hpS : p ∣ Nat.card S := by
    rw [hk]
    exact dvd_pow_self p hkpos
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥S) p hpS
  have hzG : orderOf (z : G) = p := (Subgroup.orderOf_coe z).trans hz
  have hzCen := mem_centOverO2_iff.mp (hSle z.2)
  refine false_of_two_le_pRank_inf_centralizer ctx h51 h76 hSg hr hrdvd hR hRr ?_
  have hHN : (D.M ⊓ Subgroup.centralizer (R : Set G)) ≤ Subgroup.normalizer (L : Set G) :=
    inf_le_left.trans hMN
  exact two_le_pRank_of_centralizing_mod_pCore (L := L)
    (H := D.M ⊓ Subgroup.centralizer (R : Set G)) hp hp2 hZ hHN
    ⟨hLM hyL, hyCR⟩ ⟨hzCen.1, hSc z.2⟩ hyL hyG hzG hzCen.2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
