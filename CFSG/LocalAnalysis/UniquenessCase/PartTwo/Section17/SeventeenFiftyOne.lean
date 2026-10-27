module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyTwo
public import CFSG.Quasithin.Background.RonanD33
public import TauCeti.GroupTheory.QuotientGroup.MulAut
public import CFSG.GroupTheory.NormalizerQuotientQuotient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LieBorelTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.RootLine
public import CFSG.Quasithin.H13.AS91Sec4SevenN
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InPStarCriteria
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThree
public import CFSG.GroupTheory.SylowHallIndex
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5FusionTwoAction
public import CFSG.Timmesfeld.Bridge.RootSetsConn6
public import CFSG.Quasithin.Vol2.Ch12Sec6P31LieG
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4CartanRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4CartanRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.G2CartanRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem oinf_eq_pCoreOf {L : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 L)) (hZ : Subgroup.center (Bar2 L) = ⊥) :
    OInf L = pCoreOf 2 L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSRn : (CFSG.solvableRadical ↥L).Normal := CFSG.ABGLocalTools.solvableRadical_normal
  have hSRs : Group.IsSolvable ↥(CFSG.solvableRadical ↥L) :=
    CFSG.ABGLocalTools.solvableRadical_isSolvable
  let S : Subgroup (Bar2 L) :=
    (CFSG.solvableRadical ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hSn : S.Normal := hSRn.map _ (QuotientGroup.mk'_surjective _)
  have hSs : Group.IsSolvable ↥S :=
    Group.isSolvable_of_surjective
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).subgroupMap_surjective (CFSG.solvableRadical ↥L))
  have hle : S ≤ Subgroup.center (Bar2 L) :=
    CFSG.ComponentClassification.AschbacherTheorem5.FusionTwo.le_center_of_quasisimple hq S hSs
  rw [hZ] at hle
  have h2 : CFSG.solvableRadical ↥L ≤ CFSG.pCore 2 ↥L := by
    intro x hx
    have hxS : QuotientGroup.mk' (CFSG.pCore 2 ↥L) x ∈ S := ⟨x, hx, rfl⟩
    have hSb : S = ⊥ := le_antisymm hle bot_le
    have hxbot : QuotientGroup.mk' (CFSG.pCore 2 ↥L) x ∈ (⊥ : Subgroup (Bar2 L)) :=
      hSb ▸ hxS
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) x = 1 := by
      simpa using hxbot
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have h1 : CFSG.pCore 2 ↥L ≤ CFSG.solvableRadical ↥L :=
    CFSG.Timmesfeld.Bridge.pCore_le_solvableRadical
  unfold OInf
  rw [show CFSG.solvableRadical ↥L = CFSG.pCore 2 ↥L from le_antisymm h2 h1]
  exact (openPCoreOf_eq_map_pCore 2 L)

theorem ctx_L_normal {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G}
    (h49 : R17_49At D V₀ V) (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma) :
    (L.subgroupOf D.M).Normal := by
  have hLM : L ≤ D.M := ctx.mem_calC.1.le
  have hLX : L = X := h49 L X p n l C Dc Gamma ctx
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mpr ?_
  rw [hLX, ctx.X_eq]
  exact TwelveTwentyThree.le_normalizer_conjClosure D.M L

theorem pCoreOf_le_inf_T {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G}
    (h49 : R17_49At D V₀ V) (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma) :
    pCoreOf 2 L ≤ D.T ⊓ L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLM : L ≤ D.M := ctx.mem_calC.1.le
  have hLn : (L.subgroupOf D.M).Normal := ctx_L_normal h49 ctx
  have hTL : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ L) L :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer D.sylowM hLM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn)
  obtain ⟨S, hS⟩ := hTL.exists_sylow_eq_subgroupOf
  have hQS : CFSG.pCore 2 ↥L ≤ (S : Subgroup ↥L) :=
    CFSG.Glauberman.pCore_le_sylow S
  have hQle : pCoreOf 2 L ≤ D.T ⊓ L := by
    rw [openPCoreOf_eq_map_pCore]
    rintro x ⟨y, hy, rfl⟩
    have hyS : y ∈ (S : Subgroup ↥L) := hQS hy
    have hy1 : ((y : ↥L) : G) ∈ (S : Subgroup ↥L).map L.subtype := ⟨y, hyS, rfl⟩
    rw [hS] at hy1
    simpa using hy1
  exact hQle

theorem seventeen_fiftyone_hall_index
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (h49 : R17_49At D V₀ V) (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hZ : Subgroup.center (Bar2 L) = ⊥) :
    ∃ k : ℕ, C.relIndex (L ⊓ normalizer (D.T ⊓ L : Set G)) = 2 ^ k ∧
      (pCoreOf 2 L).relIndex (D.T ⊓ L) = 2 ^ k ∧
      (pCoreOf 2 L).relIndex C =
        (D.T ⊓ L).relIndex (L ⊓ normalizer (D.T ⊓ L : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLM : L ≤ D.M := ctx.mem_calC.1.le
  have hLn : (L.subgroupOf D.M).Normal := ctx_L_normal h49 ctx
  have hOInf : OInf L = pCoreOf 2 L := oinf_eq_pCoreOf ctx.mem_calC.2.2 hZ
  have hQleTL : pCoreOf 2 L ≤ D.T ⊓ L := pCoreOf_le_inf_T h49 ctx
  have hQleC : pCoreOf 2 L ≤ C := hOInf ▸ ctx.cartan.2.1
  have hCL : C ≤ L := ctx.cartan.1
  have hCB : C ≤ L ⊓ normalizer (D.T ⊓ L : Set G) :=
    le_inf hCL ctx.cartan.2.2.1
  have hTLeB : D.T ⊓ L ≤ L ⊓ normalizer (D.T ⊓ L : Set G) :=
    le_inf inf_le_right Subgroup.le_normalizer
  have hQp : IsPGroup 2 (pCoreOf 2 L) := by
    rw [openPCoreOf_eq_map_pCore]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map L.subtype
  have hTLsyl : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ L) L :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer D.sylowM hLM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn)
  have hBsyl : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ L)
      (L ⊓ normalizer (D.T ⊓ L : Set G)) := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hTLeB, hTLsyl.isPGroup, ?_⟩
    have hoddL : ¬ 2 ∣ (D.T ⊓ L).relIndex L :=
      (CFSG.ABGLocalTools.isSylowOf_iff.mp hTLsyl).2.2
    intro h2
    have hmul : (D.T ⊓ L).relIndex (L ⊓ normalizer (D.T ⊓ L : Set G)) *
        (L ⊓ normalizer (D.T ⊓ L : Set G)).relIndex L = (D.T ⊓ L).relIndex L :=
      Subgroup.relIndex_mul_relIndex (D.T ⊓ L) (L ⊓ normalizer (D.T ⊓ L : Set G)) L
        hTLeB inf_le_left
    exact hoddL (hmul ▸ dvd_mul_of_dvd_left h2 _)
  obtain ⟨-, -, -, hodd0, hk0⟩ := ctx.cartan
  obtain ⟨k, hk⟩ := hk0
  have hodd : Odd ((pCoreOf 2 L).relIndex C) := hOInf ▸ hodd0
  obtain ⟨h1, h2⟩ := CFSG.GroupTheory.relIndex_eq_of_isSylow_two hCB hQleC hTLeB
    hQleTL hQp hk hodd hBsyl
  exact ⟨k, hk, h1, h2⟩

theorem seventeen_fiftyone_sup_eq
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (h49 : R17_49At D V₀ V) (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hZ : Subgroup.center (Bar2 L) = ⊥) :
    L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G) = C ⊔ (D.T ⊓ L) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, hQT, hQC⟩ := seventeen_fiftyone_hall_index h49 ctx hZ
  have hOInf : OInf L = pCoreOf 2 L := oinf_eq_pCoreOf ctx.mem_calC.2.2 hZ
  have hodd : Odd ((pCoreOf 2 L).relIndex C) := hOInf ▸ ctx.cartan.2.2.2.1
  have hCL : C ≤ L := ctx.cartan.1
  have hCN : C ≤ normalizer ((D.T ⊓ L : Subgroup G) : Set G) := ctx.cartan.2.2.1
  have hCB : C ≤ L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G) := le_inf hCL hCN
  have hTB : D.T ⊓ L ≤ L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G) :=
    le_inf inf_le_right Subgroup.le_normalizer
  have hsup_le : C ⊔ (D.T ⊓ L) ≤ L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G) :=
    sup_le hCB hTB
  have h1 : C.relIndex (C ⊔ (D.T ⊓ L)) *
      (C ⊔ (D.T ⊓ L)).relIndex (L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G)) =
      C.relIndex (L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G)) :=
    Subgroup.relIndex_mul_relIndex C (C ⊔ (D.T ⊓ L))
      (L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G)) le_sup_left hsup_le
  have h2 : (D.T ⊓ L).relIndex (C ⊔ (D.T ⊓ L)) *
      (C ⊔ (D.T ⊓ L)).relIndex (L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G)) =
      (D.T ⊓ L).relIndex (L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G)) :=
    Subgroup.relIndex_mul_relIndex (D.T ⊓ L) (C ⊔ (D.T ⊓ L))
      (L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G)) le_sup_right hsup_le
  have hdvd2 : (C ⊔ (D.T ⊓ L)).relIndex
      (L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G)) ∣ 2 ^ k := by
    rw [← hk]
    exact ⟨_, h1.symm.trans (mul_comm _ _)⟩
  have hdvdodd : (C ⊔ (D.T ⊓ L)).relIndex
      (L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G)) ∣ (pCoreOf 2 L).relIndex C := by
    rw [hQC]
    exact ⟨_, h2.symm.trans (mul_comm _ _)⟩
  have hcop : Nat.Coprime (2 ^ k) ((pCoreOf 2 L).relIndex C) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have hd1 : (C ⊔ (D.T ⊓ L)).relIndex
      (L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G)) = 1 := by
    have hg : (C ⊔ (D.T ⊓ L)).relIndex
        (L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G)) ∣
        Nat.gcd (2 ^ k) ((pCoreOf 2 L).relIndex C) := Nat.dvd_gcd hdvd2 hdvdodd
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at hg
    exact Nat.dvd_one.mp hg
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hd1) hsup_le

theorem seventeen_fiftyone_inf_eq
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (h49 : R17_49At D V₀ V) (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hZ : Subgroup.center (Bar2 L) = ⊥) :
    C ⊓ (D.T ⊓ L) = pCoreOf 2 L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, hQT, hQC⟩ := seventeen_fiftyone_hall_index h49 ctx hZ
  have hOInf : OInf L = pCoreOf 2 L := oinf_eq_pCoreOf ctx.mem_calC.2.2 hZ
  have hsup := seventeen_fiftyone_sup_eq h49 ctx hZ
  have hCL : C ≤ L := ctx.cartan.1
  have hCN : C ≤ normalizer ((D.T ⊓ L : Subgroup G) : Set G) := ctx.cartan.2.2.1
  have hQC' : pCoreOf 2 L ≤ C := hOInf ▸ ctx.cartan.2.1
  have hQTL : pCoreOf 2 L ≤ D.T ⊓ L := pCoreOf_le_inf_T h49 ctx
  have hle : pCoreOf 2 L ≤ C ⊓ (D.T ⊓ L) := le_inf hQC' hQTL
  have hcardB : Nat.card ↥(L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G)) =
      C.relIndex (L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G)) * Nat.card ↥C := by
    have h := Subgroup.relIndex_mul_card C (L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G))
    rw [inf_eq_left.mpr (le_inf hCL hCN)] at h
    exact h.symm
  have hcardT : Nat.card ↥(D.T ⊓ L) =
      (pCoreOf 2 L).relIndex (D.T ⊓ L) * Nat.card ↥(pCoreOf 2 L) := by
    have h := Subgroup.relIndex_mul_card (pCoreOf 2 L) (D.T ⊓ L)
    rw [inf_eq_left.mpr hQTL] at h
    exact h.symm
  have hcardC : Nat.card ↥C = (pCoreOf 2 L).relIndex C * Nat.card ↥(pCoreOf 2 L) := by
    have h := Subgroup.relIndex_mul_card (pCoreOf 2 L) C
    rw [inf_eq_left.mpr hQC'] at h
    exact h.symm
  have hcard_sup : Nat.card ↥(C ⊔ (D.T ⊓ L)) * Nat.card ↥(C ⊓ (D.T ⊓ L)) =
      Nat.card ↥C * Nat.card ↥(D.T ⊓ L) :=
    CFSG.Quasithin.H13.AS91.card_sup_mul_card_inf_of_le_normalizer hCN
  have hEq : Nat.card ↥(C ⊔ (D.T ⊓ L)) = 2 ^ k * Nat.card ↥C := by
    rw [← hsup, ← hk]
    exact hcardB
  have hkey : (2 ^ k * Nat.card ↥C) * Nat.card ↥(C ⊓ (D.T ⊓ L)) =
      Nat.card ↥C * (2 ^ k * Nat.card ↥(pCoreOf 2 L)) := by
    rw [← hEq, hcard_sup, hcardT, hQT]
  have h2 : (2 ^ k * Nat.card ↥C) * Nat.card ↥(C ⊓ (D.T ⊓ L)) =
      (2 ^ k * Nat.card ↥C) * Nat.card ↥(pCoreOf 2 L) := by
    calc (2 ^ k * Nat.card ↥C) * Nat.card ↥(C ⊓ (D.T ⊓ L))
        = Nat.card ↥C * (2 ^ k * Nat.card ↥(pCoreOf 2 L)) := hkey
      _ = (2 ^ k * Nat.card ↥C) * Nat.card ↥(pCoreOf 2 L) := by ring
  have hcard : Nat.card ↥(C ⊓ (D.T ⊓ L)) = Nat.card ↥(pCoreOf 2 L) :=
    Nat.eq_of_mul_eq_mul_left (mul_pos (pow_pos (by norm_num) k) Nat.card_pos) h2
  exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).symm

theorem seventeen_fiftyone_sylow_bar
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (h49 : R17_49At D V₀ V) (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma) :
    IsSylowTwoOf (((D.T ⊓ L).subgroupOf L).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLM : L ≤ D.M := ctx.mem_calC.1.le
  have hLn : (L.subgroupOf D.M).Normal := ctx_L_normal h49 ctx
  have hTLsyl : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ L) L :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer D.sylowM hLM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn)
  have hS'sylow : CFSG.ABGLocalTools.IsSylowOf 2 ((D.T ⊓ L).subgroupOf L) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff L]
    convert hTLsyl using 2
    · rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_right]
    · ext x
      simp
  have hS' : IsSylowTwoOf ((D.T ⊓ L).subgroupOf L) ⊤ :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr hS'sylow
  exact CFSG.Quasithin.H13.S126P31.isSylowTwoOf_map_mk' (CFSG.pCore 2 ↥L) hS'

theorem seventeen_fiftyone_cartan_normalizer_equiv
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (h49 : R17_49At D V₀ V) (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hZ : Subgroup.center (Bar2 L) = ⊥) [((pCoreOf 2 L).subgroupOf C).Normal] :
    Nonempty ((↥C ⧸ (pCoreOf 2 L).subgroupOf C) ≃*
      TauCeti.Subgroup.normalizerQuotient
        (((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Subgroup ↥L := CFSG.pCore 2 ↥L
  let S : Subgroup ↥L := (D.T ⊓ L).subgroupOf L
  let Sbar : Subgroup (Bar2 L) := S.map (QuotientGroup.mk' Q)
  have hCL : C ≤ L := ctx.cartan.1
  have hCN : C ≤ Subgroup.normalizer (((D.T ⊓ L : Subgroup G) : Set G)) := ctx.cartan.2.2.1
  have hQleTL : pCoreOf 2 L ≤ D.T ⊓ L := pCoreOf_le_inf_T h49 ctx
  have hQS : Q ≤ S := by
    rw [show Q = (pCoreOf 2 L).subgroupOf L from (CFSG.openPCoreOf_subgroupOf 2 L).symm]
    exact Subgroup.subgroupOf_mono _ hQleTL
  have hsup : L ⊓ Subgroup.normalizer (((D.T ⊓ L : Subgroup G) : Set G)) =
      C ⊔ (D.T ⊓ L) := seventeen_fiftyone_sup_eq h49 ctx hZ
  have hinf : C ⊓ (D.T ⊓ L) = pCoreOf 2 L := seventeen_fiftyone_inf_eq h49 ctx hZ
  have hQnormal : (Q.Normal) := by
    rw [show Q = (pCoreOf 2 L).subgroupOf L from (CFSG.openPCoreOf_subgroupOf 2 L).symm]
    exact (by rw [CFSG.openPCoreOf_subgroupOf 2 L]; infer_instance :
      ((pCoreOf 2 L).subgroupOf L).Normal)
  haveI : (Q.Normal) := hQnormal
  haveI hQCNormal : ((pCoreOf 2 L).subgroupOf C).Normal := by
    constructor
    intro n hn c
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hL : ((pCoreOf 2 L).subgroupOf L).Normal := by
      rw [CFSG.openPCoreOf_subgroupOf 2 L]; infer_instance
    have hnL : (⟨(n : G), hCL n.2⟩ : ↥L) ∈ (pCoreOf 2 L).subgroupOf L := hn
    have hconj := hL.conj_mem (⟨(n : G), hCL n.2⟩ : ↥L) hnL (⟨(c : G), hCL c.2⟩ : ↥L)
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using hconj
  let toN : ↥C →* ↥(Subgroup.normalizer (S : Set ↥L)) := {
    toFun c := ⟨⟨(c : G), hCL c.2⟩, by
      rw [Subgroup.mem_normalizer_iff]
      intro s
      constructor
      · intro hs
        have hsT : (s : G) ∈ D.T := by simpa [S, Subgroup.mem_subgroupOf] using hs
        have hsTL : (s : G) ∈ D.T ⊓ L := ⟨hsT, s.2⟩
        have h := (Subgroup.mem_normalizer_iff.mp (hCN c.2) (s : G)).mp hsTL
        simpa [S, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using h.1
      · intro hs
        have hsG' : (c : G) * (s : G) * (c : G)⁻¹ ∈ D.T ⊓ L := by
          have hsT : (⟨(c : G), hCL c.2⟩ * s * (⟨(c : G), hCL c.2⟩ : ↥L)⁻¹ : ↥L) ∈ S := hs
          have hT : ((⟨(c : G), hCL c.2⟩ * s * (⟨(c : G), hCL c.2⟩ : ↥L)⁻¹ : ↥L) : G) ∈ D.T :=
            (Subgroup.mem_subgroupOf.mp hsT).1
          have hL : (c : G) * (s : G) * (c : G)⁻¹ ∈ L :=
            L.mul_mem (L.mul_mem (hCL c.2) s.2) (L.inv_mem (hCL c.2))
          exact ⟨by simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hT, hL⟩
        have h := (Subgroup.mem_normalizer_iff.mp (hCN c.2) (s : G)).mpr hsG'
        have hsT : (s : G) ∈ D.T := h.1
        simpa [S, Subgroup.mem_subgroupOf] using hsT⟩
    map_one' := by ext; rfl
    map_mul' := by intro a b; ext; rfl }
  let φ : ↥C →* TauCeti.Subgroup.normalizerQuotient S :=
    (TauCeti.Subgroup.normalizerQuotientMk S).comp toN
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨n, rfl⟩ := TauCeti.Subgroup.normalizerQuotientMk_surjective S y
    have hnNorm : ((n : ↥L) : G) ∈
        Subgroup.normalizer (((D.T ⊓ L : Subgroup G) : Set G)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hxL : x ∈ L := hx.2
        have hxS : (⟨x, hxL⟩ : ↥L) ∈ S := by
          simpa [S, Subgroup.mem_subgroupOf] using hx.1
        have h := (Subgroup.mem_normalizer_iff.mp n.2 (⟨x, hxL⟩ : ↥L)).mp hxS
        have hT : (n : G) * x * (n : G)⁻¹ ∈ D.T := (Subgroup.mem_subgroupOf.mp h).1
        have hL : (n : G) * x * (n : G)⁻¹ ∈ L := (Subgroup.mem_subgroupOf.mp h).2
        exact ⟨by simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hT, hL⟩
      · intro hx
        have hxL : x ∈ L := by
          have hx' : (n : G) * x * (n : G)⁻¹ ∈ L := hx.2
          have hnL : (n : G) ∈ L := (n : ↥L).2
          have : (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * (n : G) ∈ L :=
            L.mul_mem (L.mul_mem (L.inv_mem hnL) hx') hnL
          simpa [mul_assoc] using this
        have hxT : (n : G) * x * (n : G)⁻¹ ∈ D.T := hx.1
        have hxS : (⟨(n : G) * x * (n : G)⁻¹, hx.2⟩ : ↥L) ∈ S := by
          simpa [S, Subgroup.mem_subgroupOf] using hxT
        have heq : (⟨(n : G) * x * (n : G)⁻¹, hx.2⟩ : ↥L) =
            (n : ↥L) * (⟨x, hxL⟩ : ↥L) * (n : ↥L)⁻¹ := by
          ext
          simp [Subgroup.coe_mul, Subgroup.coe_inv]
        have hxS' : (n : ↥L) * (⟨x, hxL⟩ : ↥L) * (n : ↥L)⁻¹ ∈ S := by
          rwa [← heq]
        have h := (Subgroup.mem_normalizer_iff.mp n.2 (⟨x, hxL⟩ : ↥L)).mpr hxS'
        exact ⟨by simpa using (Subgroup.mem_subgroupOf.mp h).1, hxL⟩
    have hnB : ((n : ↥L) : G) ∈ C ⊔ (D.T ⊓ L) := by
      rw [← hsup]
      exact ⟨(n : ↥L).2, hnNorm⟩
    let B : Subgroup G := C ⊔ (D.T ⊓ L)
    have hCB : C ≤ B := le_sup_left
    have hSB : (D.T ⊓ L) ≤ B := le_sup_right
    have hS'normal : ((D.T ⊓ L).subgroupOf B).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hSB]
      exact sup_le hCN Subgroup.le_normalizer
    have hsupB : C.subgroupOf B ⊔ (D.T ⊓ L).subgroupOf B = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hCB hSB]
      exact Subgroup.subgroupOf_self B
    let nB : ↥B := ⟨((n : ↥L) : G), hnB⟩
    have hnBtop : nB ∈ C.subgroupOf B ⊔ (D.T ⊓ L).subgroupOf B := by
      rw [hsupB]
      exact Subgroup.mem_top nB
    haveI := hS'normal
    obtain ⟨cB, hcB, sB, hsB, hcs⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := C.subgroupOf B)
        (t := (D.T ⊓ L).subgroupOf B)).mp hnBtop
    have hcC : (cB : G) ∈ C := hcB
    have hsS : (sB : G) ∈ D.T ⊓ L := hsB
    have hcsG : (cB : G) * (sB : G) = ((n : ↥L) : G) := by
      have := congrArg (fun x : ↥B => (x : G)) hcs
      simpa using this
    let cL : ↥L := ⟨(cB : G), hCL hcC⟩
    let sL : ↥L := ⟨(sB : G), hsS.2⟩
    have hcsL : cL * sL = (n : ↥L) := by
      apply Subtype.ext
      exact hcsG
    have hsLS : sL ∈ S := hsS
    let cC : ↥C := ⟨(cB : G), hcC⟩
    let sN : ↥(Subgroup.normalizer (S : Set ↥L)) := ⟨sL, by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact S.mul_mem (S.mul_mem hsLS hx) (S.inv_mem hsLS)
      · intro hx
        have h := S.mul_mem (S.mul_mem (S.inv_mem hsLS) hx) hsLS
        have hx' : sL⁻¹ * (sL * x * sL⁻¹) * sL = x := by group
        rwa [hx'] at h⟩
    have hmul : toN cC * sN = n := by
      apply Subtype.ext
      simpa [toN, sN, cL] using hcsL
    have h2 : TauCeti.Subgroup.normalizerQuotientMk S sN = 1 :=
      (TauCeti.Subgroup.normalizerQuotientMk_eq_one_iff S sN).mpr hsLS
    have h1 : φ cC = TauCeti.Subgroup.normalizerQuotientMk S n := by
      have hmap : TauCeti.Subgroup.normalizerQuotientMk S (toN cC * sN) =
          TauCeti.Subgroup.normalizerQuotientMk S n := by rw [hmul]
      have hmap2 : TauCeti.Subgroup.normalizerQuotientMk S (toN cC) *
          TauCeti.Subgroup.normalizerQuotientMk S sN =
          TauCeti.Subgroup.normalizerQuotientMk S n := by
        rwa [← map_mul]
      rw [h2, mul_one] at hmap2
      simpa [φ] using hmap2
    exact ⟨cC, h1⟩
  have hφker : φ.ker = (pCoreOf 2 L).subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hc
      have h1 : (toN c : ↥L) ∈ S :=
        (TauCeti.Subgroup.normalizerQuotientMk_eq_one_iff S (toN c)).mp hc
      have h2 : (c : G) ∈ D.T ⊓ L := h1
      have h3 : (c : G) ∈ C ⊓ (D.T ⊓ L) := ⟨c.2, h2⟩
      rwa [hinf] at h3
    · intro hc
      have hc' : (c : G) ∈ D.T ⊓ L := hQleTL hc
      exact (TauCeti.Subgroup.normalizerQuotientMk_eq_one_iff S (toN c)).mpr hc'
  let e1 : TauCeti.Subgroup.normalizerQuotient S ≃* TauCeti.Subgroup.normalizerQuotient
      (((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) :=
    CFSG.GroupTheory.normalizerQuotient_quotientEquiv Q S hQS
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).trans e1)⟩

theorem seventeen_fiftyone_omega1p_map_mulEquiv
    {H K : Type} [Group H] [Group K] (p : ℕ) (e : H ≃* K) :
    (F11.Omega1p p ⊤ : Subgroup H).map e.toMonoidHom =
      (F11.Omega1p p ⊤ : Subgroup K) := by
  unfold F11.Omega1p
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨trivial, by rw [← map_pow, hx.2, map_one]⟩
  · intro hy
    refine ⟨e.symm y, ⟨trivial, ?_⟩, by simp⟩
    apply e.injective
    rw [map_pow, e.apply_symm_apply, hy.2, map_one]

private theorem seventeen_fiftyone_r_ne_two {n r : ℕ}
    (hq : 2 < 2 ^ n) (hrdvd : r ∣ 2 ^ n - 1) : r ≠ 2 := by
  intro h2
  have hodd : Odd (2 ^ n - 1) := by
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · simp [h0] at hq
      · exact h0
    obtain ⟨t, ht⟩ : ∃ t, 2 ^ n = 2 * t :=
      ⟨2 ^ (n - 1), by rw [← pow_succ', Nat.sub_add_cancel hn1]⟩
    refine ⟨t - 1, ?_⟩
    rw [ht]
    omega
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2 ▸ hrdvd))

theorem seventeen_fiftyone_cartan_comm_card
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (hKT : Inputs1719.K_LieBorelTorus)
    (h49 : R17_49At D V₀ V) (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hZ : Subgroup.center (Bar2 L) = ⊥) [((pCoreOf 2 L).subgroupOf C).Normal]
    (hshape : IsU4 (Bar2 L) n ∨ IsSp4 (Bar2 L) n ∨ IsG2 (Bar2 L) n)
    (hq : 2 < 2 ^ n) {r : ℕ} (hr : r.Prime) (hrdvd : r ∣ 2 ^ n - 1) :
    IsMulCommutative (↥C ⧸ (pCoreOf 2 L).subgroupOf C) ∧
      Nat.card (F11.Omega1p r (⊤ : Subgroup (↥C ⧸ (pCoreOf 2 L).subgroupOf C))) = r ^ 2 ∧
        Odd (Nat.card (↥C ⧸ (pCoreOf 2 L).subgroupOf C)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := seventeen_fiftyone_cartan_normalizer_equiv h49 ctx hZ
  have hSbar : IsSylowTwoOf
      (((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) ⊤ :=
    seventeen_fiftyone_sylow_bar h49 ctx
  have hOInf : OInf L = pCoreOf 2 L := oinf_eq_pCoreOf ctx.mem_calC.2.2 hZ
  have hoddQ : Odd ((pCoreOf 2 L).relIndex C) := by
    have := ctx.cartan.2.2.2.1
    rwa [hOInf] at this
  have hoddC : Odd (Nat.card (↥C ⧸ (pCoreOf 2 L).subgroupOf C)) := by
    rw [← Subgroup.index_eq_card, ← Subgroup.relIndex_top_right, ← Subgroup.subgroupOf_self C,
      Subgroup.relIndex_subgroupOf (le_refl C)]
    exact hoddQ
  have hnot2 : r ≠ 2 := seventeen_fiftyone_r_ne_two hq hrdvd
  have hcommK : IsMulCommutative
      (TauCeti.Subgroup.normalizerQuotient
        (((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))) := by
    rcases hshape with hU4 | hSp4 | hG2
    · exact (hKT.1 (Bar2 L) n hU4 hq _ hSbar).1
    · exact (hKT.2.1 (Bar2 L) n hSp4 hq _ hSbar).1
    · exact (hKT.2.2 (Bar2 L) n hG2 hq _ hSbar).1
  have hcardK : Nat.card (F11.Omega1p r (⊤ : Subgroup
      (TauCeti.Subgroup.normalizerQuotient
        (((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))))) = r ^ 2 := by
    rcases hshape with hU4 | hSp4 | hG2
    · exact ((hKT.1 (Bar2 L) n hU4 hq _ hSbar).2 r hr hnot2 hrdvd).2.1
    · exact ((hKT.2.1 (Bar2 L) n hSp4 hq _ hSbar).2 r hr hnot2 hrdvd).2.1
    · exact ((hKT.2.2 (Bar2 L) n hG2 hq _ hSbar).2 r hr hnot2 hrdvd).2.1
  refine ⟨?_, ?_, hoddC⟩
  · refine IsMulCommutative.mk ⟨fun a b => ?_⟩
    apply e.injective
    rw [map_mul, map_mul]
    exact hcommK.is_comm.comm (e a) (e b)
  · have hmap := seventeen_fiftyone_omega1p_map_mulEquiv r e
    rw [← hmap, Subgroup.card_map_of_injective e.injective] at hcardK
    exact hcardK

theorem seventeen_fiftyone_cartan_factorization
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (hKT : Inputs1719.K_LieBorelTorus)
    (h49 : R17_49At D V₀ V) (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hZ : Subgroup.center (Bar2 L) = ⊥) [((pCoreOf 2 L).subgroupOf C).Normal]
    (hshape : IsU4 (Bar2 L) n ∨ IsSp4 (Bar2 L) n ∨ IsG2 (Bar2 L) n)
    (hq : 2 < 2 ^ n) {r : ℕ} (hr : r.Prime) (hrdvd : r ∣ 2 ^ n - 1)
    (hnot : ¬ (IsG2 (Bar2 L) n ∧ r = 3)) :
    (Nat.card (Bar2 L)).factorization r =
      (Nat.card (↥C ⧸ (pCoreOf 2 L).subgroupOf C)).factorization r := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := seventeen_fiftyone_cartan_normalizer_equiv h49 ctx hZ
  have hSbar : IsSylowTwoOf
      (((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) ⊤ :=
    seventeen_fiftyone_sylow_bar h49 ctx
  have hnot2 : r ≠ 2 := seventeen_fiftyone_r_ne_two hq hrdvd
  have hfactK : (Nat.card (Bar2 L)).factorization r =
      (Nat.card (TauCeti.Subgroup.normalizerQuotient
        (((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))))).factorization r := by
    rcases hshape with hU4 | hSp4 | hG2
    · exact ((hKT.1 (Bar2 L) n hU4 hq _ hSbar).2 r hr hnot2 hrdvd).2.2
    · exact ((hKT.2.1 (Bar2 L) n hSp4 hq _ hSbar).2 r hr hnot2 hrdvd).2.2
    · exact ((hKT.2.2 (Bar2 L) n hG2 hq _ hSbar).2 r hr hnot2 hrdvd).2.2
        (fun hr3 => hnot ⟨hG2, hr3⟩)
  rw [hfactK, Nat.card_congr e.symm.toEquiv]

theorem seventeen_fiftyone_factorization_bar2 {L : Subgroup G} {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) :
    (Nat.card L).factorization r = (Nat.card (Bar2 L)).factorization r := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQp : IsPGroup 2 (CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hQp)
  have hQr : (Nat.card (CFSG.pCore 2 ↥L)).factorization r = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
      (hr.dvd_of_dvd_pow (hk ▸ hdvd)))
  have hcard : Nat.card ↥L =
      Nat.card (Bar2 L) * Nat.card (CFSG.pCore 2 ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [hcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hQr,
    add_zero]

theorem seventeen_fiftyone_factorization_cartan {C L : Subgroup G} {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) [((pCoreOf 2 L).subgroupOf C).Normal] :
    (Nat.card C).factorization r =
      (Nat.card (↥C ⧸ (pCoreOf 2 L).subgroupOf C)).factorization r := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQp0 : IsPGroup 2 (pCoreOf 2 L) := by
    rw [CFSG.openPCoreOf_eq_map_pCore]
    exact CFSG.pCore_isPGroup.map L.subtype
  have hQp : IsPGroup 2 ((pCoreOf 2 L).subgroupOf C) := by
    rw [← Subgroup.comap_subtype]
    exact hQp0.comap_subtype
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hQp)
  have hQr : (Nat.card ((pCoreOf 2 L).subgroupOf C)).factorization r = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hdvd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
      (hr.dvd_of_dvd_pow (hk ▸ hdvd)))
  have hcard : Nat.card ↥C = Nat.card (↥C ⧸ (pCoreOf 2 L).subgroupOf C) *
      Nat.card ((pCoreOf 2 L).subgroupOf C) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [hcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, hQr,
    add_zero]

theorem seventeen_fiftyone_R_sylow_L
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    [((pCoreOf 2 L).subgroupOf C).Normal]
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf r R C)
    (hfact : (Nat.card (Bar2 L)).factorization r =
      (Nat.card (↥C ⧸ (pCoreOf 2 L).subgroupOf C)).factorization r) :
    CFSG.ABGLocalTools.IsSylowOf r R L := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hCL : C ≤ L := ctx.cartan.1
  have hRL : R ≤ L := hR.le.trans hCL
  have hfacC := seventeen_fiftyone_factorization_cartan (C := C) (L := L) hr hr2
  have hfacL := seventeen_fiftyone_factorization_bar2 (L := L) hr hr2
  have hcard : Nat.card R = r ^ (Nat.card L).factorization r := by
    rw [hR.card_eq, hfacC, ← hfact, ← hfacL]
  exact CFSG.ABGLocalTools.isSylowOf_of_card hRL hcard

theorem seventeen_fiftyone_R_abelian
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    [((pCoreOf 2 L).subgroupOf C).Normal]
    {r : ℕ} (hr : r.Prime) (hq : 2 < 2 ^ n) (hrdvd : r ∣ 2 ^ n - 1) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf r R C)
    (hcomm : IsMulCommutative (↥C ⧸ (pCoreOf 2 L).subgroupOf C)) :
    IsMulCommutative R ∧ (∀ x ∈ F11.Omega1p r R, x ^ r = 1) ∧
      F11.Omega1p r R ≤ C := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCL : C ≤ L := ctx.cartan.1
  let Qc : Subgroup ↥C := (pCoreOf 2 L).subgroupOf C
  let q : ↥C →* (↥C ⧸ Qc) := QuotientGroup.mk' Qc
  have hr2 : r ≠ 2 := seventeen_fiftyone_r_ne_two hq hrdvd
  have hRQ : R ⊓ pCoreOf 2 L = ⊥ := by
    have hQp : IsPGroup 2 (pCoreOf 2 L) := by
      rw [CFSG.openPCoreOf_eq_map_pCore]
      exact CFSG.pCore_isPGroup.map L.subtype
    exact (IsPGroup.disjoint_of_ne r 2 hr2 R (pCoreOf 2 L) hR.isPGroup hQp).eq_bot
  have hRcomm : IsMulCommutative R := by
    refine IsMulCommutative.mk ⟨fun x y => ?_⟩
    have hcommut : ((x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹) ∈ R ⊓ pCoreOf 2 L := by
      refine ⟨?_, ?_⟩
      · have h : ((x : G) * (y : G)) * ((x : G)⁻¹ * (y : G)⁻¹) ∈ R :=
          R.mul_mem (R.mul_mem x.2 y.2) (R.mul_mem (R.inv_mem x.2) (R.inv_mem y.2))
        simpa [mul_assoc] using h
      · have hq1 : q (⁅(⟨(x : G), hR.le x.2⟩ : ↥C), (⟨(y : G), hR.le y.2⟩ : ↥C)⁆) = 1 := by
          rw [map_commutatorElement]
          exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm.is_comm.comm _ _)
        have hmemQc : (⁅(⟨(x : G), hR.le x.2⟩ : ↥C), (⟨(y : G), hR.le y.2⟩ : ↥C)⁆) ∈ Qc :=
          (QuotientGroup.eq_one_iff _).mp hq1
        have hc : ((⁅(⟨(x : G), hR.le x.2⟩ : ↥C), (⟨(y : G), hR.le y.2⟩ : ↥C)⁆ : ↥C) : G) =
            ((x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹) := by
          simp [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
        simpa [Qc, Subgroup.mem_subgroupOf, hc] using hmemQc
    have h1 : ((x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹) = 1 := by
      have h2 : ((x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹) ∈ (⊥ : Subgroup G) := by
        rw [← hRQ]
        exact hcommut
      simpa using h2
    apply Subtype.ext
    calc (x : G) * (y : G) = ((x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹) * ((y : G) * (x : G)) := by
          group
      _ = 1 * ((y : G) * (x : G)) := by rw [h1]
      _ = (y : G) * (x : G) := one_mul _
  have hexp : ∀ z ∈ F11.Omega1p r R, z ^ r = 1 := by
    intro z hz
    have hmem := hz
    unfold F11.Omega1p at hz
    exact (Subgroup.closure_induction (p := fun w _ => w ∈ R ∧ w ^ r = 1)
      (by rintro w ⟨hwR, hwr⟩; exact ⟨hwR, hwr⟩)
      ⟨R.one_mem, one_pow r⟩
      (by
        intro a b _ _ ha hb
        refine ⟨R.mul_mem ha.1 hb.1, ?_⟩
        have hc : Commute a b :=
          congrArg (fun z : ↥R => (z : G)) (hRcomm.is_comm.comm ⟨a, ha.1⟩ ⟨b, hb.1⟩)
        rw [hc.mul_pow, ha.2, hb.2, one_mul])
      (by
        intro a _ ha
        refine ⟨R.inv_mem ha.1, ?_⟩
        rw [inv_pow, ha.2, inv_one]) hz).2
  refine ⟨hRcomm, hexp, ?_⟩
  have hΩR : F11.Omega1p r R ≤ R :=
    (Subgroup.closure_le R).mpr (by rintro z ⟨hz, -⟩; exact hz)
  exact hΩR.trans hR.le

theorem seventeen_fiftyone_R_omega1p_card
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    [((pCoreOf 2 L).subgroupOf C).Normal]
    {r : ℕ} (hr : r.Prime) (hq : 2 < 2 ^ n) (hrdvd : r ∣ 2 ^ n - 1) {R : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf r R C)
    (hcomm : IsMulCommutative (↥C ⧸ (pCoreOf 2 L).subgroupOf C))
    (hcardOmega : Nat.card (F11.Omega1p r (⊤ : Subgroup
      (↥C ⧸ (pCoreOf 2 L).subgroupOf C))) = r ^ 2) :
    r ^ 2 ≤ Nat.card (F11.Omega1p r R) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCL : C ≤ L := ctx.cartan.1
  let Qc : Subgroup ↥C := (pCoreOf 2 L).subgroupOf C
  let Rc : Subgroup ↥C := R.subgroupOf C
  let q : ↥C →* (↥C ⧸ Qc) := QuotientGroup.mk' Qc
  let Rbar : Subgroup (↥C ⧸ Qc) := Rc.map q
  have hr2 : r ≠ 2 := seventeen_fiftyone_r_ne_two hq hrdvd
  have hRQ : R ⊓ pCoreOf 2 L = ⊥ := by
    have hQp : IsPGroup 2 (pCoreOf 2 L) := by
      rw [CFSG.openPCoreOf_eq_map_pCore]
      exact CFSG.pCore_isPGroup.map L.subtype
    exact (IsPGroup.disjoint_of_ne r 2 hr2 R (pCoreOf 2 L) hR.isPGroup hQp).eq_bot
  have hRcQc : Rc ⊓ Qc = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hx' : (x : G) ∈ R ⊓ pCoreOf 2 L := ⟨hx.1, hx.2⟩
    rw [hRQ, Subgroup.mem_bot] at hx'
    exact Subtype.ext hx'
  have hqinj : ∀ x y : ↥Rc, q (x : ↥C) = q (y : ↥C) → x = y := by
    intro x y hxy
    have hmem : ((x : ↥C) * (y : ↥C)⁻¹) ∈ Qc := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (((x * y⁻¹ : ↥Rc) : ↥Rc) : ↥C) = 1
      rw [show (((x * y⁻¹ : ↥Rc) : ↥Rc) : ↥C) = (x : ↥C) * (y : ↥C)⁻¹ from rfl,
        map_mul, map_inv, hxy, mul_inv_cancel]
    have hmemR : ((x : ↥C) * (y : ↥C)⁻¹) ∈ Rc :=
      Rc.mul_mem x.2 (Rc.inv_mem y.2)
    have hbot : ((x : ↥C) * (y : ↥C)⁻¹) ∈ (⊥ : Subgroup ↥C) := by
      rw [← hRcQc]
      exact ⟨hmemR, hmem⟩
    have h1 : (x : ↥C) * (y : ↥C)⁻¹ = 1 := by simpa using hbot
    exact Subtype.ext (mul_inv_eq_one.mp h1)
  have hcardRbar : Nat.card Rbar = Nat.card Rc := by
    let f : ↥Rc → ↥Rbar := fun x => ⟨q (x : ↥C), ⟨x, x.2, rfl⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro x y hxy
        apply hqinj x y
        exact congrArg Subtype.val hxy
      · rintro ⟨y, hy⟩
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
        exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
    exact Nat.card_congr (Equiv.ofBijective f hf).symm
  have hcardRc : Nat.card Rc = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR.le).toEquiv
  have hfacC : (Nat.card C).factorization r =
      (Nat.card (↥C ⧸ (pCoreOf 2 L).subgroupOf C)).factorization r :=
    seventeen_fiftyone_factorization_cartan (C := C) (L := L) hr hr2
  have hRbarCard : Nat.card Rbar = r ^
      (Nat.card (↥C ⧸ (pCoreOf 2 L).subgroupOf C)).factorization r := by
    calc Nat.card Rbar = Nat.card Rc := hcardRbar
      _ = Nat.card R := hcardRc
      _ = r ^ (Nat.card C).factorization r := hR.card_eq
      _ = r ^ (Nat.card (↥C ⧸ (pCoreOf 2 L).subgroupOf C)).factorization r := by rw [hfacC]
  have hRbarCard' : Nat.card Rbar = r ^
      (Nat.card (⊤ : Subgroup (↥C ⧸ Qc))).factorization r := by
    simpa using hRbarCard
  have hRbarSylow : CFSG.ABGLocalTools.IsSylowOf r Rbar (⊤ : Subgroup (↥C ⧸ Qc)) :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_top hRbarCard'
  have hOmegaTop : F11.Omega1p r (⊤ : Subgroup (↥C ⧸ Qc)) = F11.Omega1p r Rbar := by
    apply le_antisymm
    · unfold F11.Omega1p
      intro y hy
      refine Subgroup.closure_induction
        (p := fun z _ => z ∈ F11.Omega1p r Rbar) ?mem ?one ?mul ?inv hy
      · rintro z ⟨-, hzr⟩
        let Z : Subgroup (↥C ⧸ Qc) := Subgroup.zpowers z
        have hzz : IsPGroup r Z :=
          CFSG.ABGLocalTools.isPGroup_zpowers_of_pow_eq_one hzr
        have hsup : IsPGroup r ↥(Rbar ⊔ Z) :=
          hRbarSylow.isPGroup.to_sup_of_normal_right hzz
        have heq : Rbar ⊔ Z = Rbar :=
          CFSG.ABGLocalTools.IsSylowOf.eq_of_le hRbarSylow le_sup_left le_top hsup
        have hz : z ∈ Rbar ⊔ Z :=
          Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
        rw [heq] at hz
        exact Subgroup.subset_closure ⟨hz, hzr⟩
      · exact (F11.Omega1p r Rbar).one_mem
      · intro a b _ _ ha hb
        exact (F11.Omega1p r Rbar).mul_mem ha hb
      · intro a _ ha
        exact (F11.Omega1p r Rbar).inv_mem ha
    · unfold F11.Omega1p
      refine Subgroup.closure_mono ?_
      rintro y ⟨hyR, hyr⟩
      exact ⟨trivial, hyr⟩
  have hmapOmega : (F11.Omega1p r Rc).map q = F11.Omega1p r (⊤ : Subgroup (↥C ⧸ Qc)) := by
    have hmapRbar : (F11.Omega1p r Rc).map q = F11.Omega1p r Rbar := by
      unfold F11.Omega1p
      rw [MonoidHom.map_closure]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨hxR, hxr⟩, rfl⟩
        exact ⟨⟨x, hxR, rfl⟩, by rw [← map_pow, hxr, map_one]⟩
      · rintro ⟨hyRbar, hyr⟩
        obtain ⟨x, hxRc, hxy⟩ := Subgroup.mem_map.mp hyRbar
        have hxpow : x ^ r = 1 := by
          have hmem : q (x ^ r) = 1 := by
            rw [map_pow, hxy, hyr]
          have hmem' : x ^ r ∈ Qc := (QuotientGroup.eq_one_iff _).mp hmem
          have hmemR : x ^ r ∈ Rc := Rc.pow_mem hxRc r
          have hbot : x ^ r ∈ (⊥ : Subgroup ↥C) := by
            rw [← hRcQc]
            exact ⟨hmemR, hmem'⟩
          simpa using hbot
        exact ⟨x, ⟨hxRc, hxpow⟩, hxy⟩
    rw [hmapRbar, hOmegaTop]
  have hcardMap : Nat.card (F11.Omega1p r Rc) =
      Nat.card ((F11.Omega1p r Rc).map q) := by
    let f : ↥(F11.Omega1p r Rc) → ↥((F11.Omega1p r Rc).map q) :=
      fun x => ⟨q (x : ↥C), ⟨x, x.2, rfl⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro x y hxy
        have hxy' : q (x : ↥C) = q (y : ↥C) := congrArg Subtype.val hxy
        have hxR : (x : ↥C) ∈ Rc := (Subgroup.closure_le Rc).mpr
          (by rintro z ⟨hz, -⟩; exact hz) x.2
        have hyR : (y : ↥C) ∈ Rc := (Subgroup.closure_le Rc).mpr
          (by rintro z ⟨hz, -⟩; exact hz) y.2
        have h1 : (⟨(x : ↥C), hxR⟩ : ↥Rc) = ⟨(y : ↥C), hyR⟩ := hqinj _ _ hxy'
        exact Subtype.ext (congrArg (fun z : ↥Rc => (z : ↥C)) h1)
      · rintro ⟨y, hy⟩
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
        exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
    exact Nat.card_congr (Equiv.ofBijective f hf)
  have hbridge : (F11.Omega1p r Rc).map C.subtype = F11.Omega1p r R := by
    unfold F11.Omega1p
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨hyR, hyr⟩, rfl⟩
      refine ⟨hyR, ?_⟩
      have hyrG : (((y : ↥C) : G) ^ r) = 1 := by
        simpa using congrArg C.subtype hyr
      simpa using hyrG
    · intro hx
      have hxRc : (⟨x, hR.le hx.1⟩ : ↥C) ∈ Rc := by
        rw [Subgroup.mem_subgroupOf]
        exact hx.1
      have hxr : (⟨x, hR.le hx.1⟩ : ↥C) ^ r = 1 := by
        exact Subtype.ext (by simpa using hx.2)
      exact ⟨⟨x, hR.le hx.1⟩, ⟨hxRc, hxr⟩, rfl⟩
  have hcardG : Nat.card (F11.Omega1p r R) = Nat.card (F11.Omega1p r Rc) := by
    rw [← hbridge, Subgroup.card_map_of_injective C.subtype_injective]
  rw [hcardG, hcardMap, hmapOmega, hcardOmega]

theorem seventeen_fiftyone_normalizer_le {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G}
    (h49 : R17_49At D V₀ V) (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma) :
    D.M ≤ Subgroup.normalizer (L : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer ctx.mem_calC.1.le).mp
    (ctx_L_normal h49 ctx)

theorem seventeen_fiftyone_omega1p_isPGroup
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (h49 : R17_49At D V₀ V) (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hZ : Subgroup.center (Bar2 L) = ⊥)
    (hshape : IsU4 (Bar2 L) n ∨ IsSp4 (Bar2 L) n ∨ IsG2 (Bar2 L) n)
    (hKT : Inputs1719.K_LieBorelTorus) (hq : 2 < 2 ^ n)
    [((pCoreOf 2 L).subgroupOf C).Normal]
    {r : ℕ} (hr : r.Prime) (hrdvd : r ∣ 2 ^ n - 1)
    {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf r R C) :
    IsPGroup r (F11.Omega1p r R) := by
  have hcomm := (seventeen_fiftyone_cartan_comm_card hKT h49 ctx hZ hshape hq hr hrdvd).1
  have hcardOmega := (seventeen_fiftyone_cartan_comm_card hKT h49 ctx hZ hshape hq hr hrdvd).2.1
  obtain ⟨-, hXexp, -⟩ := seventeen_fiftyone_R_abelian ctx hr hq hrdvd hR hcomm
  haveI : Fact r.Prime := ⟨hr⟩
  refine IsPGroup.iff_orderOf.mpr ?_
  intro x
  have hx : x ^ r = 1 := Subtype.ext (by simpa using hXexp (x : G) x.2)
  have hdvd : orderOf x ∣ r := orderOf_dvd_of_pow_eq_one hx
  rcases (Nat.dvd_prime hr).mp hdvd with h | h
  · exact ⟨0, by rw [h]; simp⟩
  · exact ⟨1, by rw [h, pow_one]⟩

private noncomputable def seventeen_fiftyone_toNormalizer (D : Data G) (L : Subgroup G) :
    ↥(L ⊓ Subgroup.normalizer (((D.T ⊓ L : Subgroup G) : Set G))) →*
      ↥(Subgroup.normalizer (((D.T ⊓ L).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Set (Bar2 L))) :=
  MonoidHom.codRestrict
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp
      (Subgroup.inclusion (inf_le_left : L ⊓ Subgroup.normalizer
        (((D.T ⊓ L : Subgroup G) : Set G)) ≤ L)))
    (Subgroup.normalizer (((D.T ⊓ L).subgroupOf L).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Set (Bar2 L)))
    (fun b => by
      have hbL : (b : G) ∈ L := (Subgroup.mem_inf.mp b.2).1
      have hbN : (b : G) ∈ Subgroup.normalizer (((D.T ⊓ L : Subgroup G) : Set G)) :=
        (Subgroup.mem_inf.mp b.2).2
      have hbS : (⟨(b : G), hbL⟩ : ↥L) ∈
          Subgroup.normalizer ((D.T ⊓ L).subgroupOf L : Set ↥L) := by
        rw [Subgroup.mem_normalizer_iff]
        intro s
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        have hconj : (((⟨(b : G), hbL⟩ : ↥L) * s * (⟨(b : G), hbL⟩ : ↥L)⁻¹ : ↥L) : G) =
            (b : G) * (s : G) * (b : G)⁻¹ := by
          simp [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hconj]
        exact Subgroup.mem_normalizer_iff.mp hbN (s : G)
      exact Subgroup.le_normalizer_map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
        (Subgroup.mem_map_of_mem _ hbS))

private theorem seventeen_fiftyone_toNormalizer_coe (D : Data G) (L : Subgroup G)
    (b : ↥(L ⊓ Subgroup.normalizer (((D.T ⊓ L : Subgroup G) : Set G)))) :
    ((seventeen_fiftyone_toNormalizer D L b :
      ↥(Subgroup.normalizer (((D.T ⊓ L).subgroupOf L).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Set (Bar2 L)))) : Bar2 L) =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨(b : G), (Subgroup.mem_inf.mp b.2).1⟩ := rfl

private noncomputable def seventeen_fiftyone_rhoB (D : Data G) (L : Subgroup G) :
    ↥(L ⊓ Subgroup.normalizer (((D.T ⊓ L : Subgroup G) : Set G))) →*
      TauCeti.Subgroup.normalizerQuotient
        (((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) :=
  (TauCeti.Subgroup.normalizerQuotientMk _).comp (seventeen_fiftyone_toNormalizer D L)

private theorem seventeen_fiftyone_rhoB_ker (D : Data G) (L : Subgroup G)
    (hQU : CFSG.pCore 2 ↥L ≤ (D.T ⊓ L).subgroupOf L) :
    (seventeen_fiftyone_rhoB D L).ker = (D.T ⊓ L).subgroupOf
      (L ⊓ Subgroup.normalizer (((D.T ⊓ L : Subgroup G) : Set G))) := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hbL : (b : G) ∈ L := (Subgroup.mem_inf.mp b.2).1
  constructor
  · intro hb
    change (TauCeti.Subgroup.normalizerQuotientMk
      (((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))
        (seventeen_fiftyone_toNormalizer D L b)) = 1 at hb
    have hb2 : ((seventeen_fiftyone_toNormalizer D L b : ↥(Subgroup.normalizer
        (((D.T ⊓ L).subgroupOf L).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Set (Bar2 L)))) : Bar2 L) ∈
        ((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
      (TauCeti.Subgroup.normalizerQuotientMk_eq_one_iff _ _).mp hb
    obtain ⟨u, hu, hqu⟩ := Subgroup.mem_map.mp hb2
    have hqbu : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨(b : G), hbL⟩ =
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) u := hqu.symm
    have hmemQ : (⟨(b : G), hbL⟩ : ↥L) * u⁻¹ ∈ CFSG.pCore 2 ↥L := by
      have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
          ((⟨(b : G), hbL⟩ : ↥L) * u⁻¹) = 1 := by
        rw [map_mul, map_inv, hqbu, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp (by simpa [QuotientGroup.mk'_apply] using h1)
    have hmemU : (⟨(b : G), hbL⟩ : ↥L) * u⁻¹ ∈ (D.T ⊓ L).subgroupOf L := hQU hmemQ
    have hmul : ((⟨(b : G), hbL⟩ : ↥L) * u⁻¹) * u ∈ (D.T ⊓ L).subgroupOf L :=
      Subgroup.mul_mem _ hmemU hu
    have heq : ((⟨(b : G), hbL⟩ : ↥L) * u⁻¹) * u = ⟨(b : G), hbL⟩ := by group
    rw [heq] at hmul
    exact Subgroup.mem_subgroupOf.mp hmul
  · intro hbU
    have hb2 : ((seventeen_fiftyone_toNormalizer D L b : ↥(Subgroup.normalizer
        (((D.T ⊓ L).subgroupOf L).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Set (Bar2 L)))) : Bar2 L) ∈
        ((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hbU)
    change (TauCeti.Subgroup.normalizerQuotientMk
      (((D.T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))
        (seventeen_fiftyone_toNormalizer D L b)) = 1
    exact (TauCeti.Subgroup.normalizerQuotientMk_eq_one_iff _ _).mpr hb2

private theorem seventeen_fiftyone_pCore_le_subgroupOf_inf_T
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (h49 : R17_49At D V₀ V) (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma) :
    CFSG.pCore 2 ↥L ≤ (D.T ⊓ L).subgroupOf L := by
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  have hx' : (x : G) ∈ pCoreOf 2 L := by
    have h := hx
    rw [← CFSG.openPCoreOf_subgroupOf 2 L] at h
    exact Subgroup.mem_subgroupOf.mp h
  exact pCoreOf_le_inf_T h49 ctx hx'

theorem seventeen_fiftyone_permutes
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (h49 : R17_49At D V₀ V) (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hZ : Subgroup.center (Bar2 L) = ⊥)
    (hshape : IsU4 (Bar2 L) n ∨ IsSp4 (Bar2 L) n ∨ IsG2 (Bar2 L) n)
    (hKT : Inputs1719.K_LieBorelTorus) (hq : 2 < 2 ^ n)
    [((pCoreOf 2 L).subgroupOf C).Normal]
    {r : ℕ} (hr : r.Prime) (hrdvd : r ∣ 2 ^ n - 1)
    {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf r R C) :
    Permutes (F11.Omega1p r R) D.T := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact r.Prime := ⟨hr⟩
  let U : Subgroup G := D.T ⊓ L
  let B : Subgroup G := L ⊓ Subgroup.normalizer (U : Set G)
  let Q : Subgroup ↥L := CFSG.pCore 2 ↥L
  let Ubar : Subgroup (Bar2 L) := (U.subgroupOf L).map (QuotientGroup.mk' Q)
  let NQ : Type := TauCeti.Subgroup.normalizerQuotient Ubar
  have hQU : Q ≤ U.subgroupOf L := seventeen_fiftyone_pCore_le_subgroupOf_inf_T h49 ctx
  obtain ⟨eC⟩ := seventeen_fiftyone_cartan_normalizer_equiv h49 ctx hZ
  have hcommC : IsMulCommutative (↥C ⧸ (pCoreOf 2 L).subgroupOf C) :=
    (seventeen_fiftyone_cartan_comm_card hKT h49 ctx hZ hshape hq hr hrdvd).1
  have hcardOmegaC : Nat.card (F11.Omega1p r (⊤ : Subgroup
      (↥C ⧸ (pCoreOf 2 L).subgroupOf C))) = r ^ 2 :=
    (seventeen_fiftyone_cartan_comm_card hKT h49 ctx hZ hshape hq hr hrdvd).2.1
  have hρB_ker : (seventeen_fiftyone_rhoB D L).ker = U.subgroupOf B :=
    seventeen_fiftyone_rhoB_ker D L hQU
  let Xr : Subgroup G := F11.Omega1p r R
  have hXR : Xr ≤ R := (Subgroup.closure_le R).mpr (by rintro x ⟨hx, -⟩; exact hx)
  have hRC : R ≤ C := hR.le
  have hCL : C ≤ L := ctx.cartan.1
  have hXnormU : Xr ≤ Subgroup.normalizer (U : Set G) :=
    hXR.trans (hRC.trans (by simpa [U] using ctx.cartan.2.2.1))
  have hXB : Xr ≤ B := le_inf (hXR.trans (hRC.trans hCL)) hXnormU
  let ρX : ↥Xr →* NQ := (seventeen_fiftyone_rhoB D L).comp (Subgroup.inclusion hXB)
  obtain ⟨-, hXexp, -⟩ := seventeen_fiftyone_R_abelian ctx hr hq hrdvd hR hcommC
  have hXp : IsPGroup r Xr :=
    seventeen_fiftyone_omega1p_isPGroup h49 ctx hZ hshape hKT hq hr hrdvd hR
  have hUT : U ≤ D.T := by simp [U]
  have hUp : IsPGroup 2 U := D.sylowM.isPGroup.to_le hUT
  have hdisj : Xr ⊓ U = ⊥ :=
    (IsPGroup.disjoint_of_ne r 2 (seventeen_fiftyone_r_ne_two hq hrdvd) Xr U hXp hUp).eq_bot
  have hρXinj : Function.Injective ρX := by
    intro x y hxy
    have h1 : ρX (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have h2 : Subgroup.inclusion hXB (x * y⁻¹) ∈ (seventeen_fiftyone_rhoB D L).ker := by
      rw [MonoidHom.mem_ker]
      exact h1
    rw [hρB_ker] at h2
    have h3 : ((x * y⁻¹ : ↥Xr) : G) ∈ U := by
      have h := Subgroup.mem_subgroupOf.mp h2
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h
    have hbot : ((x * y⁻¹ : ↥Xr) : G) ∈ (⊥ : Subgroup G) := by
      rw [← hdisj]
      exact ⟨(x * y⁻¹).2, h3⟩
    have hxy1 : x * y⁻¹ = 1 := Subtype.ext (by simpa using hbot)
    exact mul_inv_eq_one.mp hxy1
  have hcardRange : Nat.card ↥ρX.range = Nat.card ↥Xr := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hρXinj, Subgroup.card_top]
  have hrange_le : ρX.range ≤ F11.Omega1p r (⊤ : Subgroup NQ) := by
    intro z hz
    rw [MonoidHom.mem_range] at hz
    obtain ⟨x, rfl⟩ := hz
    have hxr : ((x : G)) ^ r = 1 := hXexp x x.2
    have hpow : (ρX x) ^ r = 1 := by
      rw [← map_pow]
      rw [show x ^ r = 1 from Subtype.ext (by simpa using hxr)]
      exact map_one _
    exact Subgroup.subset_closure ⟨Subgroup.mem_top _, hpow⟩
  have hcardOmegaNQ : Nat.card (F11.Omega1p r (⊤ : Subgroup NQ)) = r ^ 2 := by
    have hmap := seventeen_fiftyone_omega1p_map_mulEquiv r eC
    rw [← hmap, Subgroup.card_map_of_injective eC.injective]
    exact hcardOmegaC
  have hcardX : Nat.card ↥Xr = r ^ 2 := by
    have hle := seventeen_fiftyone_R_omega1p_card ctx hr hq hrdvd hR hcommC hcardOmegaC
    have hle2 : Nat.card ↥Xr ≤ r ^ 2 := by
      calc Nat.card ↥Xr = Nat.card ↥ρX.range := hcardRange.symm
        _ ≤ Nat.card ↥(F11.Omega1p r (⊤ : Subgroup NQ)) :=
            Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hrange_le)
        _ = r ^ 2 := hcardOmegaNQ
    exact le_antisymm hle2 hle
  have hrange_eq : ρX.range = F11.Omega1p r (⊤ : Subgroup NQ) := by
    apply Subgroup.eq_of_le_of_card_ge hrange_le
    rw [hcardRange, hcardX, hcardOmegaNQ]
  have hML : D.M ≤ Subgroup.normalizer (L : Set G) := seventeen_fiftyone_normalizer_le h49 ctx
  have hTnormU : D.T ≤ Subgroup.normalizer (U : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      refine ⟨D.T.mul_mem (D.T.mul_mem hs hz.1) (D.T.inv_mem hs), ?_⟩
      exact (Subgroup.mem_normalizer_iff.mp (hML (D.sylowM.le hs)) z).mp hz.2
    · intro hz
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hML (D.sylowM.le hs)) z).mpr hz.2⟩
      have hz1 : s * z * s⁻¹ ∈ D.T := hz.1
      have hz_eq : z = s⁻¹ * (s * z * s⁻¹) * s := by group
      rw [hz_eq]
      exact D.T.mul_mem (D.T.mul_mem (D.T.inv_mem hs) hz1) hs
  have hconj_mem : ∀ (s : G), s ∈ D.T → ∀ z : G,
      z ∈ (Xr ⊔ U : Subgroup G) → s * z * s⁻¹ ∈ (Xr ⊔ U : Subgroup G) := by
    intro s hs z hz
    have hz' : z ∈ (Xr : Set G) * (U : Set G) := by
      have hz'' : z ∈ ((Xr ⊔ U : Subgroup G) : Set G) := hz
      rw [Subgroup.coe_mul_of_left_le_normalizer_right Xr U hXnormU] at hz''
      exact hz''
    obtain ⟨x, hx, u, hu, hxu⟩ := Set.mem_mul.mp hz'
    subst hxu
    have hyB : s * x * s⁻¹ ∈ B := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hML (D.sylowM.le hs)) x).mp
          (Subgroup.mem_inf.mp (hXB hx)).1
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTnormU hs) (hXnormU hx))
          (Subgroup.inv_mem _ (hTnormU hs))
    let y : ↥B := ⟨s * x * s⁻¹, hyB⟩
    have hxr : x ^ r = 1 := hXexp x hx
    have hyr : (s * x * s⁻¹) ^ r = 1 := by
      rw [conj_pow, hxr, mul_one, mul_inv_cancel]
    have hqy : ((QuotientGroup.mk' Q) ⟨s * x * s⁻¹, (Subgroup.mem_inf.mp hyB).1⟩) ^ r = 1 := by
      rw [← map_pow]
      rw [show (⟨s * x * s⁻¹, (Subgroup.mem_inf.mp hyB).1⟩ : ↥L) ^ r = 1 from
        Subtype.ext (by simpa using hyr)]
      exact map_one _
    have hyN : (seventeen_fiftyone_rhoB D L y) ^ r = 1 := by
      change (TauCeti.Subgroup.normalizerQuotientMk Ubar
        (seventeen_fiftyone_toNormalizer D L y)) ^ r = 1
      rw [← map_pow]
      apply congrArg (TauCeti.Subgroup.normalizerQuotientMk Ubar)
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, seventeen_fiftyone_toNormalizer_coe]
      exact hqy
    have hmemOmega : seventeen_fiftyone_rhoB D L y ∈ F11.Omega1p r (⊤ : Subgroup NQ) :=
      Subgroup.subset_closure ⟨Subgroup.mem_top _, hyN⟩
    rw [← hrange_eq] at hmemOmega
    obtain ⟨x', hx'⟩ := MonoidHom.mem_range.mp hmemOmega
    have hx'' : (seventeen_fiftyone_rhoB D L) (Subgroup.inclusion hXB x') =
        (seventeen_fiftyone_rhoB D L) y := hx'
    have hker : y * (Subgroup.inclusion hXB x')⁻¹ ∈ (seventeen_fiftyone_rhoB D L).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hx'', mul_inv_cancel]
    rw [hρB_ker] at hker
    have hyU : (s * x * s⁻¹) * (x' : G)⁻¹ ∈ U := by
      have h := Subgroup.mem_subgroupOf.mp hker
      simpa [Subgroup.coe_mul, Subgroup.coe_inv, y] using h
    have hy_mem : s * x * s⁻¹ ∈ (Xr : Set G) * (U : Set G) := by
      have heq2 : s * x * s⁻¹ = ((s * x * s⁻¹) * (x' : G)⁻¹) * (x' : G) := by group
      rw [heq2]
      rw [Subgroup.set_mul_normalizer_comm (Xr : Set G) U hXnormU]
      exact Set.mul_mem_mul hyU x'.2
    have hy_sup : s * x * s⁻¹ ∈ (Xr ⊔ U : Subgroup G) := by
      have h := hy_mem
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Xr U hXnormU] at h
      exact h
    have hsu : s * u * s⁻¹ ∈ (Xr ⊔ U : Subgroup G) :=
      (le_sup_right : U ≤ Xr ⊔ U)
        ((Subgroup.mem_normalizer_iff.mp (hTnormU hs) u).mp hu)
    have heq3 : s * (x * u) * s⁻¹ = (s * x * s⁻¹) * (s * u * s⁻¹) := by group
    rw [heq3]
    exact (Xr ⊔ U).mul_mem hy_sup hsu
  have hTnorm : D.T ≤ Subgroup.normalizer ((Xr ⊔ U : Subgroup G) : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact hconj_mem t ht z hz
    · intro hz
      have h := hconj_mem t⁻¹ (D.T.inv_mem ht) (t * z * t⁻¹) hz
      have heq : t⁻¹ * (t * z * t⁻¹) * t⁻¹⁻¹ = z := by group
      rwa [heq] at h
  exact TwelveNineteen.permutes_of_le_normalizer_sup (inf_le_left : U ≤ D.T) hTnorm hXnormU

@[expose] noncomputable def seventeen_fiftyone_psi {D : Data G} {L : Subgroup G}
    (hNL : D.M ≤ Subgroup.normalizer (L : Set G)) :
    ↥D.T →* MulAut (Bar2 L) :=
  (MulAut.mapQuotient (CFSG.pCore 2 ↥L)).comp
    ((Subgroup.normalizerMonoidHom (H := L)).comp
      (Subgroup.inclusion (D.sylowM.le.trans hNL)))

@[expose] noncomputable def seventeen_fiftyone_phi {D : Data G} {L : Subgroup G}
    (hNL : D.M ≤ Subgroup.normalizer (L : Set G)) :
    ↥D.T →* CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 L) :=
  (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L))).comp
    (seventeen_fiftyone_psi hNL)

theorem seventeen_fiftyone_kernel_le_pCore
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (h49 : R17_49At D V₀ V) (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hZ : Subgroup.center (Bar2 L) = ⊥)
    (hshape : IsU4 (Bar2 L) n ∨ IsSp4 (Bar2 L) n ∨ IsG2 (Bar2 L) n)
    (hKT : Inputs1719.K_LieBorelTorus) (hq : 2 < 2 ^ n)
    [((pCoreOf 2 L).subgroupOf C).Normal]
    {r : ℕ} (hr : r.Prime) (hrdvd : r ∣ 2 ^ n - 1)
    {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf r R C)
    {u : ↥D.T}
    (hu : seventeen_fiftyone_psi (seventeen_fiftyone_normalizer_le h49 ctx) u ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L)) :
    (u : G) ∈ pCoreOf 2 (F11.Omega1p r R ⊔ D.T) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let hNL : D.M ≤ Subgroup.normalizer (L : Set G) := seventeen_fiftyone_normalizer_le h49 ctx
  let Q : Subgroup ↥L := CFSG.pCore 2 ↥L
  let U : Subgroup G := D.T ⊓ L
  let Ubar : Subgroup (Bar2 L) := (U.subgroupOf L).map (QuotientGroup.mk' Q)
  let NQ : Type := TauCeti.Subgroup.normalizerQuotient Ubar
  let ψ : ↥D.T →* MulAut (Bar2 L) := seventeen_fiftyone_psi hNL
  let ψL : ↥D.T →* MulAut ↥L :=
    (Subgroup.normalizerMonoidHom (H := L)).comp
      (Subgroup.inclusion (D.sylowM.le.trans hNL))
  have hψeq : ψ = (MulAut.mapQuotient Q).comp ψL := rfl
  have hψL_apply : ∀ (v : ↥D.T) (a : ↥L),
      ψL v a = ⟨(v : G) * (a : G) * (v : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hNL (D.sylowM.le v.2)) (a : G)).mp a.2⟩ := by
    intro v a
    dsimp only [ψL]
    rw [MonoidHom.comp_apply]
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp [Subgroup.coe_inclusion]
  have hψ_mk : ∀ (v : ↥D.T) (a : ↥L),
      ψ v (QuotientGroup.mk' Q a) =
        QuotientGroup.mk' Q ⟨(v : G) * (a : G) * (v : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hNL (D.sylowM.le v.2)) (a : G)).mp a.2⟩ := by
    intro v a
    rw [hψeq, MonoidHom.comp_apply]
    change ((MulAut.mapQuotient Q) (ψL v)) (a : Bar2 L) = _
    rw [MulAut.mapQuotient_mk]
    exact congrArg (QuotientGroup.mk' Q) (hψL_apply v a)
  have hψ_eq_conj : ∀ (v : ↥D.T) (hvL : (v : G) ∈ L),
      ψ v = MulAut.conj (QuotientGroup.mk' Q (⟨(v : G), hvL⟩ : ↥L)) := by
    intro v hvL
    apply MulEquiv.ext
    intro y
    induction y using QuotientGroup.induction_on with
    | H a =>
      change (ψ v) ((QuotientGroup.mk' Q) a) =
        (MulAut.conj (QuotientGroup.mk' Q (⟨(v : G), hvL⟩ : ↥L)))
          ((QuotientGroup.mk' Q) a)
      rw [hψ_mk v a, MulAut.conj_apply, ← map_mul, ← map_inv]
      congr 1
  have hconj_inj : Function.Injective (MulAut.conj : Bar2 L →* MulAut (Bar2 L)) := by
    intro a b hab
    have hker : MulAut.conj (b⁻¹ * a) = 1 := by
      rw [map_mul, map_inv, hab, inv_mul_cancel]
    have hmem : b⁻¹ * a ∈ Subgroup.center (Bar2 L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun f : MulAut (Bar2 L) => f g) hker
      rw [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * (b⁻¹ * a) = (b⁻¹ * a) * g * (b⁻¹ * a)⁻¹ * (b⁻¹ * a) := by rw [h]
        _ = (b⁻¹ * a) * g := by group
    rw [hZ] at hmem
    have hba : b⁻¹ * a = 1 := by simpa using hmem
    calc a = b * (b⁻¹ * a) := by group
      _ = b * 1 := by rw [hba]
      _ = b := mul_one b
  obtain ⟨x, hx⟩ := hu
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp D.sylowM.isPGroup u
  have hu_pow : u ^ 2 ^ k = 1 := by
    rw [← hk, pow_orderOf_eq_one]
  have hx_pow : x ^ 2 ^ k = 1 := by
    apply hconj_inj
    rw [map_pow, hx, ← map_pow, hu_pow, map_one, map_one]
  have hψ_maps_Ubar : ∀ (v : ↥D.T) (y : Bar2 L), y ∈ Ubar → ψ v y ∈ Ubar := by
    intro v y hy
    obtain ⟨a, ha, haz⟩ := Subgroup.mem_map.mp hy
    rw [← haz, hψ_mk v a]
    have haU : (a : G) ∈ U := Subgroup.mem_subgroupOf.mp ha
    have haT : (a : G) ∈ D.T := haU.1
    have hvT : (v : G) * (a : G) * (v : G)⁻¹ ∈ D.T :=
      D.T.mul_mem (D.T.mul_mem v.2 haT) (D.T.inv_mem v.2)
    have hvL : (v : G) * (a : G) * (v : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hNL (D.sylowM.le v.2)) (a : G)).mp a.2
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' Q) (by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨hvT, hvL⟩)
  have hxNbar : x ∈ Subgroup.normalizer (Ubar : Set (Bar2 L)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h := hψ_maps_Ubar u y hy
      rwa [← hx] at h
    · intro hy
      have h := hψ_maps_Ubar u⁻¹ ((MulAut.conj x) y) hy
      have hh : (MulAut.conj x)⁻¹ ((MulAut.conj x) y) ∈ Ubar := by
        rwa [map_inv, ← hx] at h
      have hcancel : (MulAut.conj x)⁻¹ ((MulAut.conj x) y) = y := by
        simp [MulAut.conj_apply, map_inv]
        group
      rwa [hcancel] at hh
  obtain ⟨eC⟩ := seventeen_fiftyone_cartan_normalizer_equiv h49 ctx hZ
  have hoddC : Odd (Nat.card (↥C ⧸ (pCoreOf 2 L).subgroupOf C)) :=
    (seventeen_fiftyone_cartan_comm_card hKT h49 ctx hZ hshape hq hr hrdvd).2.2
  have hoddNQ : Odd (Nat.card NQ) := by
    rw [← Nat.card_congr eC.toEquiv]
    exact hoddC
  let xN : ↥(Subgroup.normalizer (Ubar : Set (Bar2 L))) := ⟨x, hxNbar⟩
  have hclass_pow : (TauCeti.Subgroup.normalizerQuotientMk Ubar) xN ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have hxNpow : xN ^ 2 ^ k = 1 := by
      apply Subtype.ext
      simpa using hx_pow
    rw [hxNpow, map_one]
  have hclass_one : (TauCeti.Subgroup.normalizerQuotientMk Ubar) xN = 1 := by
    have hdvd1 : orderOf ((TauCeti.Subgroup.normalizerQuotientMk Ubar) xN) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one hclass_pow
    have hdvd2 : orderOf ((TauCeti.Subgroup.normalizerQuotientMk Ubar) xN) ∣ Nat.card NQ :=
      orderOf_dvd_natCard _
    have hcop : Nat.Coprime (2 ^ k) (Nat.card NQ) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hoddNQ)
    have hgcd : orderOf ((TauCeti.Subgroup.normalizerQuotientMk Ubar) xN) ∣
        Nat.gcd (2 ^ k) (Nat.card NQ) := Nat.dvd_gcd hdvd1 hdvd2
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at hgcd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
  have hxUbar : x ∈ Ubar := by
    have := (TauCeti.Subgroup.normalizerQuotientMk_eq_one_iff Ubar xN).mp hclass_one
    simpa [xN] using this
  obtain ⟨a, haU, hax⟩ := Subgroup.mem_map.mp hxUbar
  let t : ↥D.T := ⟨(a : G), (Subgroup.mem_subgroupOf.mp haU).1⟩
  have hψ_t : ψ t = MulAut.conj x := by
    have h := hψ_eq_conj t a.2
    rw [show (⟨(t : G), a.2⟩ : ↥L) = a from rfl, hax] at h
    exact h
  let w : ↥D.T := ⟨(u : G) * (t : G)⁻¹,
    D.T.mul_mem u.2 (D.T.inv_mem t.2)⟩
  have hψ_w : ψ w = 1 := by
    show ψ (u * t⁻¹) = 1
    rw [map_mul, map_inv, hψ_t, ← hx, mul_inv_cancel]
  let Cc : Subgroup G := centSection D.M L (pCoreOf 2 L)
  let Qc : Subgroup G := D.T ⊓ Cc
  have hwM : (w : G) ∈ D.M := D.sylowM.le w.2
  have hwNL : (w : G) ∈ Subgroup.normalizer (L : Set G) := hNL hwM
  have hwNQ : (w : G) ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hwNL
  have hwcent : (w : G) ∈ Cc := by
    refine mem_centSection_iff.mpr ⟨hwM, hwNL, hwNQ, ?_⟩
    intro l hl
    have hmapQ : MulAut.mapQuotient Q (ψL w) = 1 := by
      have h := hψ_w
      rw [hψeq, MonoidHom.comp_apply] at h
      exact h
    have hker : ψL w ∈ (MulAut.mapQuotient Q).ker := by
      rw [MonoidHom.mem_ker]
      exact hmapQ
    have hfix : ∀ y : ↥L, ((ψL w) y : Bar2 L) = (y : Bar2 L) :=
      fun y => (MulAut.mem_ker_mapQuotient_iff (N := Q)).mp hker y
    have hfix' := hfix (⟨l, hl⟩ : ↥L)
    have hψLw := hψL_apply w (⟨l, hl⟩ : ↥L)
    have hmk : QuotientGroup.mk' Q (⟨(w : G) * l * (w : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp hwNL l).mp hl⟩ : ↥L) =
        QuotientGroup.mk' Q (⟨l, hl⟩ : ↥L) := by
      rw [← hψLw]
      exact hfix'
    have hmemQ : (⟨(w : G) * l * (w : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp hwNL l).mp hl⟩ : ↥L) * (⟨l, hl⟩ : ↥L)⁻¹ ∈ Q := by
      apply (QuotientGroup.eq_one_iff (N := Q) ((⟨(w : G) * l * (w : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp hwNL l).mp hl⟩ : ↥L) * (⟨l, hl⟩ : ↥L)⁻¹)).mp
      change (QuotientGroup.mk' Q ((⟨(w : G) * l * (w : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp hwNL l).mp hl⟩ : ↥L) * (⟨l, hl⟩ : ↥L)⁻¹)) = 1
      rw [map_mul, map_inv, hmk, mul_inv_cancel]
    have hGmem : (((⟨(w : G) * l * (w : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp hwNL l).mp hl⟩ : ↥L) * (⟨l, hl⟩ : ↥L)⁻¹ : ↥L) : G)
        ∈ pCoreOf 2 L := by
      rw [CFSG.openPCoreOf_eq_map_pCore 2 L]
      exact Subgroup.mem_map_of_mem L.subtype hmemQ
    simpa using hGmem
  have hwQc : (w : G) ∈ Qc := ⟨w.2, hwcent⟩
  have hConjCent : ∀ {m : G}, m ∈ D.M → ∀ c ∈ Cc, m * c * m⁻¹ ∈ Cc := by
    intro m hm c hc
    obtain ⟨hcM, hcNL, hcNQ, hccent⟩ := mem_centSection_iff.mp hc
    have hmNL : m ∈ Subgroup.normalizer (L : Set G) := hNL hm
    have hmNQ : m ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hmNL
    refine mem_centSection_iff.mpr ⟨?_, ?_, ?_, ?_⟩
    · exact D.M.mul_mem (D.M.mul_mem hm hcM) (D.M.inv_mem hm)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hmNL hcNL) (Subgroup.inv_mem _ hmNL)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hmNQ hcNQ) (Subgroup.inv_mem _ hmNQ)
    · intro l hl
      have hl' : m⁻¹ * l * m ∈ L := by
        simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmNL) l).mp hl
      have hinner : c * (m⁻¹ * l * m) * c⁻¹ * (m⁻¹ * l * m)⁻¹ ∈ pCoreOf 2 L := hccent _ hl'
      have hconj : m * (c * (m⁻¹ * l * m) * c⁻¹ * (m⁻¹ * l * m)⁻¹) * m⁻¹ ∈
          pCoreOf 2 L := (Subgroup.mem_normalizer_iff.mp hmNQ _).mp hinner
      have heq : (m * c * m⁻¹) * l * (m * c * m⁻¹)⁻¹ * l⁻¹ =
          m * (c * (m⁻¹ * l * m) * c⁻¹ * (m⁻¹ * l * m)⁻¹) * m⁻¹ := by group
      rwa [heq]
  have hCentNormal : D.M ≤ Subgroup.normalizer (Cc : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · exact hConjCent hm c
    · intro hc
      have h := hConjCent (D.M.inv_mem hm) (m * c * m⁻¹) hc
      simpa [mul_assoc] using h
  have hT_norm_Qc : D.T ≤ Subgroup.normalizer (Qc : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact ⟨D.T.mul_mem (D.T.mul_mem ht hq.1) (D.T.inv_mem ht),
        (Subgroup.mem_normalizer_iff.mp (hCentNormal (D.sylowM.le ht)) q).mp hq.2⟩
    · intro hq
      have ht_inv : t⁻¹ ∈ D.T := D.T.inv_mem ht
      have hq' : t⁻¹ * (t * q * t⁻¹) * (t⁻¹)⁻¹ ∈ Qc :=
        ⟨D.T.mul_mem (D.T.mul_mem ht_inv hq.1) (D.T.inv_mem ht_inv),
          (Subgroup.mem_normalizer_iff.mp (hCentNormal (D.sylowM.le ht_inv)) _).mp hq.2⟩
      simpa [mul_assoc] using hq'
  have hT_norm_U : D.T ≤ Subgroup.normalizer (U : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact ⟨D.T.mul_mem (D.T.mul_mem ht hx.1) (D.T.inv_mem ht),
        (Subgroup.mem_normalizer_iff.mp (hNL (D.sylowM.le ht)) x).mp hx.2⟩
    · intro hx
      have ht_inv : t⁻¹ ∈ D.T := D.T.inv_mem ht
      have hx' : t⁻¹ * (t * x * t⁻¹) * (t⁻¹)⁻¹ ∈ U :=
        ⟨D.T.mul_mem (D.T.mul_mem ht_inv hx.1) (D.T.inv_mem ht_inv),
          (Subgroup.mem_normalizer_iff.mp (hNL (D.sylowM.le ht_inv)) _).mp hx.2⟩
      simpa [mul_assoc] using hx'
  have hLConjQc : ∀ {e : G}, e ∈ L → ∀ q ∈ Qc, e * q * e⁻¹ ∈ Qc := by
    intro e he q hq
    have hqDT : q ∈ D.T := hq.1
    obtain ⟨hqM, hqNL, hqNQ, hqcent⟩ := mem_centSection_iff.mp hq.2
    have hcQ : q * e * q⁻¹ * e⁻¹ ∈ pCoreOf 2 L := hqcent e he
    have hcTL := pCoreOf_le_inf_T h49 ctx hcQ
    have hcT : q * e * q⁻¹ * e⁻¹ ∈ D.T := hcTL.1
    have hcL : q * e * q⁻¹ * e⁻¹ ∈ L := hcTL.2
    have hcM : q * e * q⁻¹ * e⁻¹ ∈ D.M := ctx.mem_calC.1.le hcL
    have hcQinv : (q * e * q⁻¹ * e⁻¹)⁻¹ ∈ pCoreOf 2 L := (pCoreOf 2 L).inv_mem hcQ
    have hcTLinv := pCoreOf_le_inf_T h49 ctx hcQinv
    have hcTinv : (q * e * q⁻¹ * e⁻¹)⁻¹ ∈ D.T := hcTLinv.1
    have hcLinv : (q * e * q⁻¹ * e⁻¹)⁻¹ ∈ L := hcTLinv.2
    have hcMinv : (q * e * q⁻¹ * e⁻¹)⁻¹ ∈ D.M := ctx.mem_calC.1.le hcLinv
    have hcNLinv : (q * e * q⁻¹ * e⁻¹)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      Subgroup.le_normalizer hcLinv
    have hcNQinv : (q * e * q⁻¹ * e⁻¹)⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      Subgroup.le_normalizer hcQinv
    have heq : e * q * e⁻¹ = (q * e * q⁻¹ * e⁻¹)⁻¹ * q := by group
    rw [heq]
    refine ⟨D.T.mul_mem (D.T.inv_mem hcT) hqDT, ?_⟩
    refine mem_centSection_iff.mpr ⟨?_, ?_, ?_, ?_⟩
    · exact D.M.mul_mem (D.M.inv_mem hcM) hqM
    · exact Subgroup.mul_mem _ hcNLinv hqNL
    · exact Subgroup.mul_mem _ hcNQinv hqNQ
    · intro l hl
      have hql : q * l * q⁻¹ * l⁻¹ ∈ pCoreOf 2 L := hqcent l hl
      have hlc : l * (q * e * q⁻¹ * e⁻¹) * l⁻¹ ∈ pCoreOf 2 L :=
        (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hl) _).mp hcQ
      have heq2 : ((q * e * q⁻¹ * e⁻¹)⁻¹ * q) * l *
          ((q * e * q⁻¹ * e⁻¹)⁻¹ * q)⁻¹ * l⁻¹ =
          (q * e * q⁻¹ * e⁻¹)⁻¹ * (q * l * q⁻¹ * l⁻¹) *
            (l * (q * e * q⁻¹ * e⁻¹) * l⁻¹) := by group
      rw [heq2]
      exact (pCoreOf 2 L).mul_mem
        ((pCoreOf 2 L).mul_mem ((pCoreOf 2 L).inv_mem hcQ) hql) hlc
  have hL_norm_Qc : L ≤ Subgroup.normalizer (Qc : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · exact hLConjQc he q
    · intro hq
      have h := hLConjQc (L.inv_mem he) (e * q * e⁻¹) hq
      simpa [mul_assoc] using h
  let Xr : Subgroup G := F11.Omega1p r R
  have hXrR : Xr ≤ R := (Subgroup.closure_le R).mpr (by rintro x ⟨hx, -⟩; exact hx)
  have hXrC : Xr ≤ C := hXrR.trans hR.le
  have hXrL : Xr ≤ L := hXrC.trans ctx.cartan.1
  have hXrU : Xr ≤ Subgroup.normalizer (U : Set G) := hXrC.trans ctx.cartan.2.2.1
  have hXrQc : Xr ≤ Subgroup.normalizer (Qc : Set G) := hXrL.trans hL_norm_Qc
  let Y : Subgroup G := U ⊔ Qc
  let H : Subgroup G := Xr ⊔ D.T
  have hYH : Y ≤ H := by
    refine sup_le ?_ ?_
    · exact inf_le_left.trans le_sup_right
    · exact inf_le_left.trans le_sup_right
  have hHnorm : H ≤ Subgroup.normalizer (Y : Set G) := by
    refine sup_le ?_ ?_
    · intro e he
      exact Subgroup.inf_normalizer_le_normalizer_sup U Qc ⟨hXrU he, hXrQc he⟩
    · intro t ht
      exact Subgroup.inf_normalizer_le_normalizer_sup U Qc ⟨hT_norm_U ht, hT_norm_Qc ht⟩
  have hYp : IsPGroup 2 ↥Y := by
    dsimp only [Y]
    exact D.sylowM.isPGroup.to_le (sup_le inf_le_left inf_le_left)
  have hYle : Y ≤ pCoreOf 2 H :=
    CFSG.Quasithin.RonanD33.le_pCoreOf_of_le_normalizer hYH hHnorm hYp
  have htU : (t : G) ∈ U := Subgroup.mem_subgroupOf.mp haU
  have huY : (u : G) ∈ Y := by
    have hw_t : (w : G) * (t : G) = (u : G) := by
      change ((u : G) * (t : G)⁻¹) * (t : G) = (u : G)
      group
    rw [← hw_t]
    exact Y.mul_mem (Subgroup.mem_sup_right hwQc) (Subgroup.mem_sup_left htU)
  exact hYle huY

theorem seventeen_fiftyone_omega1_T_cyclic
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (h49 : R17_49At D V₀ V) (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hZ : Subgroup.center (Bar2 L) = ⊥)
    (hshape : IsU4 (Bar2 L) n ∨ IsSp4 (Bar2 L) n ∨ IsG2 (Bar2 L) n)
    [((pCoreOf 2 L).subgroupOf C).Normal]
    (hKT : Inputs1719.K_LieBorelTorus) (houter : (∀ (Y : Type) [Group Y] (n : ℕ), IsU4 Y n →
        IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y)) ∧ (∀ (Y : Type) [Group
        Y] (n : ℕ), IsSp4 Y n → IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y))
        ∧ (∀ (Y : Type) [Group Y] (n : ℕ), IsG2 Y n → IsCyclic
        (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y)))
    (hq : 2 < 2 ^ n)
    {r : ℕ} (hr : r.Prime) (hrdvd : r ∣ 2 ^ n - 1)
    {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf r R C) :
    ∃ a ∈ F11.Omega1p 2 D.T, F11.Omega1p 2 D.T =
      Subgroup.zpowers a ⊔ (F11.Omega1p 2 D.T ⊓ pCoreOf 2 (F11.Omega1p r R ⊔ D.T)) := by
  classical
  let hNL := seventeen_fiftyone_normalizer_le h49 ctx
  let ψ := seventeen_fiftyone_psi hNL
  let φ := seventeen_fiftyone_phi hNL
  let O : Subgroup G := pCoreOf 2 (F11.Omega1p r R ⊔ D.T)
  have hOut : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 L)) := by
    rcases hshape with h | h | h
    · exact houter.1 (Bar2 L) n h
    · exact houter.2.1 (Bar2 L) n h
    · exact houter.2.2 (Bar2 L) n h
  have hker : ∀ u : ↥D.T,
      ψ u ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L) → (u : G) ∈ O :=
    fun u hu => seventeen_fiftyone_kernel_le_pCore h49 ctx hZ hshape hKT hq hr hrdvd hR
      (u := u) hu
  have hkerφ : ∀ u : ↥D.T, φ u = 1 → (u : G) ∈ O := by
    intro u hu
    apply hker u
    change (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L)))
      (ψ u) = 1 at hu
    exact (QuotientGroup.eq_one_iff _).mp hu
  have hOT : D.T ≤ Subgroup.normalizer (O : Set G) := by
    dsimp [O]
    exact (le_sup_right : D.T ≤ F11.Omega1p r R ⊔ D.T).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.openPCoreOf_le 2 _)).mp
        (by rw [CFSG.openPCoreOf_subgroupOf 2 (_ ⊔ D.T)]; infer_instance :
          ((pCoreOf 2 (F11.Omega1p r R ⊔ D.T)).subgroupOf
            (F11.Omega1p r R ⊔ D.T)).Normal))
  haveI : IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 L)) := hOut
  exact omega1_eq_zpowers_sup_of_hom_cyclic φ hOT hkerφ

theorem normalizer_omega1p_le_of_normalizer_le {p : ℕ} {R P : Subgroup G}
    (hPR : P ≤ Subgroup.normalizer (R : Set G)) :
    P ≤ Subgroup.normalizer (F11.Omega1p p R : Set G) := by
  have hconj : ∀ x ∈ P, ∀ z ∈ F11.Omega1p p R, x * z * x⁻¹ ∈ F11.Omega1p p R := by
    intro x hx z hz
    unfold F11.Omega1p at hz ⊢
    refine Subgroup.closure_induction (p := fun w _ => x * w * x⁻¹ ∈ F11.Omega1p p R) ?_ ?_ ?_ ?_ hz
    · rintro w ⟨hwR, hwp⟩
      apply Subgroup.subset_closure
      have hxR : x * w * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hPR hx) w).mp hwR
      refine ⟨hxR, ?_⟩
      rw [conj_pow, hwp]
      simp
    · show x * 1 * x⁻¹ ∈ F11.Omega1p p R
      simpa using (F11.Omega1p p R).one_mem
    · intro a b _ _ ha hb
      simpa [mul_assoc] using (F11.Omega1p p R).mul_mem ha hb
    · intro a _ ha
      simpa [mul_assoc] using (F11.Omega1p p R).inv_mem ha
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact hconj x hx y
  · intro hy
    have h := hconj (x⁻¹) (P.inv_mem hx) (x * y * x⁻¹) hy
    have hy' : x⁻¹ * (x * y * x⁻¹) * x = y := by group
    rw [inv_inv] at h
    rwa [hy'] at h

theorem seventeen_fiftyone_omega1p_not_cyclic
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    [((pCoreOf 2 L).subgroupOf C).Normal]
    {r : ℕ} (hr : r.Prime) (hq : 2 < 2 ^ n) (hrdvd : r ∣ 2 ^ n - 1)
    {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf r R C)
    (hcomm : IsMulCommutative (↥C ⧸ (pCoreOf 2 L).subgroupOf C))
    (hcardOmega : Nat.card (F11.Omega1p r (⊤ : Subgroup
      (↥C ⧸ (pCoreOf 2 L).subgroupOf C))) = r ^ 2)
    (hXexp : ∀ x ∈ F11.Omega1p r R, x ^ r = 1) :
    ¬ IsCyclic ↥(F11.Omega1p r R) := by
  intro hcyc
  have hcard := seventeen_fiftyone_R_omega1p_card ctx hr hq hrdvd hR hcomm hcardOmega
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hg : Subgroup.zpowers g = ⊤ := le_antisymm le_top (fun x _ => hg x)
  have hgpow : g ^ r = 1 := Subtype.ext (by simpa using hXexp (g : G) g.2)
  have hord : orderOf g ∣ r := orderOf_dvd_of_pow_eq_one hgpow
  have hordle : orderOf g ≤ r := Nat.le_of_dvd hr.pos hord
  have hcardg : Nat.card ↥(F11.Omega1p r R) = orderOf g := by
    calc Nat.card ↥(F11.Omega1p r R) = Nat.card (⊤ : Subgroup ↥(F11.Omega1p r R)) := by simp
      _ = Nat.card (Subgroup.zpowers g) := by rw [hg]
      _ = orderOf g := Nat.card_zpowers g
  have hr2 : 2 ≤ r := hr.two_le
  have hle : r ^ 2 ≤ r := hcard.trans (hcardg.trans_le hordle)
  nlinarith [pow_two r]

theorem seventeen_fiftyone_inP11_of_not_g2
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (h49 : R17_49At D V₀ V) (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hZ : Subgroup.center (Bar2 L) = ⊥)
    (hshape : IsU4 (Bar2 L) n ∨ IsSp4 (Bar2 L) n ∨ IsG2 (Bar2 L) n)
    (hKT : Inputs1719.K_LieBorelTorus)
    (h50 : R17_50At D V₀ V)
    [((pCoreOf 2 L).subgroupOf C).Normal]
    {r : ℕ} (hr : r.Prime) (hrdvd : r ∣ 2 ^ n - 1)
    (hnot : ¬ (IsG2 (Bar2 L) n ∧ r = 3))
    {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf r R C)
    (hGamma : CFSG.Open.rankThreeGamma 1 r R ≤ D.M) :
    F11.InP11 D (F11.Omega1p r R) := by
  classical
  have hq : 2 < 2 ^ n := (h50 L X p n l C Dc Gamma ctx).2
  have hr2 : r ≠ 2 := seventeen_fiftyone_r_ne_two hq hrdvd
  have hcomm := (seventeen_fiftyone_cartan_comm_card hKT h49 ctx hZ hshape hq hr hrdvd).1
  have hcardOmega := (seventeen_fiftyone_cartan_comm_card hKT h49 ctx hZ hshape hq hr hrdvd).2.1
  have hfac := seventeen_fiftyone_cartan_factorization hKT h49 ctx hZ hshape hq hr hrdvd hnot
  obtain ⟨hRcomm, hXexp, hXC⟩ :=
    seventeen_fiftyone_R_abelian ctx hr hq hrdvd hR hcomm
  have hXnc : ¬ IsCyclic ↥(F11.Omega1p r R) :=
    seventeen_fiftyone_omega1p_not_cyclic ctx hr hq hrdvd hR hcomm hcardOmega hXexp
  haveI : Fact r.Prime := ⟨hr⟩
  have hXp : IsPGroup r (F11.Omega1p r R) :=
    seventeen_fiftyone_omega1p_isPGroup h49 ctx hZ hshape hKT hq hr hrdvd hR
  have hperm : Permutes (F11.Omega1p r R) D.T :=
    seventeen_fiftyone_permutes h49 ctx hZ hshape hKT hq hr hrdvd hR
  have hXR : F11.Omega1p r R ≤ R :=
    (Subgroup.closure_le R).mpr (by rintro x ⟨hx, -⟩; exact hx)
  have hXM : F11.Omega1p r R ≤ D.M :=
    hXR.trans (hR.le.trans (ctx.cartan.1.trans ctx.mem_calC.1.le))
  have hGammaX : CFSG.Open.rankThreeGamma 1 r (F11.Omega1p r R) ≤ D.M :=
    (CFSG.AGLEmbeddingD2.glbCore_mono r 1 hXR).trans hGamma
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf r R L :=
    seventeen_fiftyone_R_sylow_L ctx hr hr2 hR hfac
  have hRM : R ≤ D.M := hR.le.trans (ctx.cartan.1.trans ctx.mem_calC.1.le)
  obtain ⟨P, hPsyl, hRP⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.exists_isSylowOf_ge_of_isPGroup hR.isPGroup hRM
  have hRL : R ≤ L := hR.le.trans ctx.cartan.1
  have hQp : IsPGroup r ((P ⊓ L : Subgroup G)) := by
    rw [IsPGroup.iff_orderOf]
    intro x
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hPsyl.isPGroup) ⟨(x : G), x.2.1⟩
    have hord : orderOf x = orderOf (Subgroup.inclusion
        (inf_le_left : (P ⊓ L : Subgroup G) ≤ P) x) :=
      (orderOf_injective _ (Subgroup.inclusion_injective _) x).symm
    exact ⟨k, hord.trans hk⟩
  have hQeq : P ⊓ L = R := hRsyl.eq_of_le (le_inf hRP hRL) inf_le_right hQp
  have hML : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer ctx.mem_calC.1.le).mp
      (ctx_L_normal h49 ctx)
  have hPnormR : P ≤ Subgroup.normalizer (R : Set G) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hRP).mp ?_
    constructor
    intro n hn p
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hnPL : (n : G) ∈ P ⊓ L := by rw [hQeq]; exact hn
    have hpM : (p : G) ∈ D.M := hPsyl.le p.2
    have hpP : (p : G) ∈ P := p.2
    have hpL : (p : G) * (n : G) * (p : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hML hpM) (n : G)).mp hnPL.2
    rw [← hQeq]
    exact ⟨P.mul_mem (P.mul_mem hpP hnPL.1) (P.inv_mem hpP), hpL⟩
  have hPnormX : P ≤ Subgroup.normalizer (F11.Omega1p r R : Set G) :=
    normalizer_omega1p_le_of_normalizer_le hPnormR
  refine ⟨r, hr, hr2, hXM, hXp, hXexp, hXnc, hperm, hGammaX,
    Or.inr ⟨F11.Omega1p r R, hXnc, ⟨P, hPsyl, hXR.trans hRP, hPnormX⟩, hGammaX⟩⟩

theorem seventeen_fiftyone_strong_g2
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (h880 : F08.R880 D) (hG2 : IsG2 (Bar2 L) n) (hq : 2 < 2 ^ n) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  by_contra hns
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp at hq
    · exact h
  have hG2Der : F08.IsG2Der (Bar2 L) n := Or.inr ⟨hn2, hG2⟩
  have hList : F08.List880 (Bar2 L) := by
    unfold F08.List880
    tauto
  obtain ⟨P, hPsyl⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 D.M
  obtain ⟨hJ2, -, -, -, -, -⟩ := h880 L ctx.mem_calC hList hns P hPsyl
  obtain ⟨e⟩ := hJ2
  have hcardJ2 : Nat.card (Bar2 L) = 604800 := by
    calc Nat.card (Bar2 L) = Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J2) :=
          Nat.card_congr e.toEquiv
      _ = 604800 := CFSG.Sporadic.J2.card_J2
  have hCE : CFSG.Blueprint.ChevalleyExceptionalModel (Bar2 L) .G2 2 n :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel hG2 (by decide)
  have hcardG2 : Nat.card (Bar2 L) = ordG2 (2 ^ n) := by
    simpa using CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hCE
  have hdvdG2 : 2 ^ 8 ∣ ordG2 (2 ^ n) := by
    unfold ordG2
    have hpow : 2 ^ 8 ∣ (2 ^ n) ^ 6 := by
      rw [← pow_mul]
      exact pow_dvd_pow 2 (by omega : 8 ≤ n * 6)
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpow _) _
  have hdvd : 2 ^ 8 ∣ Nat.card (Bar2 L) := hcardG2.symm ▸ hdvdG2
  rw [hcardJ2] at hdvd
  norm_num at hdvd

theorem seventeen_fiftyone_cartan_pCore_normal
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (h49 : R17_49At D V₀ V) (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma) :
    ((pCoreOf 2 L).subgroupOf C).Normal := by
  constructor
  intro n hn c
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hL : ((pCoreOf 2 L).subgroupOf L).Normal := by
    rw [CFSG.openPCoreOf_subgroupOf 2 L]
    infer_instance
  have hnL : (n : G) ∈ L := (pCoreOf_le_inf_T h49 ctx hn).2
  exact Subgroup.mem_subgroupOf.mp
    (hL.conj_mem ⟨(n : G), hnL⟩ (Subgroup.mem_subgroupOf.mpr hn)
      ⟨(c : G), ctx.cartan.1 c.2⟩)

theorem seventeen_fiftyone_inP11_of_g2
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (h49 : R17_49At D V₀ V) (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hZ : Subgroup.center (Bar2 L) = ⊥)
    (hshape : IsU4 (Bar2 L) n ∨ IsSp4 (Bar2 L) n ∨ IsG2 (Bar2 L) n)
    (hKT : Inputs1719.K_LieBorelTorus)
    (h880 : F08.R880 D) (h50 : R17_50At D V₀ V)
    {r : ℕ} (hr : r.Prime) (hrdvd : r ∣ 2 ^ n - 1)
    (hG2r : IsG2 (Bar2 L) n ∧ r = 3)
    {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf r R C) :
    F11.InP11 D (F11.Omega1p r R) := by
  classical
  have hq : 2 < 2 ^ n := (h50 L X p n l C Dc Gamma ctx).2
  have hr2 : r ≠ 2 := by rw [hG2r.2]; norm_num
  haveI : ((pCoreOf 2 L).subgroupOf C).Normal := seventeen_fiftyone_cartan_pCore_normal h49 ctx
  have hcomm := (seventeen_fiftyone_cartan_comm_card hKT h49 ctx hZ hshape hq hr hrdvd).1
  have hcardOmega := (seventeen_fiftyone_cartan_comm_card hKT h49 ctx hZ hshape hq hr hrdvd).2.1
  obtain ⟨-, hXexp, -⟩ := seventeen_fiftyone_R_abelian ctx hr hq hrdvd hR hcomm
  haveI : Fact r.Prime := ⟨hr⟩
  have hXp : IsPGroup r (F11.Omega1p r R) :=
    seventeen_fiftyone_omega1p_isPGroup h49 ctx hZ hshape hKT hq hr hrdvd hR
  have hXnc : ¬ IsCyclic ↥(F11.Omega1p r R) :=
    seventeen_fiftyone_omega1p_not_cyclic ctx hr hq hrdvd hR hcomm hcardOmega hXexp
  have hperm : Permutes (F11.Omega1p r R) D.T :=
    seventeen_fiftyone_permutes h49 ctx hZ hshape hKT hq hr hrdvd hR
  have hXR : F11.Omega1p r R ≤ R :=
    (Subgroup.closure_le R).mpr (by rintro x ⟨hx, -⟩; exact hx)
  have hXM : F11.Omega1p r R ≤ D.M :=
    hXR.trans (hR.le.trans (ctx.cartan.1.trans ctx.mem_calC.1.le))
  have hstr3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    seventeen_fiftyone_strong_g2 ctx h880 hG2r.1 hq
  have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M := by
    rw [hG2r.2]; exact hstr3
  exact inP11_of_strongly hr hr2 hstr hXM hXp hXexp hXnc hperm

theorem seventeen_fiftyone
    (D : Data G) (V₀ V : Subgroup G)
    (hV : Hyp125 D V₀ V) (h1 : R17_1At D V₀ V hV)
    (h49 : R17_49At D V₀ V) (h50 : R17_50At D V₀ V)
    (h880 : F08.R880 D) :
    R17_51At D V₀ V := by
  have hU : Inputs1719.K_U4CartanRank := Inputs1719.k_U4CartanRank_holds
  have hSp : Inputs1719.K_Sp4CartanRank := Inputs1719.k_Sp4CartanRank_holds
  have hG : Inputs1719.K_G2CartanRank := Inputs1719.k_G2CartanRank_holds
  intro L X p n l C Dc Gamma ctx r hr hrdvd R hR hGamma
  have hq : 2 < 2 ^ n := (h50 L X p n l C Dc Gamma ctx).2
  have hLX : L = X := h49 L X p n l C Dc Gamma ctx
  have hshape : IsU4 (Bar2 L) n ∨ IsSp4 (Bar2 L) n ∨ IsG2 (Bar2 L) n := by
    have h := (h50 L X p n l C Dc Gamma ctx).1
    rwa [← hLX] at h
  have hZ : Subgroup.center (Bar2 L) = ⊥ := Inputs1719.center_eq_bot_of_rootLineShape hq hshape
  have hKT : Inputs1719.K_LieBorelTorus := Inputs1719.K_LieBorelTorus_of_parts hU hSp hG
  have houter : (∀ (Y : Type) [Group Y] (n : ℕ), IsU4 Y n → IsCyclic
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y)) ∧ (∀ (Y : Type) [Group Y] (n : ℕ),
      IsSp4 Y n → IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y)) ∧ (∀ (Y :
      Type) [Group Y] (n : ℕ), IsG2 Y n → IsCyclic
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      Y)) := Inputs1719.K_LieOuterCyclic_holds
  haveI : ((pCoreOf 2 L).subgroupOf C).Normal :=
    seventeen_fiftyone_cartan_pCore_normal h49 ctx
  have hP11 : F11.InP11 D (F11.Omega1p r R) := by
    by_cases hG2r : IsG2 (Bar2 L) n ∧ r = 3
    · exact seventeen_fiftyone_inP11_of_g2 h49 ctx hZ hshape hKT h880 h50 hr hrdvd hG2r hR
    · exact seventeen_fiftyone_inP11_of_not_g2 h49 ctx hZ hshape hKT h50
        hr hrdvd hG2r hR hGamma
  have hXp : IsPGroup r (F11.Omega1p r R) :=
    seventeen_fiftyone_omega1p_isPGroup h49 ctx hZ hshape hKT hq hr hrdvd hR
  have hPStar : InPStar D V₀ (F11.Omega1p r R) := by
    refine ⟨hP11, ?_⟩
    intro hV0
    refine ⟨r, hr, hXp, Or.inr (Or.inl ?_)⟩
    exact seventeen_fiftyone_omega1_T_cyclic h49 ctx hZ hshape hKT houter hq hr hrdvd hR
  exact h1.1 (F11.Omega1p r R) hPStar

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
