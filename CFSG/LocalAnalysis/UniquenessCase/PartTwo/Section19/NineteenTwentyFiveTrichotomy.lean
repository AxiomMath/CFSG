module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyFive72
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTenTwoComponents
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.CentOverO2Inner
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NOfUniqueShapes
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC22P218d
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21d
public import Mathlib.GroupTheory.OrderOfElement
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OuterCyclic
public import CFSG.LocalAnalysis.SectionRank.Induction
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalGroup
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.GroupTheory.PCore.PCoreOfMul
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13a
public import CFSG.GroupTheory.PGroup.RankTwoCommute
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NotThinShapes
public import CFSG.Quasithin.Vol2.Ch4Sec3L436
public import CFSG.Quasithin.Vol2.Ch6Defs
public import CFSG.Quasithin.Vol2.Ch6Vocab
public import CFSG.Quasithin.Vol2.Ch7Sec77Inputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Trichotomy19_25 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (_h : Ctx19_10 D V₀ V p L A t B r) : Prop :=
  ∀ A₁ : Subgroup G, A₁ ≤ A → Nat.card A₁ = r →
    centralizer (A₁ : Set G) ⊓ IOf D p L ≤ A ⊔ pCoreOf 2 (IOf D p L) ∨
      (1 < CFSG.Open.pRank p (D.M ⊓ centralizer (A₁ : Set G)) ∧
        HasL2SzSection (S17.nOf L) (centralizer (A₁ : Set G) ⊓ IOf D p L)) ∨
      normalizer (A₁ : Set G) ≤ D.M

theorem inter_eq_sup_pCoreOf_of_generic (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (hgen : centralizer (A₀ : Set G) ⊓ IOf D p L ≤ A ⊔ pCoreOf 2 (IOf D p L)) :
    H ⊓ IOf D p L = A ⊔ pCoreOf 2 (H ⊓ IOf D p L) := by
  set I := IOf D p L with hIdef
  have hAH : A ≤ H := A_le_H_of_ctx19_23 h
  have hAI : A ≤ I := h.ctx22.ctx.hA
  have hOO : pCoreOf 2 I ⊓ H ≤ pCoreOf 2 (H ⊓ I) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) ?_ ?_ ?_
    · exact le_inf inf_le_right (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 I))
    · intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I hx.2, Subgroup.le_normalizer hx.1⟩
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I).to_le inf_le_left
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ A ⊔ pCoreOf 2 I := hgen (by rw [← h.hH]; exact hx)
    have hAN : A ≤ normalizer (pCoreOf 2 I : Set G) :=
      hAI.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAN] at hx'
    obtain ⟨a, ha, o, ho, rfl⟩ := hx'
    have hoH : o ∈ H := by
      have he : o = a⁻¹ * (a * o) := by group
      rw [he]
      exact H.mul_mem (H.inv_mem (hAH ha)) hx.1
    exact Subgroup.mul_mem_sup ha (hOO ⟨ho, hoH⟩)
  · exact sup_le (le_inf hAH hAI) (CFSG.LieType.BorelTits.pCoreOf_le 2 _)

theorem concl19_25_of_generic (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (hgen : centralizer (A₀ : Set G) ⊓ IOf D p L ≤ A ⊔ pCoreOf 2 (IOf D p L)) :
    R19_25At D V₀ V p L A t B r A₀ H h := by
  show ((A ⊔ pCoreOf 2 (H ⊓ IOf D p L)).subgroupOf (H ⊓ D.M)).Normal
  rw [← inter_eq_sup_pCoreOf_of_generic D h hgen]
  have hIM : IOf D p L ≤ D.M := IOf_le_M D p h.ctx22.ctx.hyp.hL.1.1.le
  have hKleHM : H ⊓ IOf D p L ≤ H ⊓ D.M := le_inf inf_le_left (inf_le_right.trans hIM)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKleHM]
  intro x hx
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hx.1, le_normalizer_IOf D h.ctx22.ctx.hyp.hL.1 hx.2⟩

theorem generic_of_trichotomy (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (htri : Trichotomy19_25 D V₀ V p L A t B r h.ctx22.ctx)
    (h72 : Gap19_25_72 D V₀ V p L A t B r h.ctx22.ctx) :
    centralizer (A₀ : Set G) ⊓ IOf D p L ≤ A ⊔ pCoreOf 2 (IOf D p L) := by
  have hNle : ¬ normalizer (A₀ : Set G) ≤ D.M := fun hle =>
    h.ctx22.hcent (Subgroup.centralizer_le_normalizer (A₀ : Set G) |>.trans hle)
  obtain hgen | ⟨hrank, hsection⟩ | hN := htri A₀ h.ctx22.hA₀ h.ctx22.hcard
  · exact hgen
  · exact absurd (h72 A₀ h.ctx22.hA₀ h.ctx22.hcard hrank hsection) hNle
  · exact absurd hN hNle

@[expose] def K_19_25_torusCent : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 3 ≤ n → Odd n →
    ∀ T : Subgroup X, IsZModSq T n → ∀ x ∈ T, x ≠ 1 →
      (IsSp4 X n → centralizer ({x} : Set X) = T ∨
        ∃ Y : Subgroup X, Y ≤ centralizer ({x} : Set X) ∧
          ∃ (Z : Subgroup ↥Y) (_ : Z.Normal), IsL2 (↥Y ⧸ Z) n) ∧
      (∀ S₁ S₂ : Subgroup X, S₁.Normal → S₂.Normal → S₁ ⊓ S₂ = ⊥ → S₁ ⊔ S₂ = ⊤ →
        ((IsL2 S₁ n ∧ IsL2 S₂ n) ∨ (IsSz S₁ n ∧ IsSz S₂ n)) →
          x ∈ S₁ ∨ x ∈ S₂ ∨ centralizer ({x} : Set X) = T)

theorem bar_map_centralizer_eq {I A₁ : Subgroup G} {r : ℕ} (hrp : r.Prime)
    (hr2 : r ≠ 2) (hcard : Nat.card A₁ = r) (hA₁I : A₁ ≤ I) :
    ((centralizer (A₁ : Set G) ⊓ I).subgroupOf I).map
        (QuotientGroup.mk' (pCore 2 ↥I)) =
      centralizer ((A₁.subgroupOf I).map (QuotientGroup.mk' (pCore 2 ↥I)) : Set (Bar2 I)) := by
  classical
  haveI : Fact r.Prime := ⟨hrp⟩
  have hcard' : Nat.card ↥(A₁.subgroupOf I) = r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁I).toEquiv, hcard]
  haveI : Fact (IsPGroup r ↥(A₁.subgroupOf I)) :=
    ⟨IsPGroup.of_card (p := r) (n := 1) (by rw [hcard', pow_one])⟩
  have hcop : Nat.Coprime r (Nat.card ↥(pCore 2 ↥I)) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(pCore 2 ↥I))).mp
      (CFSG.pCore_isPGroup (p := 2) (G := ↥I))
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hrp Nat.prime_two).mpr hr2)
  have hsub : (Subgroup.centralizer (A₁.subgroupOf I) : Subgroup ↥I) =
      (centralizer (A₁ : Set G) ⊓ I).subgroupOf I := by
    have h1 : (centralizer (A₁ : Set G) ⊓ I).subgroupOf I =
        (centralizer (A₁ : Set G)).subgroupOf I := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_subgroupOf, and_iff_left]
      exact x.2
    rw [h1]
    ext x
    constructor
    · intro hx a ha
      have h := (Subgroup.mem_centralizer_iff.mp hx) ⟨a, hA₁I ha⟩
        (Subgroup.mem_subgroupOf.mpr ha)
      exact congrArg (fun z : ↥I => (z : G)) h
    · intro hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      apply Subtype.ext
      exact hx y (Subgroup.mem_subgroupOf.mp hy)
  have hmain := CFSG.centralizer_map_quotient_eq_map_centralizer r (A₁.subgroupOf I)
    (pCore 2 ↥I) inferInstance hcop
  rw [hsub] at hmain
  exact hmain.symm

theorem isZModSq_barImage {I A : Subgroup G} {n : ℕ} (hAI : A ≤ I) (hodd : Odd (Nat.card A))
    (hA : IsZModSq A n) : IsZModSq (barImage I A) n := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdisj : Disjoint A (pCoreOf 2 I) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(pCoreOf 2 I))).mp
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I)
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hk]
    exact (Nat.coprime_two_right.mpr hodd).pow_right k
  let f : ↥A →* Bar2 I := (QuotientGroup.mk' (pCore 2 ↥I)).comp (Subgroup.inclusion hAI)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hmem : (Subgroup.inclusion hAI a : ↥I) ∈ pCore 2 ↥I :=
      (QuotientGroup.eq_one_iff _).mp ha
    have hmemG : (a : G) ∈ pCoreOf 2 I := Subgroup.mem_map_of_mem I.subtype hmem
    have hbot : A ⊓ pCoreOf 2 I = ⊥ := disjoint_iff.mp hdisj
    have : (a : G) ∈ A ⊓ pCoreOf 2 I := ⟨a.2, hmemG⟩
    rw [hbot] at this
    exact Subtype.ext (Subgroup.mem_bot.mp this)
  have hinc : (Subgroup.inclusion hAI).range = A.subgroupOf I := by
    ext x
    rw [MonoidHom.mem_range, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.elim fun a ha => ha ▸ a.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hrange : f.range = barImage I A := by
    rw [MonoidHom.range_comp, hinc]
    rfl
  obtain ⟨e⟩ := hA
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm.trans e⟩

theorem exists_centralizer_bar_of_sp4 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (hsp : IsSp4 (Bar2 (IOf D p L)) (S17.nOf L))
    (h638 : UC6.R6_38 D) (hSg : UC6S846.SigmaStd D) :
    ∃ y ∈ F08.CentOverO2 D.M (IOf D p L), orderOf y = p := by
  classical
  set I := IOf D p L with hIdef
  let Inn : Subgroup (MulAut (Bar2 I)) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 I)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hp2⟩ := D.sig_prime p h.hyp.hp
  haveI : Fact p.Prime := ⟨hp⟩
  have hIM : I ≤ D.M := IOf_le_M D p h.hyp.hL.1.1.le
  have hMI : D.M ≤ normalizer (I : Set G) := le_normalizer_IOf D h.hyp.hL.1
  haveI hOut : IsCyclic (Outer (Bar2 I)) :=
    Inputs1719.isCyclic_outer_of_lieModel_PSp4 hsp
  let ψ : ↥D.M →* MulAut (Bar2 I) := (rhoL I).comp (Subgroup.inclusion hMI)
  let φ : ↥D.M →* Outer (Bar2 I) := (QuotientGroup.mk' Inn).comp ψ
  have hker : φ.ker = (I ⊔ F08.CentOverO2 D.M I).subgroupOf D.M := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact ⟨fun hm => mem_sup_centOverO2_of_mem_inner hIM hMI
        ((QuotientGroup.eq_one_iff (ψ m)).mp hm),
      fun hm => (QuotientGroup.eq_one_iff (ψ m)).mpr
        (mem_inner_of_mem_sup_centOverO2 hIM hMI hm)⟩
  have h638p : UC22.F10.OpRes p D.M = D.M := h638 p hp hp2 (Or.inl h.hyp.hp)
  have hresM : CFSG.GH74.GLS.oResidual p ↥D.M = ⊤ := by
    have hop : (CFSG.GH74.GLS.oResidual p ↥D.M).map D.M.subtype = D.M := by
      rw [← UC6.opRes_eq_map_oResidual_uc6 hp D.M, h638p]
    apply (Subgroup.map_subtype_inj (H := D.M)
      (K := CFSG.GH74.GLS.oResidual p ↥D.M) (L := ⊤)).mp
    rw [hop, Subgroup.map_top, Subgroup.range_subtype]
  have hresRange : CFSG.GH74.GLS.oResidual p ↥φ.range = ⊤ := by
    have hmap := CFSG.GH74.GLS.Stage1.Thm6.Prod.map_oResidual φ.rangeRestrict
      φ.rangeRestrict_surjective (p := p) hp
    rw [hresM] at hmap
    rw [← hmap, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr φ.rangeRestrict_surjective
  have hnotdvd : ¬ p ∣ Nat.card ↥φ.range := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥φ.range)
    have hgmem : g ∈ CFSG.GH74.GLS.oResidual p ↥φ.range := hresRange ▸ Subgroup.mem_top g
    rw [← hg]
    exact coprime_orderOf_of_mem_closure _
      (fun x hx => (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.Coprime.symm hx)) hp hgmem
  obtain ⟨E, hEM, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt D.M
  have hk3 : 3 ≤ CFSG.Open.pRank p D.M := hSg.three_le p h.hyp.hp
  by_cases hEint : E ⊓ F08.CentOverO2 D.M I = ⊥
  · exfalso
    have hφE : ∀ e : ↥E, φ (Subgroup.inclusion hEM e) = 1 := by
      intro e
      have h1 : orderOf (φ (Subgroup.inclusion hEM e)) ∣ Nat.card ↥φ.range :=
        Subgroup.orderOf_dvd_natCard φ.range (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
      have h2 : orderOf (φ (Subgroup.inclusion hEM e)) ∣
          orderOf (Subgroup.inclusion hEM e) := orderOf_map_dvd φ _
      obtain ⟨a, ha⟩ := hEel.isPGroup ⟨e, e.2⟩
      have h2' : orderOf (φ (Subgroup.inclusion hEM e)) ∣ p ^ a := by
        apply orderOf_dvd_of_pow_eq_one
        have hpa : (Subgroup.inclusion hEM e) ^ p ^ a = 1 := by
          change (Subgroup.inclusion hEM (⟨e, e.2⟩ : ↥E)) ^ p ^ a = 1
          rw [← map_pow, ha, map_one]
        rw [← map_pow]
        simpa using congrArg φ hpa
      have hcop : Nat.Coprime (p ^ a) (Nat.card ↥φ.range) :=
        Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnotdvd)
      have h3 : orderOf (φ (Subgroup.inclusion hEM e)) = 1 := by
        have hdvd := Nat.dvd_gcd h2' h1
        rw [hcop.gcd_eq_one] at hdvd
        exact Nat.dvd_one.mp hdvd
      exact orderOf_eq_one_iff.mp h3
    have hψinner : ∀ e : ↥E, ψ (Subgroup.inclusion hEM e) ∈ Inn := by
      intro e
      exact (QuotientGroup.eq_one_iff (ψ (Subgroup.inclusion hEM e))).mp (hφE e)
    have hkerψ : ψ.ker = (F08.CentOverO2 D.M I).subgroupOf D.M := by
      symm
      change (F08.CentOverO2 D.M I).subgroupOf D.M =
        ((rhoL I).comp (Subgroup.inclusion hMI)).ker
      rw [← Subgroup.comap_subtype, centOverO2_eq_ker_map hMI]
      exact Subgroup.comap_map_eq_self_of_injective D.M.subtype_injective _
    let Eb : Subgroup ↥D.M := E.subgroupOf D.M
    let F : ↥E →* MulAut (Bar2 I) := ψ.comp (Subgroup.inclusion hEM)
    have hψinj : Function.Injective F := by
      intro e1 e2 heq
      have hmem : (Subgroup.inclusion hEM e1)⁻¹ * (Subgroup.inclusion hEM e2) ∈ ψ.ker := by
        rw [MonoidHom.mem_ker]
        have h : ψ (Subgroup.inclusion hEM e1) = ψ (Subgroup.inclusion hEM e2) := heq
        rw [map_mul, map_inv, h, inv_mul_cancel]
      rw [hkerψ] at hmem
      have hmemG : (e1 : G)⁻¹ * (e2 : G) ∈ F08.CentOverO2 D.M I :=
        Subgroup.mem_subgroupOf.mp hmem
      have hmemE : (e1 : G)⁻¹ * (e2 : G) ∈ E := E.mul_mem (E.inv_mem e1.2) e2.2
      have hbot : (e1 : G)⁻¹ * (e2 : G) ∈ E ⊓ F08.CentOverO2 D.M I := ⟨hmemE, hmemG⟩
      rw [hEint] at hbot
      have h1 : (e1 : G)⁻¹ * (e2 : G) = 1 := Subgroup.mem_bot.mp hbot
      exact Subtype.ext (inv_mul_eq_one.mp h1)
    have hinc : (Subgroup.inclusion hEM).range = Eb := by
      ext x
      rw [MonoidHom.mem_range, Subgroup.mem_subgroupOf]
      exact ⟨fun h => h.elim fun a ha => ha ▸ a.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
    have hFrange : F.range = Eb.map ψ := by
      rw [MonoidHom.range_comp, hinc]
    have hEimg_el : IsElemAbelian p (Eb.map ψ) := by
      have h := CFSG.SectionRank.isElemAbelian_map (p := p) (f := ψ) (hEel.subgroupOf D.M)
      simpa [Eb] using h
    have hcard' : Nat.card (Eb.map ψ) = Nat.card ↥E := by
      rw [← hFrange]
      exact (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
    have hEimg_card : Nat.card (Eb.map ψ) = p ^ CFSG.Open.pRank p D.M := by
      rw [hcard', hEcard]
    have hle : Eb.map ψ ≤ Inn := by
      rintro _ ⟨e, he, rfl⟩
      exact hψinner ⟨e, he⟩
    have hk_le : CFSG.Open.pRank p D.M ≤ CFSG.Open.pRank p Inn :=
      CFSG.SectionRank.le_pRank hp.one_lt hle hEimg_el hEimg_card
    have hcenter : Subgroup.center (Bar2 I) = ⊥ := uc22p218d_center_eq_bot_sp4 hsp
    have hkerconj : (MulAut.conj : Bar2 I →* MulAut (Bar2 I)).ker = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hcent : x ∈ Subgroup.center (Bar2 I) := by
        rw [Subgroup.mem_center_iff]
        intro y
        have hxy : x * y * x⁻¹ = y := congrArg (fun f : MulAut (Bar2 I) => f y) hx
        calc y * x = (x * y * x⁻¹) * x := by rw [hxy]
          _ = x * y := by group
      rw [hcenter] at hcent
      exact Subgroup.mem_bot.mp hcent
    let e0 : Bar2 I ⧸ (MulAut.conj : Bar2 I →* MulAut (Bar2 I)).ker ≃* ↥Inn :=
      QuotientGroup.quotientKerEquivRange _
    let e : ↥Inn ≃* Bar2 I :=
      e0.symm.trans ((QuotientGroup.quotientMulEquivOfEq hkerconj).trans
        QuotientGroup.quotientBot)
    have hInn : CFSG.Open.pRank p Inn ≤ 2 := by
      calc CFSG.Open.pRank p Inn
          = CFSG.Open.pRank p (⊤ : Subgroup ↥Inn) :=
            CFSG.SectionRank.pRank_eq_pRank_top_subgroup Inn
        _ = CFSG.Open.pRank p (⊤ : Subgroup (Bar2 I)) :=
            CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
        _ ≤ 2 := uc22p218d_pRank_le_two_sp4 hsp hp hp2
    omega
  · obtain ⟨z, hz, hz1⟩ : ∃ z : G, z ∈ E ⊓ F08.CentOverO2 D.M I ∧ z ≠ 1 := by
      by_contra hnone
      apply hEint
      rw [eq_bot_iff]
      intro z hz
      by_contra hz1
      exact hnone ⟨z, hz, hz1⟩
    refine ⟨z, hz.2, ?_⟩
    have hzp : z ^ p = 1 := hEel.2 z hz.1
    have hd : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
    rcases hp.eq_one_or_self_of_dvd (orderOf z) hd with h1 | hp'
    · exact absurd (orderOf_eq_one_iff.mp h1) hz1
    · exact hp'

theorem barImage_mem_center_of_commutator_mem {I : Subgroup G} (xI : ↥I)
    (hx : ∀ l : ↥I, xI * l * xI⁻¹ * l⁻¹ ∈ pCore 2 ↥I) :
    QuotientGroup.mk' (pCore 2 ↥I) xI ∈ Subgroup.center (Bar2 I) :=
  CFSG.SectionRank.Ccomm.mk_mem_center_iff.mpr (fun l => by
    simpa [commutatorElement_def] using hx l)

theorem not_mem_IOf_of_sp4 {D : Data G} {p : ℕ} {L : Subgroup G}
    (hsp : IsSp4 (Bar2 (IOf D p L)) (S17.nOf L))
    {y : G} (hyC : y ∈ F08.CentOverO2 D.M (IOf D p L)) (hyord : orderOf y = p)
    (hp : p.Prime) (hp2 : p ≠ 2) : y ∉ IOf D p L := by
  classical
  set I := IOf D p L with hIdef
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hycent⟩ := mem_centOverO2_iff.mp hyC
  intro hyI
  have hcenter : Subgroup.center (Bar2 I) = ⊥ := uc22p218d_center_eq_bot_sp4 hsp
  have hybar_center : QuotientGroup.mk' (pCore 2 ↥I) (⟨y, hyI⟩ : ↥I) ∈
      Subgroup.center (Bar2 I) := by
    refine barImage_mem_center_of_commutator_mem ⟨y, hyI⟩ ?_
    intro l
    have hmemI : y * (l : G) * y⁻¹ * (l : G)⁻¹ ∈ I :=
      I.mul_mem (I.mul_mem (I.mul_mem hyI l.2) (I.inv_mem hyI)) (I.inv_mem l.2)
    have hmem : y * (l : G) * y⁻¹ * (l : G)⁻¹ ∈ pCoreOf 2 I := hycent (l : G) l.2
    exact (CFSG.mem_openPCoreOf_iff (p := 2) (⟨_, hmemI⟩ : ↥I)).mp (by simpa using hmem)
  have hybar1 : QuotientGroup.mk' (pCore 2 ↥I) (⟨y, hyI⟩ : ↥I) = 1 := by
    have h := hybar_center
    rw [hcenter] at h
    exact Subgroup.mem_bot.mp h
  have hyO : y ∈ pCoreOf 2 I :=
    Subgroup.mem_map_of_mem I.subtype ((QuotientGroup.eq_one_iff _).mp hybar1)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 2) (G := ↥(pCoreOf 2 I))).mp
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I) ⟨y, hyO⟩
  rw [Subgroup.orderOf_mk y hyO, hyord] at hk
  have hdvd : p ∣ 2 ^ k := hk ▸ dvd_rfl
  have hd : p ∣ 2 := hp.dvd_of_dvd_pow hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact hp.ne_one h
  · exact hp2 h

theorem exists_fixed_centralizer_of_sp4 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₁ : Subgroup G}
    (h : Ctx19_10 D V₀ V p L A t B r) (hA₁A : A₁ ≤ A) (hA₁card : Nat.card A₁ = r)
    {y : G} (hyC : y ∈ F08.CentOverO2 D.M (IOf D p L)) :
    ∃ c : G, c ∈ D.M ∧ c ∈ centralizer (A₁ : Set G) ∧
      c⁻¹ * y ∈ pCoreOf 2 (IOf D p L) := by
  classical
  set I := IOf D p L with hIdef
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hp2⟩ := D.sig_prime p h.hyp.hp
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨h.hr.1⟩
  have hA₁I : A₁ ≤ I := hA₁A.trans h.hA
  obtain ⟨hyM, hycent⟩ := mem_centOverO2_iff.mp hyC
  have hyN : y ∈ normalizer (I : Set G) := (le_normalizer_IOf D h.hyp.hL.1) hyM
  have hconjO : ∀ z ∈ pCoreOf 2 I, y * z * y⁻¹ ∈ pCoreOf 2 I := by
    intro z hz
    have hmem : y * z * y⁻¹ * z⁻¹ ∈ pCoreOf 2 I :=
      hycent z (CFSG.LieType.BorelTits.pCoreOf_le 2 I hz)
    have heq : y * z * y⁻¹ = (y * z * y⁻¹ * z⁻¹) * z := by group
    exact heq ▸ (pCoreOf 2 I).mul_mem hmem hz
  have hconjOinv : ∀ z ∈ pCoreOf 2 I, y⁻¹ * z * y ∈ pCoreOf 2 I := by
    intro z hz
    have hyinv : y⁻¹ ∈ F08.CentOverO2 D.M I := (F08.CentOverO2 D.M I).inv_mem hyC
    have hmem : y⁻¹ * z * y * z⁻¹ ∈ pCoreOf 2 I := by
      simpa using (mem_centOverO2_iff.mp hyinv).2 z
        (CFSG.LieType.BorelTits.pCoreOf_le 2 I hz)
    have heq : y⁻¹ * z * y = (y⁻¹ * z * y * z⁻¹) * z := by group
    exact heq ▸ (pCoreOf 2 I).mul_mem hmem hz
  have hyO : y ∈ normalizer (pCoreOf 2 I : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro o
    exact ⟨hconjO o, fun ho => by
      have := hconjOinv (y * o * y⁻¹) ho
      have heq : y⁻¹ * (y * o * y⁻¹) * y = o := by group
      rwa [heq] at this⟩
  let H : Subgroup G := I ⊔ Subgroup.zpowers y
  have hIH : I ≤ H := le_sup_left
  have hyH : y ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hA₁H : A₁ ≤ H := hA₁I.trans hIH
  have hHN : H ≤ normalizer (pCoreOf 2 I : Set G) :=
    sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I) (Subgroup.zpowers_le.mpr hyO)
  let N : Subgroup H := (pCoreOf 2 I).subgroupOf H
  have hNle : pCoreOf 2 I ≤ H := (CFSG.LieType.BorelTits.pCoreOf_le 2 I).trans hIH
  haveI : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mpr hHN
  let hAK : A₁ ≤ Subgroup.normalizer (H : Set G) := hA₁H.trans Subgroup.le_normalizer
  letI : MulDistribMulAction (↥A₁) (↥H) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer A₁ H hAK
  have hNinv : CFSG.IsInvariant (↥A₁) (↥H) N := by
    refine CFSG.SolvableHall.isInvariant_of_forall_smul_mem ?_
    intro a x hx
    have hxO : (x : G) ∈ pCoreOf 2 I := Subgroup.mem_subgroupOf.mp hx
    have haI : (a : G) ∈ I := hA₁I a.2
    have hcoe : ((a • x : ↥H) : G) = (a : G) * (x : G) * (a : G)⁻¹ :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit A₁ H hAK a x
    rw [Subgroup.mem_subgroupOf, hcoe]
    exact (Subgroup.mem_normalizer_iff.mp
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I) haI) (x : G)).mp hxO
  have hNp : IsPGroup 2 ↥N := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I).comap_subtype
  have hNsolv : Group.IsSolvable ↥N := CFSG.Quasithin.E1.isSolvable_of_isPGroup_two hNp
  have hNcop : Nat.Coprime (Nat.card ↥A₁) (Nat.card ↥N) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥N)).mp hNp
    rw [hk]
    have hodd : Odd (Nat.card A₁) := by
      rw [show Nat.card A₁ = r from hA₁card]
      exact Odd.of_dvd_nat (odd_card_of_ctx19_10 h) h.hr.2
    exact (Nat.coprime_two_right.mpr hodd).pow_right k
  have hg : ∀ b : ↥A₁,
      (⟨y, hyH⟩ : ↥H)⁻¹ * (b • (⟨y, hyH⟩ : ↥H)) ∈ N := by
    intro b
    rw [Subgroup.mem_subgroupOf]
    have hcoe : ((b • (⟨y, hyH⟩ : ↥H) : ↥H) : G) = (b : G) * y * (b : G)⁻¹ :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit A₁ H hAK b ⟨y, hyH⟩
    have hbI : (b : G) ∈ I := hA₁I b.2
    have hmem : y⁻¹ * (b : G) * y * (b : G)⁻¹ ∈ pCoreOf 2 I := by
      have hyinv : y⁻¹ ∈ F08.CentOverO2 D.M I := (F08.CentOverO2 D.M I).inv_mem hyC
      simpa using (mem_centOverO2_iff.mp hyinv).2 (b : G) hbI
    have heq : ((⟨y, hyH⟩ : ↥H)⁻¹ * (b • (⟨y, hyH⟩ : ↥H)) : ↥H) =
        (⟨y⁻¹ * (b : G) * y * (b : G)⁻¹, hNle hmem⟩ : ↥H) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk, hcoe]
      group
    rw [heq]
    simpa using hmem
  obtain ⟨c, hcFix, hcN⟩ := CFSG.SolvableHall.exists_fixed_of_coset_fixed
    (B := ↥A₁) (G := ↥H) N hNinv hNsolv hNcop ⟨y, hyH⟩ hg
  have hHM : H ≤ D.M :=
    sup_le (IOf_le_M D p h.hyp.hL.1.1.le) (Subgroup.zpowers_le.mpr hyM)
  refine ⟨(c : G), hHM c.2, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hfix := hcFix ⟨a, ha⟩
    have hcoe : (((⟨a, ha⟩ : ↥A₁) • c : ↥H) : G) = a * (c : G) * a⁻¹ :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit A₁ H hAK ⟨a, ha⟩ c
    have hG : a * (c : G) * a⁻¹ = (c : G) := by
      have h := congrArg (fun z : ↥H => (z : G)) hfix
      simpa [hcoe] using h
    calc a * (c : G) = (a * (c : G) * a⁻¹) * a := by group
      _ = (c : G) * a := by rw [hG]
  · have hmemN : ((c⁻¹ * ⟨y, hyH⟩ : ↥H) : G) ∈ pCoreOf 2 I :=
      Subgroup.mem_subgroupOf.mp hcN
    simpa using hmemN

theorem hasL2SzSection_of_comap {n : ℕ} {X : Subgroup G} {Q : Type} [Group Q]
    {f : ↥X →* Q} {W : Subgroup Q} (hW : W ≤ f.range) {S : Type} [Group S]
    (hS : IsL2 S n ∨ IsSz S n) (g : ↥W →* S) (hg : Function.Surjective g) :
    HasL2SzSection n X := by
  classical
  let WX : Subgroup ↥X := W.comap f
  let Y : Subgroup G := WX.map X.subtype
  have hYX : Y ≤ X := Subgroup.map_subtype_le _
  have hYsub : Y.subgroupOf X = WX :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective WX
  let e : ↥Y ≃* ↥WX := (Subgroup.subgroupOfEquivOfLe hYX).symm.trans
    (MulEquiv.subgroupCongr hYsub)
  let fW : ↥WX →* ↥W := (f.comp WX.subtype).codRestrict W
    (fun a => Subgroup.mem_comap.mp a.2)
  have hfW : Function.Surjective fW := by
    rintro ⟨w, hw⟩
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (hW hw)
    refine ⟨⟨x, Subgroup.mem_comap.mpr (by rw [hx]; exact hw)⟩, ?_⟩
    apply Subtype.ext
    dsimp only [fW]
    exact hx
  have hcomp : Function.Surjective (g.comp (fW.comp e.toMonoidHom)) := by
    intro s
    obtain ⟨w, hw⟩ := hg s
    obtain ⟨a, ha⟩ := hfW w
    exact ⟨e.symm a, by simp [ha, hw]⟩
  exact hasL2SzSection_of_surjective hYX hS (g.comp (fW.comp e.toMonoidHom)) hcomp

theorem card_barImage_of_prime_of_le {I A₁ : Subgroup G} {r : ℕ} (hrp : r.Prime)
    (hr2 : r ≠ 2) (hcard : Nat.card A₁ = r) (hA₁I : A₁ ≤ I) :
    Nat.card (barImage I A₁) = r := by
  classical
  haveI : Fact r.Prime := ⟨hrp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard' : Nat.card ↥(A₁.subgroupOf I) = r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁I).toEquiv, hcard]
  have hE : IsPGroup r ↥(A₁.subgroupOf I) :=
    IsPGroup.of_card (p := r) (n := 1) (by rw [hcard', pow_one])
  have hpN : ¬ r ∣ Nat.card ↥(pCore 2 ↥I) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(pCore 2 ↥I))).mp
      (CFSG.pCore_isPGroup (p := 2) (G := ↥I))
    rw [hk]
    intro hdvd
    have h2 : r ∣ 2 := hrp.dvd_of_dvd_pow hdvd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).mp h2)
  rw [show barImage I A₁ = (A₁.subgroupOf I).map (QuotientGroup.mk' (pCore 2 ↥I)) from rfl,
    CFSG.RankThree.PartOne.StrongP.card_map_quotient_of_coprime hE hpN, hcard']

theorem dvd_card_of_isL2_add_one {X : Type} [Group X] [Finite X] {n p : ℕ}
    (h : IsL2 X n) (hpn : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) :
    p ∣ Nat.card X := by
  have hdvd : p ∣ 2 ^ n + 1 :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_dvd_succ hpn
  rw [CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_L2_card h]
  have h2 : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    rw [← Nat.sq_sub_sq, one_pow]
  rw [h2]
  exact (hdvd.mul_right _).mul_left _

theorem barImage_factor_data (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {n : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    {x : G} (hxM : x ∈ D.M)
    (hXsupC : conjClosure D.M L = L ⊔ CFSG.Quasithin.conjSubgroup L x)
    (hneC : conjClosure D.M L ≠ L)
    (hIeq : IOf D p L = L ⊔ CFSG.Quasithin.conjSubgroup L x)
    (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)
    (hn : n = S17.nOf L) :
    (barImage (IOf D p L) L).Normal ∧
      (barImage (IOf D p L) (CFSG.Quasithin.conjSubgroup L x)).Normal ∧
      barImage (IOf D p L) L ⊓ barImage (IOf D p L) (CFSG.Quasithin.conjSubgroup L x) = ⊥ ∧
      barImage (IOf D p L) L ⊔ barImage (IOf D p L) (CFSG.Quasithin.conjSubgroup L x) = ⊤ ∧
      ((IsL2 (barImage (IOf D p L) L) n ∧
          IsL2 (barImage (IOf D p L) (CFSG.Quasithin.conjSubgroup L x)) n) ∨
        (IsSz (barImage (IOf D p L) L) n ∧
          IsSz (barImage (IOf D p L) (CFSG.Quasithin.conjSubgroup L x)) n)) := by
  classical
  set I : Subgroup G := IOf D p L with hI
  set K : Subgroup G := CFSG.Quasithin.conjSubgroup L x with hK
  have hLcalM : L ∈ calC D.M := h.hyp.hL.1
  have hKcalM : K ∈ calC D.M := (S17.conjSubgroup_mem_calC_and_ne hLcalM hxM hXsupC hneC).1
  have hKne : K ≠ L := (S17.conjSubgroup_mem_calC_and_ne hLcalM hxM hXsupC hneC).2
  have hIeqC : I = conjClosure D.M L := hIeq.trans hXsupC.symm
  obtain ⟨-, -, hsubset⟩ := conjSetOf_subset_calC_conjClosure (M := D.M) hLcalM
  have hLcalI : L ∈ calC I := by
    rw [hIeqC]
    exact hsubset L (self_mem_conjSetOf D.M L)
  have hKmem : K ∈ conjSetOf D.M L := ⟨x⁻¹, D.M.inv_mem hxM, rfl⟩
  have hKcalI : K ∈ calC I := by
    rw [hIeqC]
    exact hsubset K hKmem
  let π : ↥I →* Bar2 I := QuotientGroup.mk' (pCore 2 ↥I)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  let S₁ : Subgroup (Bar2 I) := barImage I L
  let S₂ : Subgroup (Bar2 I) := barImage I K
  have hLI : L ≤ I := by rw [hIeq]; exact le_sup_left
  have hKI : K ≤ I := by rw [hIeq]; exact le_sup_right
  have hcomm : ∀ a ∈ S₁, ∀ b ∈ S₂, a * b = b * a := fun a ha b hb =>
    uc22p22l_barImage_commute hLcalI hKcalI hKne.symm a ha b hb
  have hsup : S₁ ⊔ S₂ = ⊤ := by
    have h1 : (L.subgroupOf I) ⊔ (K.subgroupOf I) = ⊤ := by
      have h2 : (L ⊔ K).subgroupOf I = ⊤ := by rw [← hIeq, Subgroup.subgroupOf_self]
      rwa [Subgroup.subgroupOf_sup hLI hKI] at h2
    have hmap : ((L.subgroupOf I) ⊔ (K.subgroupOf I)).map π = ⊤ := by
      rw [h1, Subgroup.map_top, MonoidHom.range_eq_top.mpr hπsurj]
    rwa [Subgroup.map_sup] at hmap
  have hS₁normal : S₁.Normal := uc22p22r_normal_of_commuting hsup hcomm
  have hS₂normal : S₂.Normal :=
    uc22p22r_normal_of_commuting (by rw [sup_comm, hsup])
      (fun p hp q hq => (hcomm q hq p hp).symm)
  have hpair : (IsL2 ↥S₁ n ∧ IsL2 ↥S₂ n) ∨ (IsSz ↥S₁ n ∧ IsSz ↥S₂ n) := by
    obtain ⟨eL, -⟩ := uc22p22l_barImage_equiv (L := I) (K := L) hLcalI
    obtain ⟨eKbar, -⟩ := uc22p22l_barImage_equiv (L := I) (K := K) hKcalI
    obtain ⟨eK⟩ := uc22p20d_bar2_conj x⁻¹ L
    rcases hshape with hL2 | hSz
    · exact Or.inl ⟨LieModel.of_mulEquiv eL hL2,
        LieModel.of_mulEquiv eKbar (LieModel.of_mulEquiv eK hL2)⟩
    · exact Or.inr ⟨LieModel.of_mulEquiv eL hSz,
        LieModel.of_mulEquiv eKbar (LieModel.of_mulEquiv eK hSz)⟩
  have hS₁shape : IsL2 ↥S₁ n ∨ IsSz ↥S₁ n :=
    hpair.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hdisj : S₁ ⊓ S₂ = ⊥ := by
    haveI : IsSimpleGroup ↥S₁ :=
      isSimpleGroup_of_isL2_or_isSz (n := n) hS₁shape
    haveI : Group.IsPerfect ↥S₁ := (uc22p22l_barImage_isComponent hLcalI).1.1
    haveI : (S₁ ⊓ S₂).Normal := inferInstance
    haveI : ((S₁ ⊓ S₂).subgroupOf S₁).Normal := Subgroup.Normal.subgroupOf inferInstance S₁
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((S₁ ⊓ S₂).subgroupOf S₁) with hbot | htop
    · have hd : Disjoint (S₁ ⊓ S₂) S₁ := Subgroup.subgroupOf_eq_bot.mp hbot
      have h := disjoint_iff.mp hd
      simpa [inf_eq_left.mpr inf_le_left] using h
    · exfalso
      have hle : S₁ ≤ S₂ := (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_right
      have hcommS : ∀ a b : ↥S₁, a * b = b * a := by
        intro a b
        apply Subtype.ext
        exact hcomm (a : Bar2 I) a.2 (b : Bar2 I) (hle b.2)
      exact Group.IsPerfect.not_isMulCommutative ↥S₁ (isMulCommutative_iff.mpr hcommS)
  exact ⟨hS₁normal, hS₂normal, hdisj, hsup, hpair⟩

theorem normalizer_le_of_barImage_le (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h3 : S17.R17_3At D V₀ V) (K : Subgroup G) {A₁ : Subgroup G} (hA₁A : A₁ ≤ A)
    (hA₁card : Nat.card A₁ = r) (hKI : K ≤ IOf D p L) (hKcal : K ∈ calC D.M)
    (hKthin : F08.Thin8 K)
    (hle : (A₁.subgroupOf (IOf D p L)).map
        (QuotientGroup.mk' (pCore 2 ↥(IOf D p L))) ≤ barImage (IOf D p L) K) :
    Subgroup.normalizer (A₁ : Set G) ≤ D.M := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I : Subgroup G := IOf D p L with hI
  set Q : Subgroup G := pCoreOf 2 I with hQ
  have hQL : Q ≤ I := CFSG.LieType.BorelTits.pCoreOf_le 2 I
  have hA₁I : A₁ ≤ I := hA₁A.trans h.hA
  have hrp : r.Prime := h.hr.1
  haveI : Fact r.Prime := ⟨hrp⟩
  have hAodd : Odd (Nat.card A) := odd_card_of_ctx19_10 h
  have hr2 : r ≠ 2 := by
    intro h2
    exact hAodd.not_two_dvd_nat (h2 ▸ h.hr.2)
  let π : ↥I →* Bar2 I := QuotientGroup.mk' (pCore 2 ↥I)
  let Y : Subgroup (Bar2 I) := (A₁.subgroupOf I).map π
  have hYcard : Nat.card ↥Y = r :=
    card_barImage_of_prime_of_le (I := I) (A₁ := A₁) hrp hr2 hA₁card hA₁I
  have hYle : Y ≤ barImage I K := hle

  let πK : ↥K →* Bar2 I := π.comp (Subgroup.inclusion hKI)
  have hπLrange : πK.range = barImage I K := by
    rw [MonoidHom.range_comp]
    congr 1
    ext y
    rw [MonoidHom.mem_range, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.elim fun a ha => ha ▸ a.2, fun hy => ⟨⟨y, hy⟩, rfl⟩⟩
  let W : Subgroup ↥K := Y.comap πK
  have hWmap : W.map πK = Y := Subgroup.map_comap_eq_self (by rw [hπLrange]; exact hYle)
  have hrW : r ∣ Nat.card ↥W := by
    have hdvd : Nat.card ↥Y ∣ Nat.card ↥W := by
      have hc := Subgroup.card_map_dvd W πK
      rwa [hWmap] at hc
    rwa [hYcard] at hdvd
  obtain ⟨xW, hxWord⟩ := exists_prime_orderOf_dvd_card' r hrW
  let x : G := (xW : ↥K)
  have hxL : x ∈ K := (xW : ↥K).2
  have hxord : orderOf x = r := by
    change orderOf ((xW : ↥K) : G) = r
    rw [Subgroup.orderOf_coe (xW : ↥K), Subgroup.orderOf_coe xW, hxWord]
  have hxI : x ∈ I := hKI hxL
  let xI : ↥I := ⟨x, hxI⟩
  have hxY : π xI ∈ Y := (xW : W).2
  have hxbar_ord : orderOf (π xI) = r := by
    have hdvd : orderOf (π xI) ∣ orderOf xI := orderOf_map_dvd π xI
    rw [← Subgroup.orderOf_coe xI, hxord] at hdvd
    have hne : π xI ≠ 1 := by
      intro h1
      have hmem : x ∈ Q := by
        have h2 : xI ∈ pCore 2 ↥I := (QuotientGroup.eq_one_iff _).mp h1
        exact (CFSG.mem_openPCoreOf_iff xI).mpr h2
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I).exists_card_eq
      have hd : orderOf x ∣ Nat.card (Q : Subgroup G) := Subgroup.orderOf_dvd_natCard _ hmem
      rw [hk] at hd
      have hdiv : r ∣ 2 ^ k := by rwa [hxord] at hd
      have h2 : r ∣ 2 := hrp.dvd_of_dvd_pow hdiv
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).mp h2)
    rcases hrp.eq_one_or_self_of_dvd (orderOf (π xI)) hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hne
    · exact h1
  have hYeq : Y = Subgroup.zpowers (π xI) := by
    refine (Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers (π xI)) (K := Y)
      (Subgroup.zpowers_le.mpr hxY) ?_).symm
    rw [Nat.card_zpowers, hxbar_ord, hYcard]
  let X : Subgroup G := Subgroup.zpowers x
  have hXL : X ≤ K := Subgroup.zpowers_le.mpr hxL
  have hXI : X ≤ I := hXL.trans hKI
  have hXcard : Nat.card X = r := by
    rw [Nat.card_zpowers, hxord]
  have hA₁le : A₁ ≤ X ⊔ Q := by
    intro a ha
    have hale : π ⟨a, hA₁I ha⟩ ∈ Y := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ha)
    rw [hYeq] at hale
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hale
    have hxna : x ^ n * a⁻¹ ∈ Q := by
      have h1 : π ⟨x ^ n * a⁻¹, I.mul_mem (Subgroup.zpow_mem I hxI n)
          (I.inv_mem (hA₁I ha))⟩ = (π xI) ^ n * (π ⟨a, hA₁I ha⟩)⁻¹ := rfl
      rw [hn, mul_inv_cancel] at h1
      have h2 : (⟨x ^ n * a⁻¹, I.mul_mem (Subgroup.zpow_mem I hxI n)
          (I.inv_mem (hA₁I ha))⟩ : ↥I) ∈ pCore 2 ↥I := (QuotientGroup.eq_one_iff _).mp h1
      exact (CFSG.mem_openPCoreOf_iff _).mpr h2
    have he : a = (x ^ n * a⁻¹)⁻¹ * x ^ n := by group
    rw [he]
    have hmem : (x ^ n * a⁻¹)⁻¹ * x ^ n ∈ Q ⊔ X :=
      Subgroup.mul_mem_sup (Q.inv_mem hxna)
        (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩)
    rwa [sup_comm] at hmem
  have hXle : X ≤ A₁ ⊔ Q := by
    obtain ⟨a, haA, haπ⟩ := Subgroup.mem_map.mp hxY
    have haG : (a : G) ∈ A₁ := Subgroup.mem_subgroupOf.mp haA
    let aG : G := (a : G)
    have hxa : x * aG⁻¹ ∈ Q := by
      have h1 : π ⟨x * aG⁻¹, I.mul_mem hxI (I.inv_mem (hA₁I haG))⟩ = 1 := by
        change π xI * (π a)⁻¹ = 1
        rw [haπ, mul_inv_cancel]
      have h2 : (⟨x * aG⁻¹, I.mul_mem hxI (I.inv_mem (hA₁I haG))⟩ : ↥I) ∈ pCore 2 ↥I :=
        (QuotientGroup.eq_one_iff _).mp h1
      exact (CFSG.mem_openPCoreOf_iff _).mpr h2
    have hxSup : x ∈ A₁ ⊔ Q := by
      have hmem : (x * aG⁻¹) * aG ∈ Q ⊔ A₁ :=
        Subgroup.mul_mem_sup hxa haG
      have he : (x * aG⁻¹) * aG = x := by group
      have hmem' : x ∈ Q ⊔ A₁ := by simpa [he] using hmem
      simpa [sup_comm] using hmem'
    exact Subgroup.zpowers_le.mpr hxSup
  have hsup : A₁ ⊔ Q = X ⊔ Q := le_antisymm (sup_le hA₁le le_sup_right) (sup_le hXle le_sup_right)
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I
  have hPQ : A₁ ⊔ Q ≤ Subgroup.normalizer (Q : Set G) := by
    refine sup_le ?_ Subgroup.le_normalizer
    exact hA₁I.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I)
  have hQM : Q ⊓ X = ⊥ := by
    have hcop : Nat.Coprime (Nat.card ↥Q) (Nat.card ↥X) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥Q)).mp hQp
      rw [hk, hXcard]
      exact Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hrp).mpr hr2.symm)
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hXnormQ : X ≤ Subgroup.normalizer (Q : Set G) :=
    hXL.trans (hKI.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I))
  have hdec : ∀ g ∈ A₁ ⊔ Q, ∃ q ∈ Q, ∃ m ∈ X, q * m = g := by
    intro g hg
    have hg' : g ∈ (Q ⊔ X : Subgroup G) := by
      rw [sup_comm, ← hsup]
      exact hg
    have hprod : ((Q ⊔ X : Subgroup G) : Set G) = (Q : Set G) * (X : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left Q X hXnormQ
    have hg'' : g ∈ (Q : Set G) * (X : Set G) := by
      rw [← hprod]
      exact hg'
    obtain ⟨q, hq, m, hm, rfl⟩ := hg''
    exact ⟨q, hq, m, hm, rfl⟩
  have hS : ¬ 2 ∣ Nat.card ↥A₁ := by
    rw [hA₁card]
    exact fun h2 => hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hrp).mp h2).symm
  obtain ⟨y, hyQ, hyconj⟩ :=
    CFSG.LieType.Chevalley.EvenOddRadical.exists_conj_le_of_complement (p := 2)
      (P := A₁ ⊔ Q) (Q := Q) (M := X) (S := A₁) hQp
      le_sup_right hPQ hQM hdec le_sup_left hS
  have hyI : y ∈ I := hQL hyQ
  have hyM : y ∈ D.M := IOf_le_M D p (S17.calLp_subset_calC D p h.hyp.hL).1.le hyI
  have hAyL : A₁.map (MulAut.conj y).toMonoidHom ≤ K := hyconj.trans hXL
  have hAycard : Nat.card (A₁.map (MulAut.conj y).toMonoidHom) = r := by
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective, hA₁card]
  have hNAy : Subgroup.normalizer ((A₁.map (MulAut.conj y).toMonoidHom) : Set G) ≤ D.M :=
    h3 K hKcal hKthin (A₁.map (MulAut.conj y).toMonoidHom)
      ⟨r, hrp, hr2, hAycard, hAyL⟩
  have hyinvM : y⁻¹ ∈ D.M := D.M.inv_mem hyM
  have hback : (A₁.map (MulAut.conj y).toMonoidHom).map
      (MulAut.conj y⁻¹).toMonoidHom = A₁ := by
    ext a
    constructor
    · rintro ⟨b, ⟨c, hc, hbc⟩, hb⟩
      change (MulAut.conj y) c = b at hbc
      change (MulAut.conj y⁻¹) b = a at hb
      rw [MulAut.conj_apply] at hb
      rw [MulAut.conj_apply] at hbc
      rw [← hbc] at hb
      have hca : c = a := by
        rw [← hb]
        group
      simpa [hca] using hc
    · intro ha
      refine ⟨y * a * y⁻¹, ⟨a, ha, rfl⟩, ?_⟩
      change (MulAut.conj y⁻¹) (y * a * y⁻¹) = a
      rw [MulAut.conj_apply]
      group
  have hmapN := Subgroup.map_equiv_normalizer_eq
    (H := A₁.map (MulAut.conj y).toMonoidHom) (MulAut.conj y⁻¹)
  rw [hback] at hmapN
  intro z hz
  rw [← hmapN] at hz
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
  change (MulAut.conj y⁻¹) w ∈ D.M
  rw [MulAut.conj_apply]
  exact D.M.mul_mem (D.M.mul_mem hyinvM (hNAy hw)) (D.M.inv_mem hyinvM)

private theorem sp4_branch_setup (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    {A₁ : Subgroup G} (hA₁A : A₁ ≤ A) (hA₁card : Nat.card A₁ = r) :
    ∃ (x0 : Bar2 (IOf D p L)) (hT : IsZModSq (barImage (IOf D p L) A) (S17.nOf L)),
      x0 ∈ barImage (IOf D p L) A ∧ x0 ≠ 1 ∧
      ((A₁.subgroupOf (IOf D p L)).map
          (QuotientGroup.mk' (pCore 2 ↥(IOf D p L))) = Subgroup.zpowers x0) ∧
      (Subgroup.centralizer (Subgroup.zpowers x0 : Set (Bar2 (IOf D p L))) =
        Subgroup.centralizer ({x0} : Set (Bar2 (IOf D p L)))) ∧
      (Subgroup.centralizer ({x0} : Set (Bar2 (IOf D p L))) =
        barImage (IOf D p L) A →
        Subgroup.centralizer (A₁ : Set G) ⊓ IOf D p L ≤ A ⊔ pCoreOf 2 (IOf D p L)) := by
  classical
  let I : Subgroup G := IOf D p L
  let n : ℕ := S17.nOf L
  have hp : p.Prime := (D.sig_prime p h.hyp.hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p h.hyp.hp).2
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrp : r.Prime := h.hr.1
  haveI : Fact r.Prime := ⟨hrp⟩
  have hA₁I : A₁ ≤ I := hA₁A.trans h.hA
  have hAodd : Odd (Nat.card A) := odd_card_of_ctx19_10 h
  have hr2 : r ≠ 2 := by
    intro h2
    exact hAodd.not_two_dvd_nat (h2 ▸ h.hr.2)
  have hT : IsZModSq (barImage I A) n := isZModSq_barImage h.hA hAodd h.hAcard
  haveI hcyc : IsCyclic ↥A₁ := isCyclic_of_card_dvd_prime (p := r) (by rw [hA₁card])
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := ↥A₁)
  let g : G := (a : G)
  have hgA₁ : g ∈ A₁ := a.2
  have hgA : g ∈ A := hA₁A hgA₁
  have hgold : orderOf g = r := by
    have htop : Subgroup.zpowers a = ⊤ := eq_top_iff.mpr (fun x _ => ha x)
    have h2 : Nat.card (Subgroup.zpowers a) = r := by
      rw [htop, Subgroup.card_top, hA₁card]
    rw [← h2, Nat.card_zpowers, Subgroup.orderOf_coe]
  have hgen : A₁ = Subgroup.zpowers g := by
    refine (Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers g) (K := A₁)
      (Subgroup.zpowers_le.mpr hgA₁) ?_).symm
    rw [Nat.card_zpowers, hgold, hA₁card]
  have hgI : g ∈ I := hA₁I hgA₁
  let x0 : Bar2 I := QuotientGroup.mk' (pCore 2 ↥I) ⟨g, hgI⟩
  have hx0T : x0 ∈ barImage I A :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hgA)
  have hx0ne : x0 ≠ 1 := by
    intro h1
    have hmem : g ∈ pCoreOf 2 I := by
      have h2 : (⟨g, hgI⟩ : ↥I) ∈ pCore 2 ↥I := (QuotientGroup.eq_one_iff _).mp h1
      exact Subgroup.mem_map_of_mem I.subtype h2
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I).exists_card_eq
    have hdvd : orderOf g ∣ Nat.card (pCoreOf 2 I) := Subgroup.orderOf_dvd_natCard _ hmem
    rw [hk] at hdvd
    have hdiv : r ∣ 2 ^ k := by rwa [hgold] at hdvd
    have h2 : r ∣ 2 := hrp.dvd_of_dvd_pow hdiv
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).mp h2)
  have himgA₁ : (A₁.subgroupOf I).map (QuotientGroup.mk' (pCore 2 ↥I)) =
      Subgroup.zpowers x0 := by
    rw [hgen]
    have hsub : (Subgroup.zpowers g).subgroupOf I =
        Subgroup.zpowers (⟨g, hgI⟩ : ↥I) := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, Subtype.ext hk⟩
      · rintro ⟨k, hk⟩
        exact ⟨k, congrArg Subtype.val hk⟩
    rw [hsub, MonoidHom.map_zpowers]
  have hcentz : Subgroup.centralizer (Subgroup.zpowers x0 : Set (Bar2 I)) =
      Subgroup.centralizer ({x0} : Set (Bar2 I)) := by
    apply le_antisymm
    · refine Subgroup.centralizer_le ?_
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
    · intro x hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((commute_iff_eq x0 x).mpr (hx x0 (by simp))).zpow_left k |>.eq
  have hgeneric_of_cent : Subgroup.centralizer ({x0} : Set (Bar2 I)) = barImage I A →
      Subgroup.centralizer (A₁ : Set G) ⊓ I ≤ A ⊔ pCoreOf 2 I := by
    intro hcent x hx
    have hmap := bar_map_centralizer_eq (I := I) (A₁ := A₁) hrp hr2 hA₁card hA₁I
    have himg : ((Subgroup.centralizer (A₁ : Set G) ⊓ I).subgroupOf I).map
        (QuotientGroup.mk' (pCore 2 ↥I)) = barImage I A := by
      rw [hmap, himgA₁, hcentz, hcent]
    have hxbar : (QuotientGroup.mk' (pCore 2 ↥I) ⟨x, hx.2⟩) ∈ barImage I A := by
      rw [← himg]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
    obtain ⟨a, haA, haeq⟩ := Subgroup.mem_map.mp hxbar
    have haG : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp haA
    have hmemO : (a : G)⁻¹ * x ∈ pCoreOf 2 I := by
      have h1 : QuotientGroup.mk' (pCore 2 ↥I) (a⁻¹ * ⟨x, hx.2⟩) = 1 := by
        rw [map_mul, map_inv, haeq]
        group
      have h2 : (a⁻¹ * ⟨x, hx.2⟩ : ↥I) ∈ pCore 2 ↥I := (QuotientGroup.eq_one_iff _).mp h1
      have h3 : ((a⁻¹ * ⟨x, hx.2⟩ : ↥I) : G) ∈ pCoreOf 2 I :=
        Subgroup.mem_map_of_mem I.subtype h2
      simpa using h3
    have hxeq : x = (a : G) * ((a : G)⁻¹ * x) := by group
    rw [hxeq]
    exact Subgroup.mul_mem_sup haG hmemO
  refine ⟨x0, ?_, hx0T, hx0ne, himgA₁, hcentz, ?_⟩
  · simpa [I, n] using hT
  · intro hcent
    simpa [I] using hgeneric_of_cent hcent

theorem sp4_trichotomy_branch (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (hodd : Odd (S17.nOf L)) (hsp : IsSp4 (Bar2 (IOf D p L)) (S17.nOf L))
    (hcong : (2 : ℤ) ^ (S17.nOf L) ≡ -1 [ZMOD (p : ℤ)])
    (h638 : UC6.R6_38 D) (hSg : UC6S846.SigmaStd D) (hK : K_19_25_torusCent)
    {A₁ : Subgroup G} (hA₁A : A₁ ≤ A) (hA₁card : Nat.card A₁ = r) :
    (Subgroup.centralizer (A₁ : Set G) ⊓ IOf D p L ≤ A ⊔ pCoreOf 2 (IOf D p L)) ∨
      (1 < CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (A₁ : Set G)) ∧
        HasL2SzSection (S17.nOf L)
          (Subgroup.centralizer (A₁ : Set G) ⊓ IOf D p L)) := by
  classical
  set I : Subgroup G := IOf D p L with hI
  set n : ℕ := S17.nOf L with hn
  have hp : p.Prime := (D.sig_prime p h.hyp.hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p h.hyp.hp).2
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrp : r.Prime := h.hr.1
  haveI : Fact r.Prime := ⟨hrp⟩
  have hA₁I : A₁ ≤ I := hA₁A.trans h.hA
  have hAodd : Odd (Nat.card A) := odd_card_of_ctx19_10 h
  have hr2 : r ≠ 2 := by
    intro h2
    exact hAodd.not_two_dvd_nat (h2 ▸ h.hr.2)
  have hn3 : 3 ≤ n := three_le_nOf_of_setting1910 h.h1910
  have hIleM : I ≤ D.M := IOf_le_M D p (S17.calLp_subset_calC D p h.hyp.hL).1.le
  obtain ⟨x0, hT0, hx0T, hx0ne, himgA₁0, hcentz0, hgeneric_of_cent0⟩ :=
    sp4_branch_setup D h hA₁A hA₁card
  have hT : IsZModSq (barImage I A) n := by simpa [I, n] using hT0
  have himgA₁ : (A₁.subgroupOf I).map (QuotientGroup.mk' (pCore 2 ↥I)) =
      Subgroup.zpowers x0 := by simpa [I] using himgA₁0
  have hcentz : Subgroup.centralizer (Subgroup.zpowers x0 : Set (Bar2 I)) =
      Subgroup.centralizer ({x0} : Set (Bar2 I)) := by simpa [I] using hcentz0
  have hgeneric_of_cent : Subgroup.centralizer ({x0} : Set (Bar2 I)) = barImage I A →
      Subgroup.centralizer (A₁ : Set G) ⊓ I ≤ A ⊔ pCoreOf 2 I := by
    intro hcent
    simpa [I] using hgeneric_of_cent0 (by simpa [I] using hcent)

  have hcongn : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] := by rw [hn]; exact hcong
  have hKsp := (hK (Bar2 I) n hn3 hodd (barImage I A) hT x0 hx0T hx0ne).1 hsp
  rcases hKsp with hcent | ⟨Y, hYle, Z, hZ, hY2⟩
  · exact Or.inl (hgeneric_of_cent hcent)
  ·
    haveI hZn : Z.Normal := hZ
    let X : Subgroup G := Subgroup.centralizer (A₁ : Set G) ⊓ I
    have hXI : X ≤ I := inf_le_right
    let f : ↥X →* Bar2 I :=
      (QuotientGroup.mk' (pCore 2 ↥I)).comp (Subgroup.inclusion hXI)
    have hfr : f.range = Subgroup.centralizer ({x0} : Set (Bar2 I)) := by
      have h1 : f.range = (X.subgroupOf I).map (QuotientGroup.mk' (pCore 2 ↥I)) := by
        rw [MonoidHom.range_comp]
        congr 1
        ext y
        rw [MonoidHom.mem_range, Subgroup.mem_subgroupOf]
        exact ⟨fun h => h.elim fun a ha => ha ▸ a.2, fun hy => ⟨⟨y, hy⟩, rfl⟩⟩
      rw [h1, bar_map_centralizer_eq (I := I) (A₁ := A₁) hrp hr2 hA₁card hA₁I,
        himgA₁, hcentz]
    have hsec : HasL2SzSection n X :=
      hasL2SzSection_of_comap (n := n) (X := X) (f := f) (W := Y)
        (by rw [hfr]; exact hYle) (Or.inl hY2) (QuotientGroup.mk' Z)
        (QuotientGroup.mk'_surjective Z)
    refine Or.inr ⟨?_, hsec⟩
    have hpdvdS : p ∣ Nat.card (↥Y ⧸ Z) := dvd_card_of_isL2_add_one hY2 hcongn
    have hpY : p ∣ Nat.card ↥Y := hpdvdS.trans (Subgroup.card_quotient_dvd_card Z)
    let W : Subgroup ↥X := Y.comap f
    have hmapW : W.map f = Y := Subgroup.map_comap_eq_self (by rw [hfr]; exact hYle)
    have hpW : p ∣ Nat.card ↥W := by
      have hdvd : Nat.card ↥Y ∣ Nat.card ↥W := by
        have h := Subgroup.card_map_dvd W f
        rwa [hmapW] at h
      exact hpY.trans hdvd
    obtain ⟨zW, hzWord⟩ := exists_prime_orderOf_dvd_card' p hpW
    let z : G := ((zW : ↥X) : G)
    have hzX : z ∈ X := (zW : ↥X).2
    have hzCent : z ∈ Subgroup.centralizer (A₁ : Set G) := hzX.1
    have hzI : z ∈ I := hzX.2
    have hzord : orderOf z = p := by
      change orderOf ((zW : ↥X) : G) = p
      rw [Subgroup.orderOf_coe (zW : ↥X), Subgroup.orderOf_coe zW, hzWord]
    have hzp : z ^ p = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
    obtain ⟨y, hyC, hyord⟩ := exists_centralizer_bar_of_sp4 D h hsp h638 hSg
    obtain ⟨c, hcM, hcCent, hcO⟩ :=
      exists_fixed_centralizer_of_sp4 D h hA₁A hA₁card hyC
    have hyNotI : y ∉ I := not_mem_IOf_of_sp4 (D := D) hsp hyC hyord hp hp2
    have hyM : y ∈ D.M := (mem_centOverO2_iff.mp hyC).1
    have hyNO : y ∈ Subgroup.normalizer (pCoreOf 2 I : Set G) :=
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.normalizer_le_normalizer_pCoreOf I)
        ((le_normalizer_IOf D h.hyp.hL.1) hyM)
    have hcNotI : c ∉ I := by
      intro hcI
      refine hyNotI ?_
      have he : y = c * (c⁻¹ * y) := by group
      rw [he]
      exact I.mul_mem hcI ((CFSG.LieType.BorelTits.pCoreOf_le 2 I) hcO)
    have hcNO : c ∈ Subgroup.normalizer (pCoreOf 2 I : Set G) :=
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.normalizer_le_normalizer_pCoreOf I)
        ((le_normalizer_IOf D h.hyp.hL.1) hcM)
    have hcComm : ∀ l ∈ I, c * l * c⁻¹ * l⁻¹ ∈ pCoreOf 2 I :=
      CFSG.GroupTheory.commutator_mem_pCoreOf_of_mem_mul (L := I)
        (fun l hl => (mem_centOverO2_iff.mp hyC).2 l hl) hyNO hcO
    have hyp : y ^ p = 1 := by rw [← hyord]; exact pow_orderOf_eq_one y
    have hcpO : c ^ p ∈ pCoreOf 2 I :=
      CFSG.GroupTheory.pow_mem_pCoreOf_of_mem_mul (L := I) hyp hcO hcNO hyNO
    let H : Subgroup G := D.M ⊓ Subgroup.centralizer (A₁ : Set G)
    let N : Subgroup ↥H := (pCoreOf 2 I).subgroupOf H
    have hNnormal : N.Normal := by
      refine Subgroup.Normal.mk ?_
      intro nn hnn g
      rw [Subgroup.mem_subgroupOf] at hnn ⊢
      have hgNO : (g : G) ∈ Subgroup.normalizer (pCoreOf 2 I : Set G) :=
        (CFSG.LocalAnalysis.UniquenessCase.UC6S846.normalizer_le_normalizer_pCoreOf I)
          ((le_normalizer_IOf D h.hyp.hL.1) g.2.1)
      exact (Subgroup.mem_normalizer_iff.mp hgNO (nn : G)).mp hnn
    have hNp : IsPGroup 2 N :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I).comap_subtype
    have hcH : c ∈ H := ⟨hcM, hcCent⟩
    have hzH : z ∈ H := ⟨hIleM hzI, hzCent⟩
    let cH : ↥H := ⟨c, hcH⟩
    let zH : ↥H := ⟨z, hzH⟩
    let Q := ↥H ⧸ N
    let cN : Q := QuotientGroup.mk' N cH
    let zN : Q := QuotientGroup.mk' N zH
    have hcNpow : cN ^ p = 1 := by
      show (QuotientGroup.mk' N cH) ^ p = 1
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hcpO)
    have hcNne : cN ≠ 1 := by
      intro h1
      have hmemN : cH ∈ N := (QuotientGroup.eq_one_iff _).mp h1
      have hcPI : c ∈ pCoreOf 2 I := Subgroup.mem_subgroupOf.mp hmemN
      exact hcNotI ((CFSG.LieType.BorelTits.pCoreOf_le 2 I) hcPI)
    have hcNp : orderOf cN = p := by
      have hdvd : orderOf cN ∣ p := orderOf_dvd_of_pow_eq_one hcNpow
      rcases hp.eq_one_or_self_of_dvd (orderOf cN) hdvd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hcNne
      · exact h1
    have hzNpow : zN ^ p = 1 := by
      show (QuotientGroup.mk' N zH) ^ p = 1
      rw [← map_pow]
      have hzHp : zH ^ p = (⟨z ^ p, H.pow_mem hzH p⟩ : ↥H) := rfl
      have hzHp1 : (⟨z ^ p, H.pow_mem hzH p⟩ : ↥H) = 1 := Subtype.ext (by simpa using hzp)
      rw [hzHp, hzHp1, map_one]
    have hzNne : zN ≠ 1 := by
      intro h1
      have hmemN : zH ∈ N := (QuotientGroup.eq_one_iff _).mp h1
      have hzPI : z ∈ pCoreOf 2 I := Subgroup.mem_subgroupOf.mp hmemN
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I).exists_card_eq
      have hdvd : orderOf z ∣ Nat.card (pCoreOf 2 I) := Subgroup.orderOf_dvd_natCard _ hzPI
      rw [hk] at hdvd
      have hdiv : p ∣ 2 ^ k := by rwa [hzord] at hdvd
      have h2 : p ∣ 2 := hp.dvd_of_dvd_pow hdiv
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    have hzNp : orderOf zN = p := by
      have hdvd : orderOf zN ∣ p := orderOf_dvd_of_pow_eq_one hzNpow
      rcases hp.eq_one_or_self_of_dvd (orderOf zN) hdvd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hzNne
      · exact h1
    have hczN : cH * zH * cH⁻¹ * zH⁻¹ ∈ N :=
      Subgroup.mem_subgroupOf.mpr (hcComm z hzI)
    have hcz_comm : QuotientGroup.mk' N (cH * zH) = QuotientGroup.mk' N (zH * cH) := by
      change ((cH * zH : ↥H) : Q) = ((zH * cH : ↥H) : Q)
      rw [QuotientGroup.eq_iff_div_mem]
      simpa [div_eq_mul_inv, mul_assoc] using hczN
    have hcommute : Commute cN zN := by
      rw [commute_iff_eq]
      change QuotientGroup.mk' N (cH * zH) = QuotientGroup.mk' N (zH * cH)
      exact hcz_comm
    have hindep : zN ∉ Subgroup.zpowers cN := by
      intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hmemN : (cH ^ k)⁻¹ * zH ∈ N := by
        rw [← QuotientGroup.eq]
        change QuotientGroup.mk' N (cH ^ k) = QuotientGroup.mk' N zH
        rw [map_zpow]
        exact hk
      have hmemO : (((cH ^ k)⁻¹ * zH : ↥H) : G) ∈ pCoreOf 2 I :=
        Subgroup.mem_subgroupOf.mp hmemN
      have hmemOg : c ^ (-k) * z ∈ pCoreOf 2 I := by
        simpa [cH, zH] using hmemO
      have hckI : c ^ k ∈ I := by
        have he : c ^ k = z * (c ^ (-k) * z)⁻¹ := by
          rw [zpow_neg]
          group
        rw [he]
        exact I.mul_mem hzI (I.inv_mem ((CFSG.LieType.BorelTits.pCoreOf_le 2 I) hmemOg))
      have hck_bar : QuotientGroup.mk' (pCore 2 ↥I) ⟨c ^ k, hckI⟩ =
          QuotientGroup.mk' (pCore 2 ↥I) ⟨z, hzI⟩ := by
        change ((⟨c ^ k, hckI⟩ : ↥I) : Bar2 I) = ((⟨z, hzI⟩ : ↥I) : Bar2 I)
        rw [QuotientGroup.eq, ← CFSG.mem_openPCoreOf_iff]
        simpa [zpow_neg] using hmemOg
      have hckCB : CentralizesBar (c ^ k) I :=
        uc22p21d_centralizesBar_of_mem_zpowers
          ((uc22p21d_centralizesBar_iff).mpr hcComm)
            (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
      have hck_center : QuotientGroup.mk' (pCore 2 ↥I) ⟨c ^ k, hckI⟩ ∈
          Subgroup.center (Bar2 I) := by
        refine barImage_mem_center_of_commutator_mem ⟨c ^ k, hckI⟩ ?_
        intro l
        rw [← CFSG.mem_openPCoreOf_iff]
        exact hckCB.2 (l : G) l.2
      have hz_center : QuotientGroup.mk' (pCore 2 ↥I) ⟨z, hzI⟩ ∈
          Subgroup.center (Bar2 I) := by
        rw [← hck_bar]
        exact hck_center
      have hz_bar_ne : QuotientGroup.mk' (pCore 2 ↥I) ⟨z, hzI⟩ ≠ 1 := by
        intro h1
        have hzPI : (⟨z, hzI⟩ : ↥I) ∈ pCore 2 ↥I := (QuotientGroup.eq_one_iff _).mp h1
        have hzO : z ∈ pCoreOf 2 I := (CFSG.mem_openPCoreOf_iff _).mpr hzPI
        obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I).exists_card_eq
        have hdvd : orderOf z ∣ Nat.card (pCoreOf 2 I) := Subgroup.orderOf_dvd_natCard _ hzO
        rw [hm] at hdvd
        have hdiv : p ∣ 2 ^ m := by rwa [hzord] at hdvd
        have h2 : p ∣ 2 := hp.dvd_of_dvd_pow hdiv
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
      have hcenter : Subgroup.center (Bar2 I) = ⊥ := uc22p218d_center_eq_bot_sp4 hsp
      have hbot : QuotientGroup.mk' (pCore 2 ↥I) ⟨z, hzI⟩ ∈ (⊥ : Subgroup (Bar2 I)) := by
        rw [← hcenter]
        exact hz_center
      exact hz_bar_ne (Subgroup.mem_bot.mp hbot)
    have h2p : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup Q) :=
      CFSG.GroupTheory.two_le_pRank_of_commute (H := ⊤) (x := cN) (y := zN)
        (Subgroup.mem_top cN) (Subgroup.mem_top zN) hcNp hzNp hcommute hindep
    have hquot := CFSG.SectionRank.pRank_quotient_two_group (G := ↥H) N hNp hp hp2
    have htop := CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) H
    have hH : 2 ≤ CFSG.Open.pRank p H := by
      rw [htop, ← hquot]
      exact h2p
    exact lt_of_lt_of_le (by norm_num : 1 < 2) hH

theorem product_case_of_shape (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (hodd : Odd (S17.nOf L)) (h3 : S17.R17_3At D V₀ V) (hK : K_19_25_torusCent)
    {A₁ : Subgroup G} (hA₁A : A₁ ≤ A) (hA₁card : Nat.card A₁ = r)
    (hIeqC : IOf D p L = conjClosure D.M L) (hneC : conjClosure D.M L ≠ L)
    (hn2 : 2 < S17.nOf L)
    (hLshape : (IsL2 (Bar2 L) (S17.nOf L) ∧
        (2 : ℤ) ^ S17.nOf L ≡ -1 [ZMOD (p : ℤ)]) ∨
      (IsSz (Bar2 L) (S17.nOf L) ∧
        (2 : ℤ) ^ (2 * S17.nOf L) ≡ -1 [ZMOD (p : ℤ)]))
    {x : G} (hxM : x ∈ D.M)
    (hXsup : conjClosure D.M L = L ⊔ CFSG.Quasithin.conjSubgroup L x) :
    Subgroup.centralizer (A₁ : Set G) ⊓ IOf D p L ≤ A ⊔ pCoreOf 2 (IOf D p L) ∨
      (1 < CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (A₁ : Set G)) ∧
        HasL2SzSection (S17.nOf L)
          (Subgroup.centralizer (A₁ : Set G) ⊓ IOf D p L)) ∨
      Subgroup.normalizer (A₁ : Set G) ≤ D.M := by
  classical
  set I : Subgroup G := IOf D p L with hI
  set n : ℕ := S17.nOf L with hn
  have hp : p.Prime := (D.sig_prime p h.hyp.hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p h.hyp.hp).2
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrp : r.Prime := h.hr.1
  haveI : Fact r.Prime := ⟨hrp⟩
  have hA₁I : A₁ ≤ I := hA₁A.trans h.hA
  have hAodd : Odd (Nat.card A) := odd_card_of_ctx19_10 h
  have hr2 : r ≠ 2 := by
    intro h2
    exact hAodd.not_two_dvd_nat (h2 ▸ h.hr.2)
  have hn3 : 3 ≤ n := three_le_nOf_of_setting1910 h.h1910
  obtain ⟨x0, hT0, hx0T, hx0ne, himgA₁0, hcentz0, hgeneric_of_cent0⟩ :=
    sp4_branch_setup D h hA₁A hA₁card
  have hT : IsZModSq (barImage I A) n := by simpa [I, n] using hT0
  have himgA₁ : (A₁.subgroupOf I).map (QuotientGroup.mk' (pCore 2 ↥I)) =
      Subgroup.zpowers x0 := by simpa [I] using himgA₁0
  have hcentz : Subgroup.centralizer (Subgroup.zpowers x0 : Set (Bar2 I)) =
      Subgroup.centralizer ({x0} : Set (Bar2 I)) := by simpa [I] using hcentz0
  have hgeneric_of_cent : Subgroup.centralizer ({x0} : Set (Bar2 I)) = barImage I A →
      Subgroup.centralizer (A₁ : Set G) ⊓ I ≤ A ⊔ pCoreOf 2 I := by
    intro hcent
    simpa [I] using hgeneric_of_cent0 (by simpa [I] using hcent)

  have hXsupC : conjClosure D.M L = L ⊔ CFSG.Quasithin.conjSubgroup L x := hXsup
  have hshapeL : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n :=
    hLshape.elim (fun hh => Or.inl hh.1) (fun hh => Or.inr hh.1)
  have hXsupI : IOf D p L = L ⊔ CFSG.Quasithin.conjSubgroup L x := hIeqC.trans hXsup
  have hdata := barImage_factor_data (D := D) (n := n) h hxM hXsupC hneC hXsupI hshapeL hn
  obtain ⟨hS₁n, hS₂n, hdisj, hsup, hpair⟩ := hdata
  obtain ⟨hKcalM, hKne⟩ := S17.conjSubgroup_mem_calC_and_ne h.hyp.hL.1 hxM hXsupC hneC
  let K : Subgroup G := CFSG.Quasithin.conjSubgroup L x
  have hLI : L ≤ I := by rw [hI, hXsupI]; exact le_sup_left
  have hKI : K ≤ I := by rw [hI, hXsupI]; exact le_sup_right
  have hLthin : F08.Thin8 L :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s13a_thin8_of_isL2_or_isSz hshapeL
  have hKshape : IsL2 (Bar2 K) n ∨ IsSz (Bar2 K) n := by
    obtain ⟨eK⟩ := uc22p20d_bar2_conj x⁻¹ L
    exact hshapeL.imp (fun hh => LieModel.of_mulEquiv eK hh)
      (fun hh => LieModel.of_mulEquiv eK hh)
  have hKthin : F08.Thin8 K :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s13a_thin8_of_isL2_or_isSz hKshape
  have hKall := hK (Bar2 I) n hn3 hodd (barImage I A) hT x0 hx0T hx0ne
  have hKprod := hKall.2 (barImage I L) (barImage I K) hS₁n hS₂n hdisj hsup hpair
  rcases hKprod with hxS₁ | hxS₂ | hcent
  ·
    have hle₁ : (A₁.subgroupOf I).map (QuotientGroup.mk' (pCore 2 ↥I)) ≤
        barImage I L := by
      rw [himgA₁]
      exact Subgroup.zpowers_le.mpr hxS₁
    exact Or.inr (Or.inr (normalizer_le_of_barImage_le (D := D) (K := L) h h3 hA₁A hA₁card
      hLI h.hyp.hL.1 hLthin hle₁))
  ·
    have hle₂ : (A₁.subgroupOf I).map (QuotientGroup.mk' (pCore 2 ↥I)) ≤
        barImage I K := by
      rw [himgA₁]
      exact Subgroup.zpowers_le.mpr hxS₂
    exact Or.inr (Or.inr (normalizer_le_of_barImage_le (D := D) (K := K) h h3 hA₁A hA₁card
      hKI hKcalM hKthin hle₂))
  ·
    exact Or.inl (hgeneric_of_cent hcent)

theorem trichotomy19_25_product_case
    (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ}
    (h : Ctx19_10 D V₀ V p L A t B r)
    (hodd : Odd (S17.nOf L)) (h3 : S17.R17_3At D V₀ V) (h42 : S17.R17_42At D V₀ V)
    (hK : K_19_25_torusCent) :
    ∀ (_hcase2 : IOf D p L = conjClosure D.M L ∧ conjClosure D.M L ≠ L ∧ 2 < S17.nOf L ∧
      ((IsL2 (Bar2 L) (S17.nOf L) ∧ (2 : ℤ) ^ S17.nOf L ≡ -1 [ZMOD (p : ℤ)]) ∨
        (IsSz (Bar2 L) (S17.nOf L) ∧
          (2 : ℤ) ^ (2 * S17.nOf L) ≡ -1 [ZMOD (p : ℤ)]))),
      ∀ A₁ : Subgroup G, A₁ ≤ A → Nat.card A₁ = r →
        Subgroup.centralizer (A₁ : Set G) ⊓ IOf D p L ≤ A ⊔ pCoreOf 2 (IOf D p L) ∨
          (1 < CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (A₁ : Set G)) ∧
            HasL2SzSection (S17.nOf L)
              (Subgroup.centralizer (A₁ : Set G) ⊓ IOf D p L)) ∨
          Subgroup.normalizer (A₁ : Set G) ≤ D.M := by
  intro hcase2 A₁ hA₁A hA₁card
  obtain ⟨-, x, hxM, hXsup, -, -, -⟩ :=
    S17.p42_alt2_of_ne (D := D) (V₀ := V₀) (V := V) h42 h.hyp.hp h.hyp.hL.1
      hcase2.2.1
  exact product_case_of_shape (D := D) (V₀ := V₀) (V := V) (p := p) (L := L) (A := A)
    (t := t) (B := B) (r := r) h hodd h3 hK hA₁A hA₁card
    hcase2.1 hcase2.2.1 hcase2.2.2.1 hcase2.2.2.2 hxM hXsup

theorem trichotomy19_25_of
    (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (hodd : Odd (S17.nOf L)) (h3 : S17.R17_3At D V₀ V) (h42 : S17.R17_42At D V₀ V)
    (h638 : UC6.R6_38 D) (hSg : UC6S846.SigmaStd D) (hK : K_19_25_torusCent) :
    Trichotomy19_25 D V₀ V p L A t B r h := by
  classical
  intro A₁ hA₁A hA₁card
  have hset := h.h1910
  simp only [Setting1910] at hset
  obtain ⟨-, h1 | hcase2 | hcase3⟩ := hset
  · obtain ⟨hsp, -, -, hcong⟩ := h1
    rcases sp4_trichotomy_branch D h hodd hsp hcong h638 hSg hK hA₁A hA₁card with
      hgen | hranksec
    · exact Or.inl hgen
    · exact Or.inr (Or.inl hranksec)
  · exact trichotomy19_25_product_case D h hodd h3 h42 hK hcase2 A₁ hA₁A hA₁card
  · exfalso
    set n : ℕ := S17.nOf L with hn
    obtain ⟨-, hn2, ⟨k, hk⟩, -⟩ := hcase3
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [hk] at hn2
      norm_num at hn2
    have heven : Even n := by
      rw [hk]
      exact (Nat.even_pow' hk0).mpr even_two
    have heven' : Even (S17.nOf L) := by simpa [hn] using heven
    exact (Nat.not_odd_iff_even.mpr heven') hodd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
