module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CComponents
public import CFSG.GroupTheory.ConjActionModPCore
import CFSG.GroupTheory.CoprimeCentralizerCover
import CFSG.GroupTheory.WielandtProductAux
import CFSG.GroupTheory.SteinbergCBFTHall
import CFSG.LocalAnalysis.RankFourTheoremC.PPointSetup
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.GroupTheory.PGroup.CardCoprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3

theorem mem_L_of_mem_ker_of_pow_three_eq_one (c : Ctx82E3 D) {y : G}
    (hy : y ∈ (CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L).ker.map
      D.M.subtype)
    (hy3 : y ^ 3 = 1) : y ∈ c.L := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set φ := CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L with hφ
  set C : Subgroup G := φ.ker.map D.M.subtype with hC
  by_contra hyL
  have hyM : y ∈ D.M := Subgroup.map_subtype_le φ.ker hy
  have hy_ne : y ≠ 1 := fun h => hyL (h ▸ c.L.one_mem)
  have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy_ne
  let R : Subgroup G := Subgroup.zpowers y
  have hR_le_C : R ≤ C := Subgroup.zpowers_le.mpr hy
  have hR_le_M : R ≤ D.M := hR_le_C.trans (Subgroup.map_subtype_le φ.ker)
  have hR : IsPGroup 3 R :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyord]; norm_num)
  have hR_le_NL : R ≤ Subgroup.normalizer (c.L : Set G) := hR_le_M.trans c.le_normalizer_L
  have hRN : R ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.L : Set G) :=
    hR_le_NL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 c.L)
  have hcomm : ⁅c.L, R⁆ ≤ CFSG.Open.pCoreOf 2 c.L :=
    (CFSG.GroupTheory.le_map_ker_conjModPCore_iff_commutator 2 c.L D.M R
      c.le_normalizer_L hR_le_M).mp (by simpa [hC, hφ] using hR_le_C)
  have hN2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 c.L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L
  have hN_not_dvd_3 : ¬ 3 ∣ Nat.card (CFSG.Open.pCoreOf 2 c.L) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hN2 Nat.prime_three (by norm_num)
  obtain ⟨S, hS_sylow, hS_cent⟩ :=
    CFSG.GroupTheory.exists_isSylowOf_le_centralizer_of_commutator_le
      (p := 3) (q := 3) (X := c.L) (N := CFSG.Open.pCoreOf 2 c.L) (R := R)
      (CFSG.LieType.BorelTits.pCoreOf_le 2 c.L) hR_le_NL hRN hR hN_not_dvd_3 hcomm
      hN_not_dvd_3
  have hS_rank : CFSG.Open.pRank 3 S = 3 := by
    rw [CFSG.LocalAnalysis.RankFourTheoremC.pRank_eq_of_isSylowOf (p := 3) (by norm_num)
      hS_sylow, c.pRank_three_L]
  obtain ⟨E, hES, hEab, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) S
  rw [hS_rank] at hEcard
  have hEL : E ≤ c.L := hES.trans hS_sylow.le
  have hEM : E ≤ D.M := hEL.trans c.hyp81.1
  have hEcent : E ≤ Subgroup.centralizer (R : Set G) := hES.trans hS_cent
  have hcardR : Nat.card R = 3 := by rw [Nat.card_zpowers, hyord]
  have hRdisj_L : R ⊓ c.L = ⊥ := by
    haveI : Fact (Nat.Prime (Nat.card R)) := ⟨by rw [hcardR]; norm_num⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (G := ↥R) (c.L.subgroupOf R) with h | h
    · exact disjoint_iff.mp (disjoint_comm.mp (Subgroup.subgroupOf_eq_bot.mp h))
    · exfalso
      rw [Subgroup.subgroupOf_eq_top] at h
      exact hyL (h (Subgroup.mem_zpowers y))
  have hdisj : Disjoint E R := by
    rw [Subgroup.disjoint_def]
    intro x hxE hxR
    have hx : x ∈ R ⊓ c.L := ⟨hxR, hEL hxE⟩
    rw [hRdisj_L] at hx
    exact Subgroup.mem_bot.mp hx
  have hcommER : ∀ a ∈ E, ∀ b ∈ R, a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hEcent ha) b hb).symm
  have hsup_ab : IsElemAbelian 3 (E ⊔ R) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hEab (CFSG.Open.isElemAbelian_zpowers hy3) hcommER
  have hsup_le_M : E ⊔ R ≤ D.M := sup_le hEM hR_le_M
  have hsup_card : Nat.card ↥(E ⊔ R) = 3 ^ 4 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E R hcommER).1
    rw [hdisj.eq_bot, Subgroup.card_bot, mul_one, hEcard, hcardR] at h
    rw [h]; norm_num
  have h4 : 4 ≤ CFSG.Open.pRank 3 D.M :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hsup_le_M hsup_ab hsup_card
  rw [c.pRank_three_M] at h4
  omega

theorem not_three_dvd_card_map_ker (c : Ctx82E3 D)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L))) :
    ¬ 3 ∣ Nat.card ((CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L).ker.map
      D.M.subtype) := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  intro h3C
  set φ := CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L with hφ
  set C : Subgroup G := φ.ker.map D.M.subtype with hC
  obtain ⟨yC, hyCord⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 3 h3C
  let y : G := (yC : C)
  have hyC : y ∈ C := yC.2
  have hyM : y ∈ D.M := Subgroup.map_subtype_le φ.ker hyC
  have hyord : orderOf y = 3 := by
    change orderOf (yC : G) = 3
    rw [Subgroup.orderOf_coe, hyCord]
  have hy3 : y ^ 3 = 1 := by rw [← hyord]; exact pow_orderOf_eq_one y
  have hyL : y ∈ c.L := mem_L_of_mem_ker_of_pow_three_eq_one c hyC hy3
  set z : (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L) :=
    QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) (⟨y, hyL⟩ : ↥c.L) with hz
  have hφy : φ ⟨y, hyM⟩ = 1 := by
    obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp hyC
    rw [show (⟨y, hyM⟩ : ↥D.M) = a from Subtype.ext hay.symm]
    exact MonoidHom.mem_ker.mp ha
  have hconj : MulAut.conj z = φ ⟨y, hyM⟩ := by
    rw [hz]
    exact (CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 c.L D.M c.le_normalizer_L
      hyM hyL).symm
  have hz_center : z ∈ Subgroup.center (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L) := by
    rw [Subgroup.mem_center_iff]
    intro w
    have h1 : z * w * z⁻¹ = w := by
      have := congrArg (fun f : MulAut _ => f w) (hconj.trans hφy)
      simpa [MulAut.conj_apply] using this
    calc w * z = (z * w * z⁻¹) * z := by rw [h1]
      _ = z * w := by group
  have hz_ne : z ≠ 1 := by
    intro hz1
    have hy_core : (⟨y, hyL⟩ : ↥c.L) ∈ CFSG.Open.pCore 2 ↥c.L := by
      rw [← QuotientGroup.eq_one_iff]; exact hz1
    have h3core : 3 ∣ Nat.card (CFSG.Open.pCore 2 ↥c.L) :=
      (by rw [Nat.card_zpowers, Subgroup.orderOf_mk y hyL, hyord] :
        Nat.card (Subgroup.zpowers (⟨y, hyL⟩ : ↥c.L)) = 3) ▸
        Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hy_core)
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L))
      Nat.prime_three (by norm_num) h3core
  have hz3 : z ^ 3 = 1 := by
    rw [hz, ← QuotientGroup.mk_pow,
      show (⟨y, hyL⟩ : ↥c.L) ^ 3 = 1 by ext; simpa using hy3]
    exact QuotientGroup.mk_one _
  have h3center : 3 ∣ Nat.card (Subgroup.center (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L)) :=
    (by rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz_ne] :
      Nat.card (Subgroup.zpowers z) = 3) ▸
      Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hz_center)
  exact hZ h3center

theorem le_L_of_map_le_innAut (c : Ctx82E3 D)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L)))
    {Q : Subgroup G} (hQM : Q ≤ D.M) (hQ : IsPGroup 3 Q)
    (hinn : (Q.subgroupOf D.M).map
        (CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L) ≤
      (MulAut.conj : (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L) →*
        MulAut (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L)).range) :
    Q ≤ c.L := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let Lbar := ↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L
  let φ := CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L
  let C : Subgroup G := φ.ker.map D.M.subtype
  let Inn : Subgroup (MulAut Lbar) := (MulAut.conj : Lbar →* MulAut Lbar).range
  have h3C : ¬ 3 ∣ Nat.card C := not_three_dvd_card_map_ker c hZ
  have hQ_le_sup : Q ≤ c.L ⊔ C := by
    intro x hxQ
    have hxM : x ∈ D.M := hQM hxQ
    have hxR : φ ⟨x, hxM⟩ ∈ (Q.subgroupOf D.M).map φ :=
      Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr hxQ, rfl⟩
    obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp (hinn hxR)
    obtain ⟨ℓ, hℓ⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥c.L) q
    have hφℓ : φ ⟨(ℓ : G), c.hyp81.1 ℓ.2⟩ =
        MulAut.conj (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ℓ) :=
      CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 c.L D.M c.le_normalizer_L
        (c.hyp81.1 ℓ.2) ℓ.2
    have hφx_eq : φ ⟨x, hxM⟩ = φ ⟨(ℓ : G), c.hyp81.1 ℓ.2⟩ := by
      rw [hφℓ]
      rw [← hℓ] at hq
      exact hq.symm
    have hmem_ker : (⟨x, hxM⟩ * (⟨(ℓ : G), c.hyp81.1 ℓ.2⟩ : ↥D.M)⁻¹) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφx_eq, mul_inv_cancel]
    have hxC : x * (ℓ : G)⁻¹ ∈ C := Subgroup.mem_map.mpr ⟨_, hmem_ker, rfl⟩
    rw [show x = (x * (ℓ : G)⁻¹) * (ℓ : G) by group]
    exact (c.L ⊔ C).mul_mem (Subgroup.mem_sup_right hxC) (Subgroup.mem_sup_left ℓ.2)
  have hCsub_normal : (C.subgroupOf D.M).Normal := by
    have hCsub : C.subgroupOf D.M = φ.ker := by
      change Subgroup.comap D.M.subtype (Subgroup.map D.M.subtype φ.ker) = φ.ker
      rw [Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq]
    rw [hCsub]
    infer_instance
  have hM_le_NC : D.M ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le φ.ker)).mp
      hCsub_normal
  have hL_le_NC : c.L ≤ Subgroup.normalizer (C : Set G) := c.hyp81.1.trans hM_le_NC
  let H : Subgroup G := c.L ⊔ C
  have hL_le_H : c.L ≤ H := le_sup_left
  have hH_le_NL : H ≤ Subgroup.normalizer (c.L : Set G) :=
    sup_le Subgroup.le_normalizer ((Subgroup.map_subtype_le φ.ker).trans c.le_normalizer_L)
  have hHL_idx : c.L.relIndex H ∣ Nat.card C := by
    have h := CFSG.GroupTheory.FT63ChII.relIndex_eq_relIndex_sup_of_le_normalizer
      (H := c.L) (K := C) hL_le_NC
    change c.L.relIndex (c.L ⊔ C) ∣ Nat.card C
    rw [← h]
    exact Subgroup.relIndex_dvd_card c.L C
  have h3HL : ¬ 3 ∣ c.L.relIndex H := fun hdvd => h3C (hdvd.trans hHL_idx)
  let Kh : Subgroup ↥H := c.L.subgroupOf H
  haveI : Kh.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hL_le_H).mpr hH_le_NL
  have hQhp : IsPGroup 3 (Q.subgroupOf H) := by
    have h : Q.subgroupOf H = Subgroup.comap H.subtype Q := by rw [Subgroup.comap_subtype]
    rw [h]
    exact hQ.comap_subtype
  have hindexKh : Kh.index = c.L.relIndex H := by
    change (Subgroup.comap H.subtype c.L).index = c.L.relIndex H
    rw [Subgroup.index_comap, Subgroup.range_subtype]
  have hcop : Nat.Coprime (Nat.card (Q.subgroupOf H)) Kh.index := by
    obtain ⟨n, hn⟩ := hQhp.exists_card_eq
    rw [hn, hindexKh]
    exact Nat.Coprime.pow_left n
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).2 h3HL)
  have hQh_le_Kh : Q.subgroupOf H ≤ Kh :=
    CFSG.GroupTheory.WielandtProduct.le_of_coprime_index (K := Kh) (H := Q.subgroupOf H) hcop
  intro x hxQ
  have hxH : x ∈ H := hQ_le_sup hxQ
  have hxQh : (⟨x, hxH⟩ : ↥H) ∈ Q.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    simpa using hxQ
  exact Subgroup.mem_subgroupOf.mp (hQh_le_Kh hxQh)

theorem le_L_of_isSylowOf (c : Ctx82E3 D)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L)))
    (hK2 : ∀ R : Subgroup (MulAut (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L)), IsPGroup 3 R →
      CFSG.ABGLocalTools.IsSylowOf 3 (R ⊓ (MulAut.conj : (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L) →*
        MulAut (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L)).range)
        (MulAut.conj : (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L) →*
          MulAut (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L)).range →
      ¬ R ≤ (MulAut.conj : (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L) →*
        MulAut (↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L)).range →
      4 ≤ CFSG.Open.pRank 3 R)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) : P ≤ c.L := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let Lbar := ↥c.L ⧸ CFSG.Open.pCore 2 ↥c.L
  let φ := CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L
  let C : Subgroup G := φ.ker.map D.M.subtype
  let Inn : Subgroup (MulAut Lbar) := (MulAut.conj : Lbar →* MulAut Lbar).range
  have h3C : ¬ 3 ∣ Nat.card C := not_three_dvd_card_map_ker c hZ
  have h3ker : ¬ 3 ∣ Nat.card φ.ker := by
    rw [← Subgroup.card_map_of_injective D.M.subtype_injective (K := φ.ker)]
    exact h3C
  let P' : Subgroup ↥D.M := P.subgroupOf D.M
  let R : Subgroup (MulAut Lbar) := P'.map φ
  have hP'p : IsPGroup 3 P' := by
    have h : P' = Subgroup.comap D.M.subtype P := by rw [Subgroup.comap_subtype]
    rw [h]
    exact hP.isPGroup.comap_subtype
  have hRp : IsPGroup 3 R := hP'p.map φ
  have hrankP' : CFSG.Open.pRank 3 P' = CFSG.Open.pRank 3 P := by
    have h1 : CFSG.pRank 3 ↥P' = CFSG.pRank 3 ↥P :=
      CFSG.pRank_congr_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hP.le) 3
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 3 P',
      ← CFSG.SectionRank.pRank_coe_eq_openPRank 3 P]
    exact h1
  let f : ↥P' →* MulAut Lbar := φ.comp P'.subtype
  have hdisj : Disjoint P' φ.ker := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    obtain ⟨n, hn⟩ := hP'p.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_left n
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).2 h3ker)
  have hf_inj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
    have hxinter : (x : ↥D.M) ∈ P' ⊓ φ.ker := ⟨x.2, by simpa [f] using hx⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at hxinter
    exact Subtype.ext hxinter
  have hrange : f.range = R := by
    rw [show f = φ.comp P'.subtype from rfl, MonoidHom.range_comp, Subgroup.range_subtype]
  have hrankR : CFSG.Open.pRank 3 R = CFSG.Open.pRank 3 P' := by
    have e : ↥P' ≃* ↥R :=
      (MonoidHom.ofInjective hf_inj).trans (MulEquiv.subgroupCongr hrange)
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 3 P',
      ← CFSG.SectionRank.pRank_coe_eq_openPRank 3 R]
    exact (CFSG.pRank_congr_of_mulEquiv e 3).symm
  have hRrank_le : CFSG.Open.pRank 3 R ≤ 3 := by
    have hPM : CFSG.Open.pRank 3 P ≤ CFSG.Open.pRank 3 D.M :=
      CFSG.SectionRank.pRank_mono (by norm_num : (1 : ℕ) < 3) hP.le
    rw [c.pRank_three_M] at hPM
    omega
  let S : Subgroup G := P ⊓ c.L
  have hS_sylow : CFSG.ABGLocalTools.IsSylowOf 3 S c.L :=
    hP.inf_of_le_normalizer c.hyp81.1 c.le_normalizer_L
  obtain ⟨Q, hQ⟩ := hS_sylow
  let ψ : ↥c.L →* MulAut Lbar :=
    (MulAut.conj : Lbar →* MulAut Lbar).comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))
  let ψInn : ↥c.L →* Inn := ψ.codRestrict Inn (fun x => MonoidHom.mem_range.mpr
    ⟨QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) x, rfl⟩)
  have hψInn_surj : Function.Surjective ψInn := by
    rintro ⟨_, q, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥c.L) q
    exact ⟨x, Subtype.ext rfl⟩
  let T : Subgroup (MulAut Lbar) := (Q : Subgroup ↥c.L).map ψ
  have hT_sylow : CFSG.ABGLocalTools.IsSylowOf 3 T Inn := by
    refine ⟨Q.mapSurjective hψInn_surj, ?_⟩
    rw [Sylow.coe_mapSurjective, Subgroup.map_map]
    congr 1
  have hT_le_Inn : T ≤ Inn := hT_sylow.le
  have hT_le_R : T ≤ R := by
    rintro t ⟨q, hqQ, rfl⟩
    have hqS : (q : G) ∈ S := by
      rw [← hQ]
      exact Subgroup.mem_map_of_mem c.L.subtype hqQ
    exact Subgroup.mem_map.mpr ⟨⟨(q : G), c.hyp81.1 q.2⟩,
      Subgroup.mem_subgroupOf.mpr hqS.1,
      CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 c.L D.M c.le_normalizer_L
        (c.hyp81.1 q.2) q.2⟩
  have hRinf_sylow : CFSG.ABGLocalTools.IsSylowOf 3 (R ⊓ Inn) Inn := by
    have heq : R ⊓ Inn = T :=
      hT_sylow.eq_of_le (le_inf hT_le_R hT_le_Inn) inf_le_right hRp.to_inf_left
    rw [heq]
    exact hT_sylow
  have hR_le_Inn : R ≤ Inn := by
    by_contra hnot
    have h4 : 4 ≤ CFSG.Open.pRank 3 R := hK2 R hRp (by simpa [Inn] using hRinf_sylow) hnot
    omega
  exact le_L_of_map_le_innAut c hZ hP.le hP.isPGroup (by simpa [Inn] using hR_le_Inn)

end Ctx82E3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
