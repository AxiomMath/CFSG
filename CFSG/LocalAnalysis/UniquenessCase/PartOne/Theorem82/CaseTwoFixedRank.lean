module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CComponents
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
import CFSG.LocalAnalysis.RankFourTheoremC.PPointSmallTypes
import CFSG.ClassicalInvolution.LBalance.Glauberman.SylowTools
import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4End
import CFSG.RankThree.OddKernel.CentralCoverComponentModels
import CFSG.RankThree.OddKernel.EvenMinimalCover
import CFSG.RankThree.PartOne.S11d.OutCentral
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace SylowThreeData

variable (d : SylowThreeData G)

theorem le_normalizer_Lf_of_isPGroup {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hinj : Function.Injective d.Lf)
    (hperm : ∀ m ∈ d.M, ∀ i, ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    {g : G} (hg : g ∈ d.M) (hgp : IsPGroup p (Subgroup.zpowers g)) (i : Fin 3) :
    g ∈ Subgroup.normalizer (d.Lf i : Set G) := by
  classical
  have hpp : p.Prime := Fact.out
  obtain ⟨k, hk⟩ := hgp.exists_card_eq
  have hord : orderOf g = p ^ k := by
    rw [← Nat.card_zpowers, hk]
  let σ₀ : Fin 3 → Fin 3 := fun i => Classical.choose (hperm g hg i)
  have hσ₀ : ∀ i, (d.Lf i).map (MulAut.conj g).toMonoidHom = d.Lf (σ₀ i) :=
    fun i => Classical.choose_spec (hperm g hg i)
  have hinjσ₀ : Function.Injective σ₀ := by
    intro a b hab
    apply hinj
    have h1 : (d.Lf a).map (MulAut.conj g).toMonoidHom =
        (d.Lf b).map (MulAut.conj g).toMonoidHom := by
      rw [hσ₀ a, hσ₀ b, hab]
    exact Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective h1
  let σ : Equiv.Perm (Fin 3) :=
    Equiv.ofBijective σ₀ ⟨hinjσ₀, Finite.injective_iff_surjective.mp hinjσ₀⟩
  have hσ : ∀ a, (d.Lf a).map (MulAut.conj g).toMonoidHom = d.Lf (σ a) := hσ₀
  have hpow : ∀ n : ℕ, ∀ a, (d.Lf a).map (MulAut.conj (g ^ n)).toMonoidHom =
      d.Lf ((σ ^ n) a) := by
    intro n
    induction n with
    | zero =>
        intro a
        rw [pow_zero, map_one, pow_zero]
        show (d.Lf a).map (↑(1 : MulAut G)) = d.Lf ((1 : Equiv.Perm (Fin 3)) a)
        exact Subgroup.map_id (d.Lf a)
    | succ n ih =>
        intro a
        have hstep : (d.Lf a).map (MulAut.conj (g ^ (n + 1))).toMonoidHom =
            ((d.Lf a).map (MulAut.conj (g ^ n)).toMonoidHom).map
              (MulAut.conj g).toMonoidHom := by
          rw [pow_succ', map_mul, Subgroup.map_map]
          congr 1
        rw [hstep, ih a, hσ]
        congr 1
        rw [pow_succ']
        rfl
  have hσpow : σ ^ (p ^ k) = 1 := by
    apply Equiv.ext
    intro a
    have h1 : d.Lf ((σ ^ (p ^ k)) a) = d.Lf a := by
      rw [← hpow (p ^ k) a, ← hord, pow_orderOf_eq_one, map_one]
      exact Subgroup.map_id (d.Lf a)
    exact hinj h1
  have hdvd1 : orderOf σ ∣ p ^ k := orderOf_dvd_of_pow_eq_one hσpow
  have hdvd2 : orderOf σ ∣ 6 := by
    have h := orderOf_dvd_natCard σ
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    norm_num at h
    exact h
  have hcop6 : Nat.Coprime p 6 := by
    rw [hpp.coprime_iff_not_dvd]
    intro hdvd
    have hle : p ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases p
    · norm_num at hdvd
    · exact absurd hpp (by norm_num)
  have hcop : Nat.Coprime (p ^ k) 6 := hcop6.pow_left k
  have hone : orderOf σ = 1 := by
    have h := Nat.dvd_gcd hdvd1 hdvd2
    rw [hcop.gcd_eq_one] at h
    exact Nat.dvd_one.mp h
  have hσ1 : σ = 1 := orderOf_eq_one_iff.mp hone
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (d.Lf i).map (MulAut.conj g).toMonoidHom = d.Lf i
  rw [hσ i, hσ1]
  rfl

theorem pRank_L_le_add {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (h : ∀ i, CFSG.Open.pRank p (d.Lf i) ≤ 1) :
    CFSG.Open.pRank p d.L ≤ CFSG.Open.pRank p (d.Lf 0) + CFSG.Open.pRank p (d.Lf 1) +
      CFSG.Open.pRank p (d.Lf 2) := by
  classical
  have hpp : p.Prime := Fact.out
  let Y : Subgroup G := d.Lf 0 ⊔ d.Lf 1
  have hY0 : Y ≤ Subgroup.normalizer (d.Lf 0 : Set G) :=
    sup_le Subgroup.le_normalizer (d.hLnorm 0 1)
  haveI : ((d.Lf 0).subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : d.Lf 0 ≤ Y)).mpr hY0
  have hYL : d.L ≤ Subgroup.normalizer (Y : Set G) := by
    have h2 : d.Lf 2 ≤ Subgroup.normalizer (Y : Set G) :=
      (le_inf (d.hLnorm 0 2) (d.hLnorm 1 2)).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    rw [d.hL, show d.Lf 0 ⊔ d.Lf 1 ⊔ d.Lf 2 = Y ⊔ d.Lf 2 from rfl]
    exact sup_le Subgroup.le_normalizer h2
  have hYLmem : Y ≤ d.L := by
    rw [d.hL]
    show Y ≤ Y ⊔ d.Lf 2
    exact le_sup_left
  haveI : (Y.subgroupOf d.L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYLmem).mpr hYL
  have hYle : CFSG.pRank p ↥Y ≤ CFSG.pRank p ↥(d.Lf 0) + CFSG.pRank p ↥(d.Lf 1) := by
    have hsub := CFSG.RankThree.OddKernel.pRank_le_add_of_normal (p := p) hpp
      ((d.Lf 0).subgroupOf Y)
    have hA : CFSG.pRank p ↥((d.Lf 0).subgroupOf Y) = CFSG.pRank p ↥(d.Lf 0) := by
      rw [CFSG.pRank_congr_of_mulEquiv (Subgroup.subgroupOfEquivOfLe le_sup_left) p]
    have h1rank : CFSG.pRank p ↥(d.Lf 1) ≤ 1 := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
      exact h 1
    have hB : CFSG.pRank p (↥Y ⧸ (d.Lf 0).subgroupOf Y) ≤ CFSG.pRank p ↥(d.Lf 1) := by
      let ψ : ↥(d.Lf 1) →* (↥Y ⧸ (d.Lf 0).subgroupOf Y) :=
        (QuotientGroup.mk' ((d.Lf 0).subgroupOf Y)).comp (Subgroup.inclusion le_sup_right)
      have hψ : Function.Surjective ψ := by
        intro z
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((d.Lf 0).subgroupOf Y) z
        have hxmem : (x : G) ∈ (d.Lf 0 : Set G) * (d.Lf 1 : Set G) := by
          rw [← Subgroup.coe_mul_of_right_le_normalizer_left (d.Lf 0) (d.Lf 1) (d.hLnorm 0 1)]
          exact x.2
        obtain ⟨a, ha, b, hb, hxab⟩ := hxmem
        refine ⟨⟨b, hb⟩, ?_⟩
        change QuotientGroup.mk' ((d.Lf 0).subgroupOf Y)
            (Subgroup.inclusion le_sup_right (⟨b, hb⟩ : d.Lf 1)) =
          QuotientGroup.mk' ((d.Lf 0).subgroupOf Y) x
        have hx : x = Subgroup.inclusion le_sup_left (⟨a, ha⟩ : d.Lf 0) *
            Subgroup.inclusion le_sup_right (⟨b, hb⟩ : d.Lf 1) := by
          apply Subtype.ext
          simpa using hxab.symm
        rw [hx, map_mul]
        have hker : QuotientGroup.mk' ((d.Lf 0).subgroupOf Y)
            (Subgroup.inclusion le_sup_left (⟨a, ha⟩ : d.Lf 0)) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ha)
        rw [hker, one_mul]
      exact CFSG.RankThree.OddKernel.pRank_le_of_surjective_of_le_one hpp hp ψ hψ h1rank
    rw [hA] at hsub
    exact hsub.trans (add_le_add_right hB (CFSG.pRank p ↥(d.Lf 0)))
  have hQle : CFSG.pRank p (↥d.L ⧸ Y.subgroupOf d.L) ≤ CFSG.pRank p ↥(d.Lf 2) := by
    have h2rank : CFSG.pRank p ↥(d.Lf 2) ≤ 1 := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
      exact h 2
    let ψ : ↥(d.Lf 2) →* (↥d.L ⧸ Y.subgroupOf d.L) :=
      (QuotientGroup.mk' (Y.subgroupOf d.L)).comp (Subgroup.inclusion (d.Lf_le_L 2))
    have hψ : Function.Surjective ψ := by
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Y.subgroupOf d.L) z
      have hY2norm : d.Lf 2 ≤ Subgroup.normalizer (Y : Set G) :=
        (le_inf (d.hLnorm 0 2) (d.hLnorm 1 2)).trans
          (Subgroup.inf_normalizer_le_normalizer_sup _ _)
      have hxY : (x : G) ∈ Y ⊔ d.Lf 2 := by
        have hYL' : Y ⊔ d.Lf 2 = d.L := d.hL.symm
        rw [hYL']
        exact x.2
      have hxmem : (x : G) ∈ (Y : Set G) * (d.Lf 2 : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y (d.Lf 2) hY2norm]
        exact hxY
      obtain ⟨c, hcY, d2, hd2, hxcd⟩ := hxmem
      refine ⟨⟨d2, hd2⟩, ?_⟩
      change QuotientGroup.mk' (Y.subgroupOf d.L)
          (Subgroup.inclusion (d.Lf_le_L 2) (⟨d2, hd2⟩ : d.Lf 2)) =
        QuotientGroup.mk' (Y.subgroupOf d.L) x
      have hYLmem : Y ≤ d.L := by
        rw [d.hL]
        show Y ≤ Y ⊔ d.Lf 2
        exact le_sup_left
      have hx' : x = Subgroup.inclusion hYLmem (⟨c, hcY⟩ : Y) *
          Subgroup.inclusion (d.Lf_le_L 2) (⟨d2, hd2⟩ : d.Lf 2) := by
        apply Subtype.ext
        simpa using hxcd.symm
      rw [hx', map_mul]
      have hker : QuotientGroup.mk' (Y.subgroupOf d.L)
          (Subgroup.inclusion hYLmem (⟨c, hcY⟩ : Y)) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hcY)
      rw [hker, one_mul]
    exact CFSG.RankThree.OddKernel.pRank_le_of_surjective_of_le_one hpp hp ψ hψ h2rank
  have hsub := CFSG.RankThree.OddKernel.pRank_le_add_of_normal (p := p) hpp (Y.subgroupOf d.L)
  have hYiso : CFSG.pRank p ↥(Y.subgroupOf d.L) = CFSG.pRank p ↥Y :=
    CFSG.pRank_congr_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYLmem) p
  rw [hYiso] at hsub
  rw [← CFSG.SectionRank.pRank_coe_eq_openPRank p d.L]
  calc CFSG.pRank p ↥d.L
      ≤ CFSG.pRank p ↥Y + CFSG.pRank p (↥d.L ⧸ Y.subgroupOf d.L) := hsub
    _ ≤ (CFSG.pRank p ↥(d.Lf 0) + CFSG.pRank p ↥(d.Lf 1)) +
        CFSG.pRank p ↥(d.Lf 2) := add_le_add hYle hQle
    _ = CFSG.Open.pRank p (d.Lf 0) + CFSG.Open.pRank p (d.Lf 1) +
        CFSG.Open.pRank p (d.Lf 2) := by
        rw [CFSG.SectionRank.pRank_coe_eq_openPRank p (d.Lf 0),
          CFSG.SectionRank.pRank_coe_eq_openPRank p (d.Lf 1),
          CFSG.SectionRank.pRank_coe_eq_openPRank p (d.Lf 2)]

theorem pRank_L_le_three {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (h : ∀ i, CFSG.Open.pRank p (d.Lf i) ≤ 1) : CFSG.Open.pRank p d.L ≤ 3 := by
  have hsum := d.pRank_L_le_add hp h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  omega

end SylowThreeData

namespace Ctx812

theorem exists_isPGroup_le_centralizer_AA (c : Ctx812 G) {p : ℕ}
    (hp : p ∈ c.sig) (d : SylowThreeData G) (hdM : d.M = c.S.M)
    (hdL : d.L = c.L) (hinj : Function.Injective d.Lf)
    (hperm : ∀ m ∈ c.S.M, ∀ i, ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    (h1 : ∀ i, CFSG.Open.pRank p (d.Lf i) ≤ 1) :
    ∃ T : Subgroup G, IsPGroup p T ∧ T ≠ ⊥ ∧
      T ≤ c.S.M ⊓ Subgroup.centralizer (d.AA : Set G) ∧
      (CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (d.AA : Set G)) ≤ 1 →
        c.k ≤ CFSG.Open.pRank p (d.Lf 0) + CFSG.Open.pRank p (d.Lf 1) +
          CFSG.Open.pRank p (d.Lf 2) + 1) := by
  classical
  have hpp : p.Prime := (c.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hpp⟩
  have hp5 : 5 ≤ p := c.five_le_of_mem_sigma hp
  have hp2 : p ≠ 2 := by omega
  haveI : ((c.L).subgroupOf c.S.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer c.hyp81.1).mpr c.le_normalizer_L
  let N : Subgroup G := c.S.M ⊓ Subgroup.normalizer (d.S : Set G)
  have hNM : N ≤ c.S.M := inf_le_left
  obtain ⟨T, hT⟩ := CFSG.ABGLocalTools.exists_isSylowOf p N
  have hTp : IsPGroup p T := hT.isPGroup
  have hTN : T ≤ N := hT.le
  have hTM : T ≤ c.S.M := hTN.trans inf_le_left
  have hTNnorm : T ≤ Subgroup.normalizer (d.S : Set G) := hTN.trans inf_le_right
  let φ : ↥N →* (↥c.S.M ⧸ (c.L).subgroupOf c.S.M) :=
    (QuotientGroup.mk' ((c.L).subgroupOf c.S.M)).comp (Subgroup.inclusion hNM)
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective ((c.L).subgroupOf c.S.M) q
    let S₂ : Subgroup G := d.S.map (MulAut.conj (m : G)).toMonoidHom
    have hS₂le : S₂ ≤ c.L := by
      rintro _ ⟨s, hs, rfl⟩
      have hsL : s ∈ c.L := by
        have hs' := d.hS.le hs
        rwa [hdL] at hs'
      have hconj := (Subgroup.mem_normalizer_iff.mp (c.le_normalizer_L m.2) s).mp hsL
      simpa [S₂, MulAut.conj_apply] using hconj
    have hS₂card : Nat.card S₂ = 3 ^ (Nat.card c.L).factorization 3 := by
      have hcard : Nat.card S₂ = Nat.card d.S :=
        Subgroup.card_map_of_injective (MulAut.conj (m : G)).injective
      rw [hcard, ← hdL]
      exact d.hS.card_eq
    have hS₂syl : CFSG.ABGLocalTools.IsSylowOf 3 S₂ c.L :=
      CFSG.ABGLocalTools.isSylowOf_of_card hS₂le hS₂card
    have hSsyl : CFSG.ABGLocalTools.IsSylowOf 3 d.S c.L := by
      simpa [hdL] using d.hS
    obtain ⟨x, hxL, hxconj⟩ :=
      CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_exists_conj hSsyl hS₂syl
    have hxinvL : x⁻¹ ∈ c.L := c.L.inv_mem hxL
    have hnM : x⁻¹ * (m : G) ∈ c.S.M :=
      c.S.M.mul_mem (c.hyp81.1 hxinvL) m.2
    have hnN : x⁻¹ * (m : G) ∈ N := by
      refine Subgroup.mem_inf.mpr ⟨hnM, ?_⟩
      refine CFSG.RankThree.PartOne.mem_normalizer_of_conj_subset fun s hs => ?_
      have hms : (m : G) * s * (m : G)⁻¹ ∈ S₂ := ⟨s, hs, rfl⟩
      have h := (hxconj ((m : G) * s * (m : G)⁻¹)).mp hms
      have hEq : (x⁻¹ * (m : G)) * s * (x⁻¹ * (m : G))⁻¹ =
          x⁻¹ * ((m : G) * s * (m : G)⁻¹) * x := by group
      rw [hEq]
      exact h
    refine ⟨⟨x⁻¹ * (m : G), hnN⟩, ?_⟩
    show QuotientGroup.mk' ((c.L).subgroupOf c.S.M) ⟨x⁻¹ * (m : G), hnM⟩ =
      QuotientGroup.mk' ((c.L).subgroupOf c.S.M) m
    have hn_eq : (⟨x⁻¹ * (m : G), hnM⟩ : ↥c.S.M) =
        Subgroup.inclusion c.hyp81.1 (⟨x⁻¹, hxinvL⟩ : c.L) * m := by
      apply Subtype.ext
      rfl
    rw [hn_eq, map_mul]
    have hker : QuotientGroup.mk' ((c.L).subgroupOf c.S.M)
        (Subgroup.inclusion c.hyp81.1 (⟨x⁻¹, hxinvL⟩ : c.L)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hxinvL)
    rw [hker, one_mul]
  have hTC : T ≤ c.S.M ⊓ Subgroup.centralizer (d.AA : Set G) := by
    refine le_inf hTM ?_
    intro t htT
    have hgp : IsPGroup p (Subgroup.zpowers t) :=
      hTp.to_le (Subgroup.zpowers_le.mpr htT)
    have hperm' : ∀ m ∈ d.M, ∀ i, ∃ j,
        (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j :=
      fun m hm i => hperm m (hdM ▸ hm) i
    have htL : ∀ i, t ∈ Subgroup.normalizer (d.Lf i : Set G) :=
      fun i => d.le_normalizer_Lf_of_isPGroup hp5 hinj hperm'
        (hdM.symm ▸ hTM htT) hgp i
    have hcent := d.centralizes_AA_of_isPGroup hpp hp2 hgp (hTNnorm htT) htL
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hcent a ha).symm
  have hTne : T ≠ ⊥ := by
    intro hTbot
    have hNcard : ¬ p ∣ Nat.card ↥N := by
      have hfac : (Nat.card ↥N).factorization p = 0 := by
        have h := hT.card_eq
        rw [hTbot, Subgroup.card_bot] at h
        have h1 : p ^ (Nat.card ↥N).factorization p = 1 := h.symm
        rcases Nat.pow_eq_one.mp h1 with h2 | h2
        · exact absurd h2 hpp.ne_one
        · exact h2
      rcases (Nat.factorization_eq_zero_iff (Nat.card ↥N) p).mp hfac with h | h | h
      · exact absurd hpp h
      · exact h
      · exact absurd h (Nat.card_pos.ne')
    have hcarddvd : Nat.card (↥c.S.M ⧸ (c.L).subgroupOf c.S.M) ∣ Nat.card ↥N :=
      Subgroup.card_dvd_of_surjective hφ
    have hMLcard : ¬ p ∣ Nat.card (↥c.S.M ⧸ (c.L).subgroupOf c.S.M) :=
      fun hdvd => hNcard (hdvd.trans hcarddvd)
    have hindex : ¬ p ∣ ((c.L).subgroupOf c.S.M).index := by
      rwa [Subgroup.index_eq_card]
    have hLle : CFSG.Open.pRank p c.L ≤ 3 := by
      have h := d.pRank_L_le_three hp2 h1
      simpa [hdL] using h
    exact hindex (c.dvd_index p hp hLle)
  refine ⟨T, hTp, hTne, hTC, ?_⟩
  intro hrankC
  have hTcyc : IsCyclic ↥T := by
    have hrankT : CFSG.Open.pRank p T ≤ 1 :=
      (CFSG.SectionRank.pRank_mono hpp.one_lt hTC).trans hrankC
    refine CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one hpp hp2 le_rfl hTp ?_
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank]
  obtain ⟨Q₀, hQ₀⟩ := hT
  have hQ₀cyc : IsCyclic ↥(Q₀ : Subgroup ↥N) := by
    haveI : IsCyclic ↥((Q₀ : Subgroup ↥N).map N.subtype) := hQ₀ ▸ hTcyc
    exact isCyclic_of_surjective
      ((Q₀ : Subgroup ↥N).equivMapOfInjective N.subtype N.subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  have hNcyc : ∀ Q : Sylow p ↥N, IsCyclic (Q : Subgroup ↥N) := by
    intro Q
    haveI : IsCyclic ↥(Q₀ : Subgroup ↥N) := hQ₀cyc
    exact isCyclic_of_surjective (Sylow.equiv Q₀ Q).toMonoidHom (MulEquiv.surjective _)
  have hNrankOpen : CFSG.Open.pRank p (⊤ : Subgroup ↥N) ≤ 1 :=
    CFSG.LocalAnalysis.RankFourTheoremC.pRank_top_le_one_of_forall_sylow_isCyclic hNcyc
  have hNrank : CFSG.pRank p ↥N ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hNrankOpen
  have hQrank : CFSG.pRank p (↥c.S.M ⧸ (c.L).subgroupOf c.S.M) ≤ 1 :=
    CFSG.Quasithin.H13.Ch4.L436.pRank_le_one_of_surjective' hpp hp2 φ hφ hNrank
  have hQrank' : CFSG.Open.pRank p (⊤ : Subgroup (↥c.S.M ⧸ (c.L).subgroupOf c.S.M)) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hQrank
  have hsub := CFSG.RankThree.OddKernel.pRank_le_add_of_normal (p := p) hpp
    ((c.L).subgroupOf c.S.M)
  have hMle : CFSG.Open.pRank p c.S.M ≤ CFSG.Open.pRank p c.L + 1 := by
    have hM' : CFSG.pRank p ↥c.S.M = CFSG.Open.pRank p c.S.M :=
      CFSG.SectionRank.pRank_coe_eq_openPRank p c.S.M
    have hL' : CFSG.pRank p ↥((c.L).subgroupOf c.S.M) = CFSG.Open.pRank p c.L := by
      rw [CFSG.pRank_congr_of_mulEquiv (Subgroup.subgroupOfEquivOfLe c.hyp81.1) p,
        CFSG.SectionRank.pRank_coe_eq_openPRank p c.L]
    have hQrank'' : CFSG.pRank p (↥c.S.M ⧸ (c.L).subgroupOf c.S.M) ≤ 1 := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact hQrank'
    rw [← hM', ← hL']
    exact hsub.trans (add_le_add_right hQrank'' (CFSG.pRank p ↥((c.L).subgroupOf c.S.M)))
  have hLsum : CFSG.Open.pRank p c.L ≤ CFSG.Open.pRank p (d.Lf 0) +
      CFSG.Open.pRank p (d.Lf 1) + CFSG.Open.pRank p (d.Lf 2) := by
    have h := d.pRank_L_le_add hp2 h1
    simpa [hdL] using h
  have hk := c.rank_ge p hp
  omega

end Ctx812

namespace Counterexample4

theorem exists_isPGroup_le_centralizer_AA (c : Counterexample4 G) {p : ℕ}
    (hp : p ∈ CFSG.Open.uniqueFourSigma c.S.M) (d : SylowThreeData G) (hdM : d.M = c.S.M)
    (hdL : d.L = c.L) (hinj : Function.Injective d.Lf)
    (hperm : ∀ m ∈ c.S.M, ∀ i, ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    (h1 : ∀ i, CFSG.Open.pRank p (d.Lf i) ≤ 1) :
    ∃ T : Subgroup G, IsPGroup p T ∧ T ≠ ⊥ ∧
      T ≤ c.S.M ⊓ Subgroup.centralizer (d.AA : Set G) ∧
      (CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (d.AA : Set G)) ≤ 1 →
        ∀ i, CFSG.Open.pRank p (d.Lf i) = 1) := by
  obtain ⟨T, hTp, hTne, hTC, hsum⟩ :=
    Ctx812.exists_isPGroup_le_centralizer_AA c.toCtx812 hp d hdM hdL hinj hperm h1
  refine ⟨T, hTp, hTne, hTC, fun hle i => ?_⟩
  have h4 : 4 ≤ CFSG.Open.pRank p (d.Lf 0) + CFSG.Open.pRank p (d.Lf 1) +
      CFSG.Open.pRank p (d.Lf 2) + 1 := hsum hle
  have h10 := h1 0
  have h11 := h1 1
  have h12 := h1 2
  fin_cases i <;> simp <;> omega

end Counterexample4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
