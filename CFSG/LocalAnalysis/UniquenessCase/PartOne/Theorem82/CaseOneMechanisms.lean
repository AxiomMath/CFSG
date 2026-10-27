module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOne
import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4End
import CFSG.LocalAnalysis.RankFourTheoremC.PPointSmallTypes
import CFSG.RankThree.PartOne.S11d.OutCentral
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
import CFSG.RankThree.OddKernel.CentralCoverComponentModels
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Diag.Fixed

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Case811Sylow

theorem exists_mem_L_mul_eq {c : Counterexample4 G} (h : Case811Sylow c) {m : G}
    (hm : m ∈ c.S.M) :
    ∃ l ∈ c.L, ∃ n ∈ c.S.M ⊓ Subgroup.normalizer (h.A : Set G), m = l * n := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hP_sylow_L : CFSG.ABGLocalTools.IsSylowOf 3 h.P c.L :=
    h.sylow.of_le h.P_le_L c.hyp81.1
  have unique_of_le_normalizer : ∀ {n : G}, n ∈ Subgroup.normalizer (h.P : Set G) →
      h.A.map (MulAut.conj n).toMonoidHom = h.A := by
    intro n hn
    have hPn : h.P.map (MulAut.conj n).toMonoidHom = h.P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
    have hAle : h.A.map (MulAut.conj n).toMonoidHom ≤ h.P := by
      rw [← hPn]
      exact Subgroup.map_mono h.A_le
    have hAab : CFSG.Open.IsElemAbelian 3 (h.A.map (MulAut.conj n).toMonoidHom) :=
      h.elemAbelian.map _
    have hAcard : Nat.card (h.A.map (MulAut.conj n).toMonoidHom) = 27 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, h.card_A]
    exact h.unique _ hAle hAab hAcard
  let P' : Subgroup G := h.P.map (MulAut.conj m).toMonoidHom
  have hmN : m ∈ Subgroup.normalizer (c.L : Set G) := c.le_normalizer_L hm
  have hP'_le_L : P' ≤ c.L := by
    rintro _ ⟨q, hq, rfl⟩
    have hLmap : c.L.map (MulAut.conj m).toMonoidHom = c.L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hmN
    have hq' : (MulAut.conj m).toMonoidHom q ∈ c.L.map (MulAut.conj m).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨q, h.P_le_L hq, rfl⟩
    rwa [hLmap] at hq'
  have hP'_sylow_L : CFSG.ABGLocalTools.IsSylowOf 3 P' c.L := by
    have hcard : Nat.card P' = Nat.card h.P :=
      Subgroup.card_map_of_injective (MulAut.conj m).injective
    refine CFSG.ABGLocalTools.isSylowOf_of_card hP'_le_L ?_
    rw [hcard]
    exact hP_sylow_L.card_eq
  obtain ⟨l, hlL, hlconj⟩ := hP_sylow_L.exists_mem_conj hP'_sylow_L
  have hnM : l⁻¹ * m ∈ c.S.M :=
    c.S.M.mul_mem (c.S.M.inv_mem (c.hyp81.1 hlL)) hm
  have hnN : l⁻¹ * m ∈ Subgroup.normalizer (h.P : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : h.P.map (MulAut.conj (l⁻¹ * m)).toMonoidHom ≤ h.P := by
      rintro _ ⟨q, hq, rfl⟩
      have hmq : m * q * m⁻¹ ∈ P' := Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
      have h := (hlconj (m * q * m⁻¹)).mp hmq
      have hEq : (MulAut.conj (l⁻¹ * m)).toMonoidHom q = l⁻¹ * (m * q * m⁻¹) * l := by
        show (l⁻¹ * m) * q * (l⁻¹ * m)⁻¹ = l⁻¹ * (m * q * m⁻¹) * l
        group
      rw [hEq]
      exact h
    exact Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj _).injective])
  have hnA : l⁻¹ * m ∈ Subgroup.normalizer (h.A : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact unique_of_le_normalizer hnN
  exact ⟨l, hlL, l⁻¹ * m, Subgroup.mem_inf.mpr ⟨hnM, hnA⟩, by group⟩

theorem pRank_M_le_pRank_L_add_one {c : Counterexample4 G} (h : Case811Sylow c) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2)
    (hpA : ∀ g ∈ c.S.M ⊓ Subgroup.normalizer (h.A : Set G), IsPGroup p (Subgroup.zpowers g) →
      g ∈ Subgroup.centralizer (h.A : Set G))
    (hC : CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (h.A : Set G)) ≤ 1) :
    CFSG.Open.pRank p c.S.M ≤ CFSG.Open.pRank p c.L + 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hpp : p.Prime := Fact.out
  haveI : ((c.L).subgroupOf c.S.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer c.hyp81.1).mpr c.le_normalizer_L
  let N : Subgroup G := c.S.M ⊓ Subgroup.normalizer (h.A : Set G)
  let C : Subgroup G := c.S.M ⊓ Subgroup.centralizer (h.A : Set G)
  obtain ⟨T, hT⟩ := CFSG.ABGLocalTools.exists_isSylowOf p N
  have hTN : T ≤ N := hT.le
  have hT_p : IsPGroup p T := hT.isPGroup
  have hTC : T ≤ C := by
    refine le_inf (hTN.trans inf_le_left) ?_
    intro t htT
    exact hpA t (hTN htT) (hT_p.to_le (Subgroup.zpowers_le.mpr htT))
  have hrankT : CFSG.Open.pRank p T ≤ 1 :=
    (CFSG.SectionRank.pRank_mono hpp.one_lt hTC).trans hC
  have hTcyc : IsCyclic ↥T := by
    refine CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one hpp hp2 le_rfl hT_p ?_
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
  let φ : ↥N →* (↥c.S.M ⧸ (c.L).subgroupOf c.S.M) :=
    (QuotientGroup.mk' ((c.L).subgroupOf c.S.M)).comp
      (Subgroup.inclusion (show N ≤ c.S.M from inf_le_left))
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective ((c.L).subgroupOf c.S.M) q
    obtain ⟨l, hlL, n, hnN, hmn⟩ := h.exists_mem_L_mul_eq m.2
    have hnM : n ∈ c.S.M := hnN.1
    refine ⟨⟨n, hnN⟩, ?_⟩
    show QuotientGroup.mk' ((c.L).subgroupOf c.S.M) ⟨n, hnM⟩ =
      QuotientGroup.mk' ((c.L).subgroupOf c.S.M) m
    have hmdecomp : (m : ↥c.S.M) =
        Subgroup.inclusion c.hyp81.1 ⟨l, hlL⟩ * ⟨n, hnM⟩ := by
      apply Subtype.ext
      exact hmn
    rw [hmdecomp, map_mul]
    have hker : QuotientGroup.mk' ((c.L).subgroupOf c.S.M)
        (Subgroup.inclusion c.hyp81.1 (⟨l, hlL⟩ : c.L)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hlL)
    rw [hker, one_mul]
  have hQrank : CFSG.pRank p (↥c.S.M ⧸ (c.L).subgroupOf c.S.M) ≤ 1 :=
    CFSG.Quasithin.H13.Ch4.L436.pRank_le_one_of_surjective' hpp hp2 φ hφ hNrank
  have hQrank' : CFSG.Open.pRank p
      (⊤ : Subgroup (↥c.S.M ⧸ (c.L).subgroupOf c.S.M)) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hQrank
  have hsub := CFSG.RankThree.OddKernel.pRank_le_add_of_normal (p := p) hpp
    ((c.L).subgroupOf c.S.M)
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

theorem pRank_M_le_pRank_L_of_not_dvd {c : Counterexample4 G} (h : Case811Sylow c) {p : ℕ}
    [Fact p.Prime]
    (hpA : ∀ g ∈ c.S.M ⊓ Subgroup.normalizer (h.A : Set G), IsPGroup p (Subgroup.zpowers g) →
      g ∈ Subgroup.centralizer (h.A : Set G))
    (hC : ¬ p ∣ Nat.card (c.S.M ⊓ Subgroup.centralizer (h.A : Set G) : Subgroup G)) :
    CFSG.Open.pRank p c.S.M ≤ CFSG.Open.pRank p c.L := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hpp : p.Prime := Fact.out
  haveI : ((c.L).subgroupOf c.S.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer c.hyp81.1).mpr c.le_normalizer_L
  let N : Subgroup G := c.S.M ⊓ Subgroup.normalizer (h.A : Set G)
  let C : Subgroup G := c.S.M ⊓ Subgroup.centralizer (h.A : Set G)
  obtain ⟨T, hT⟩ := CFSG.ABGLocalTools.exists_isSylowOf p N
  have hTN : T ≤ N := hT.le
  have hT_p : IsPGroup p T := hT.isPGroup
  have hTC : T ≤ C := by
    refine le_inf (hTN.trans inf_le_left) ?_
    intro t htT
    exact hpA t (hTN htT) (hT_p.to_le (Subgroup.zpowers_le.mpr htT))
  have hTbot : T = ⊥ := by
    by_contra hne
    obtain ⟨n, hn⟩ := hT_p.exists_card_eq
    have hnpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · exact absurd (Subgroup.card_eq_one.mp (by rw [hn, h0, pow_zero])) hne
      · exact hpos
    have hpdvdT : p ∣ Nat.card ↥T := by
      rw [hn]
      exact dvd_pow_self p (by omega)
    exact hC (hpdvdT.trans (Subgroup.card_dvd_of_le hTC))
  obtain ⟨Q₀, hQ₀⟩ := hT
  have hQ₀card : Nat.card ↥(Q₀ : Subgroup ↥N) = Nat.card ↥T := by
    rw [← hQ₀]
    exact (Subgroup.card_map_of_injective (K := (Q₀ : Subgroup ↥N)) (f := N.subtype)
      N.subtype_injective).symm
  have hNrank : CFSG.Open.pRank p (⊤ : Subgroup ↥N) = 0 := by
    rw [← (CFSG.SectionRank.pRank_sylow Q₀).1]
    have hQ₀bot : (Q₀ : Subgroup ↥N) = ⊥ := by
      apply Subgroup.card_eq_one.mp
      rw [hQ₀card, hTbot]
      exact Subgroup.card_bot
    rw [hQ₀bot]
    refine le_antisymm ?_ (Nat.zero_le _)
    refine CFSG.SectionRank.pRank_le (p := p) (H := ⊥) (k := 0) hpp.one_lt ?_
    intro E hE _
    rw [le_bot_iff] at hE
    rw [hE, Subgroup.card_bot, pow_zero]
  have hNpd : ¬ p ∣ Nat.card ↥N := by
    intro hpd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hpd
    have hxpow : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have h1 : 1 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥N) := by
      refine CFSG.SectionRank.le_pRank hpp.one_lt le_top
        (CFSG.Open.isElemAbelian_zpowers hxpow) ?_
      rw [Nat.card_zpowers, hx, pow_one]
    omega
  let φ : ↥N →* (↥c.S.M ⧸ (c.L).subgroupOf c.S.M) :=
    (QuotientGroup.mk' ((c.L).subgroupOf c.S.M)).comp
      (Subgroup.inclusion (show N ≤ c.S.M from inf_le_left))
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective ((c.L).subgroupOf c.S.M) q
    obtain ⟨l, hlL, n, hnN, hmn⟩ := h.exists_mem_L_mul_eq m.2
    have hnM : n ∈ c.S.M := hnN.1
    refine ⟨⟨n, hnN⟩, ?_⟩
    show QuotientGroup.mk' ((c.L).subgroupOf c.S.M) ⟨n, hnM⟩ =
      QuotientGroup.mk' ((c.L).subgroupOf c.S.M) m
    have hmdecomp : (m : ↥c.S.M) =
        Subgroup.inclusion c.hyp81.1 ⟨l, hlL⟩ * ⟨n, hnM⟩ := by
      apply Subtype.ext
      exact hmn
    rw [hmdecomp, map_mul]
    have hker : QuotientGroup.mk' ((c.L).subgroupOf c.S.M)
        (Subgroup.inclusion c.hyp81.1 (⟨l, hlL⟩ : c.L)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hlL)
    rw [hker, one_mul]
  have hQpd : ¬ p ∣ Nat.card (↥c.S.M ⧸ (c.L).subgroupOf c.S.M) := by
    intro hpd
    apply hNpd
    have hrange : φ.range = ⊤ := MonoidHom.range_eq_top.mpr hφ
    let e : (↥N ⧸ φ.ker) ≃* (↥c.S.M ⧸ (c.L).subgroupOf c.S.M) :=
      (QuotientGroup.quotientKerEquivRange φ).trans
        ((MulEquiv.subgroupCongr hrange).trans (Subgroup.topEquiv (G :=
          ↥c.S.M ⧸ (c.L).subgroupOf c.S.M)))
    have hQcard : Nat.card (↥c.S.M ⧸ (c.L).subgroupOf c.S.M) =
        Nat.card (↥N ⧸ φ.ker) := (Nat.card_congr e.toEquiv).symm
    have hNcard : Nat.card ↥N = Nat.card (↥N ⧸ φ.ker) * Nat.card ↥φ.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    have hdvd : Nat.card (↥c.S.M ⧸ (c.L).subgroupOf c.S.M) ∣ Nat.card ↥N := by
      rw [hQcard, hNcard]
      exact dvd_mul_right _ _
    exact hpd.trans hdvd
  have hQrank : CFSG.Open.pRank p
      (⊤ : Subgroup (↥c.S.M ⧸ (c.L).subgroupOf c.S.M)) ≤ 0 := by
    refine CFSG.SectionRank.pRank_le (k := 0) hpp.one_lt ?_
    intro E _ hEab
    rw [pow_zero]
    obtain ⟨n, hn⟩ := (CFSG.Open.IsElemAbelian.isPGroup hEab).exists_card_eq
    have hn0 : n = 0 := by
      by_contra hne
      apply hQpd
      have hdvdE : p ∣ Nat.card ↥E := by
        rw [hn]
        exact dvd_pow_self p hne
      exact hdvdE.trans (Subgroup.card_subgroup_dvd_card E)
    rw [hn, hn0, pow_zero]
  have hQrank' : CFSG.pRank p (↥c.S.M ⧸ (c.L).subgroupOf c.S.M) ≤ 0 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hQrank
  have hsub := CFSG.RankThree.OddKernel.pRank_le_add_of_normal (p := p) hpp
    ((c.L).subgroupOf c.S.M)
  have hM' : CFSG.pRank p ↥c.S.M = CFSG.Open.pRank p c.S.M :=
    CFSG.SectionRank.pRank_coe_eq_openPRank p c.S.M
  have hL' : CFSG.pRank p ↥((c.L).subgroupOf c.S.M) = CFSG.Open.pRank p c.L := by
    rw [CFSG.pRank_congr_of_mulEquiv (Subgroup.subgroupOfEquivOfLe c.hyp81.1) p,
      CFSG.SectionRank.pRank_coe_eq_openPRank p c.L]
  rw [← hM', ← hL']
  exact hsub.trans (add_le_add_right hQrank' (CFSG.pRank p ↥((c.L).subgroupOf c.S.M)))

theorem false_of_pElement_not_mem_L {c : Counterexample4 G} (h : Case811Sylow c) {p : ℕ}
    (hp : p ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    {y : G} (hyM : y ∈ c.S.M) (hyA : y ∈ Subgroup.centralizer (h.A : Set G)) (hyp : orderOf y = p)
    (hyL : y ∉ c.L)
    (hdvd : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      p ∣ Nat.card (c.L ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp_prime : p.Prime := hp.1.1
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hy_pow : y ^ p = 1 := by rw [← hyp]; exact pow_orderOf_eq_one y
  have hy_cent : ∀ X : Subgroup G, X ≤ h.A → y ∈ Subgroup.centralizer (X : Set G) := by
    intro X hXA
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_iff.mp hyA x (hXA hx)
  have hR_X : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      ∃ R : Subgroup G, CFSG.Open.IsElemAbelian p R ∧ Nat.card R = p ^ 2 ∧
        R ≤ c.S.M ⊓ Subgroup.normalizer (X : Set G) := by
    intro X hXA hXcard
    let Y : Subgroup G := c.L ⊓ Subgroup.centralizer (X : Set G)
    have hyN : y ∈ Subgroup.normalizer (Y : Set G) := by
      have hyNL : y ∈ Subgroup.normalizer (c.L : Set G) := c.le_normalizer_L hyM
      have hyNC : y ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) :=
        Subgroup.le_normalizer (hy_cent X hXA)
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hyNL, hyNC⟩
    have hpdvdY : p ∣ Nat.card Y := hdvd X hXA hXcard
    obtain ⟨u, huY, huord, huCent⟩ :=
      CFSG.Quasithin.exists_orderOf_eq_of_isPGroup_normalizer
        (P := Subgroup.zpowers y) (H := Y)
        (CFSG.Open.isElemAbelian_zpowers hy_pow).isPGroup
        (Subgroup.zpowers_le.mpr hyN) hpdvdY
    have huy : u * y = y * u :=
      (Subgroup.mem_centralizer_iff.mp huCent y (Subgroup.mem_zpowers y)).symm
    have huL : u ∈ c.L := huY.1
    have huC : u ∈ Subgroup.centralizer (X : Set G) := huY.2
    have hu_not : u ∉ Subgroup.zpowers y := by
      intro hu
      have hEq : Subgroup.zpowers u = Subgroup.zpowers y := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hu) ?_
        rw [Nat.card_zpowers, Nat.card_zpowers, huord, hyp]
      have hy_mem : y ∈ Subgroup.zpowers u := by
        rw [hEq]
        exact Subgroup.mem_zpowers y
      exact hyL (Subgroup.zpowers_le.mpr huL hy_mem)
    have hu_pow : u ^ p = 1 := by rw [← huord]; exact pow_orderOf_eq_one u
    let R : Subgroup G := Subgroup.zpowers u ⊔ Subgroup.zpowers y
    have hcomm_uy : ∀ a ∈ Subgroup.zpowers u, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
      intro a ha b hb
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact ((show Commute u y from huy).zpow_zpow m n).eq
    have hR_elem : CFSG.Open.IsElemAbelian p R :=
      CFSG.Open.IsElemAbelian.sup_of_commute
        (CFSG.Open.isElemAbelian_zpowers hu_pow)
        (CFSG.Open.isElemAbelian_zpowers hy_pow) hcomm_uy
    have hinf : Subgroup.zpowers u ⊓ Subgroup.zpowers y = ⊥ :=
      CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Diag.zpowers_inf_eq_bot
        hp_prime hu_pow hu_not
    have hR_card : Nat.card R = p ^ 2 := by
      obtain ⟨hcard, -⟩ :=
        CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
          (Subgroup.zpowers u) (Subgroup.zpowers y) hcomm_uy
      rw [hinf, Nat.card_zpowers, Nat.card_zpowers, huord, hyp] at hcard
      simpa [pow_two] using hcard
    have hRM : R ≤ c.S.M :=
      sup_le (Subgroup.zpowers_le.mpr (c.hyp81.1 huL)) (Subgroup.zpowers_le.mpr hyM)
    have hRN : R ≤ Subgroup.normalizer (X : Set G) :=
      sup_le ((Subgroup.zpowers_le.mpr huC).trans (Subgroup.centralizer_le_normalizer (X : Set G)))
        ((Subgroup.zpowers_le.mpr (hy_cent X hXA)).trans
          (Subgroup.centralizer_le_normalizer (X : Set G)))
    exact ⟨R, hR_elem, hR_card, le_inf hRM hRN⟩
  refine false_of_rank_conditions h hp h76 ?_ ?_ ?_
  ·
    intro E hEA hEab hEcard
    have hle : Subgroup.zpowers y ≤ c.S.M ⊓ Subgroup.centralizer (E : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hyM, hy_cent E hEA⟩)
    have h1 : 1 ≤ CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (E : Set G)) :=
      CFSG.SectionRank.le_pRank hp_prime.one_lt hle
        (CFSG.Open.isElemAbelian_zpowers hy_pow) (by rw [Nat.card_zpowers, hyp, pow_one])
    omega
  ·
    intro E X hXE hEA hEab hEcard hXcard
    obtain ⟨R, hR_elem, hR_card, hR_le⟩ := hR_X X (hXE.trans hEA) hXcard
    have h2 : 2 ≤ CFSG.Open.pRank p (c.S.M ⊓ Subgroup.normalizer (X : Set G)) :=
      CFSG.SectionRank.le_pRank hp_prime.one_lt hR_le hR_elem hR_card
    omega
  ·
    intro X hXA hXcard
    exact (hdvd X hXA hXcard).trans
      (Subgroup.card_dvd_of_le
        (inf_le_right.trans (Subgroup.centralizer_le_normalizer (X : Set G))))

end Case811Sylow

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
