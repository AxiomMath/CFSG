module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsGroup
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftB
import CFSG.LocalAnalysis.UniquenessCase.UC22P2014a
import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalPComponentCore
import CFSG.RankThree.PartOne.TAIL.QStruct
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.RankThree.PartOne.CTP.StrongPGlue

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private lemma le_sup_centralizer_of_le_normalizer (hSch : CFSG.LocalAnalysis.RankThreeUC.S15.KSch)
    {X K Y : Subgroup G} (hXk : CFSG.Open.IsKGroup ↥X) (hY : CFSG.Open.IsComponentOf Y X)
    (hKX : K ≤ X) (hK : ⁅K, K⁆ = K) (hKY : K ≤ normalizer (Y : Set G)) :
    K ≤ Y ⊔ centralizer (Y : Set G) := by
  intro k hk
  have hYtop : CFSG.Open.IsComponentOf (Y.subgroupOf X) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · have h := hY.2.1.comap X.subtype
      simpa [Subgroup.comap_subtype, Subgroup.subgroupOf_self] using h
    · exact CFSG.Open.IsQuasisimple.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hY.1) hY.2.2
  have hE : ⁅K.subgroupOf X, K.subgroupOf X⁆ = K.subgroupOf X := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hKX, hK]
  have hEJ : K.subgroupOf X ≤ Subgroup.normalizer (Y.subgroupOf X : Set ↥X) := by
    intro k' hk'
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h := (Subgroup.mem_normalizer_iff.mp (hKY (Subgroup.mem_subgroupOf.mp hk')) (y : G))
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hSch' := CFSG.LocalAnalysis.RankThreeUC.S15.perfect_le_sup_centralizer_component
    hSch hXk (K.subgroupOf X) (Y.subgroupOf X) hE hYtop hEJ
  have hmem : (⟨k, hKX hk⟩ : ↥X) ∈
      (Y.subgroupOf X) ⊔ centralizer (Y.subgroupOf X : Set ↥X) :=
    hSch' (Subgroup.mem_subgroupOf.mpr hk)
  obtain ⟨y, hy, c, hc, hyc⟩ := CFSG.RankThree.PartOne.TAIL.mem_KC_iff.mp hmem
  have hyY : (y : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy
  have hcC : (c : G) ∈ centralizer (Y : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzX : z ∈ X := hY.1 hz
    have h := (Subgroup.mem_centralizer_iff.mp hc) (⟨z, hzX⟩ : ↥X)
      (Subgroup.mem_subgroupOf.mpr hz)
    simpa using congrArg (fun t : ↥X => (t : G)) h
  have hkc : k = (y : G) * (c : G) := by
    have := congrArg (fun t : ↥X => (t : G)) hyc
    simpa using this
  rw [hkc]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hyY) (Subgroup.mem_sup_right hcC)

private lemma mem_zpowers_of_mul_eq_of_orderOf_eq_prime {p : ℕ} [Fact p.Prime] {y c w : G}
    (hcomm : Commute y c) (hword : orderOf w = p) (hmul : w = y * c)
    (hc : ¬ p ∣ orderOf c) : w ∈ Subgroup.zpowers y := by
  have hcop : Nat.Coprime (orderOf w) (orderOf c) := by
    rw [hword]
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hc
  obtain ⟨e, he1, he0⟩ := Nat.chineseRemainder hcop 1 0
  have hwe : w ^ e = w := by
    rw [← pow_mod_orderOf, show e % orderOf w = 1 % orderOf w from he1, pow_mod_orderOf]
    simp
  have hce : c ^ e = 1 := by
    rw [← pow_mod_orderOf, show e % orderOf c = 0 % orderOf c from he0, pow_mod_orderOf]
    simp
  have hweq : y ^ e = w := by
    have h1 : w ^ e = y ^ e := by
      rw [hmul, hcomm.mul_pow, hce, mul_one]
    rw [hwe] at h1
    exact h1.symm
  have hmem : y ^ e ∈ Subgroup.zpowers y := by
    simpa using Subgroup.zpow_mem (Subgroup.zpowers y) (Subgroup.mem_zpowers y) (e : ℤ)
  rwa [← hweq]

private lemma mem_of_commute_of_isStronglyPEmbedded {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hM : IsStronglyPEmbedded p M) {w c : G} (hwM : w ∈ M) (hword : orderOf w = p)
    (hcw : Commute w c) : c ∈ M := by
  have hw1 : w ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hword
    exact (Fact.out : p.Prime).ne_one hword.symm
  have hwp : w ^ p = 1 := by rw [← hword, pow_orderOf_eq_one]
  refine (hM.centralizer_le hw1 hwp hwM) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  exact hcw

private lemma not_dvd_orderOf_of_isStronglyPEmbedded {p : ℕ} {M Y : Subgroup G}
    (hM : IsStronglyPEmbedded p M) (hYM : ¬ Y ≤ M) {c : G} (hcM : c ∈ M)
    (hcY : c ∈ centralizer (Y : Set G)) : ¬ p ∣ orderOf c := by
  have hzpM : Subgroup.zpowers c ≤ M := Subgroup.zpowers_le.mpr hcM
  have hzpC : Subgroup.zpowers c ≤ centralizer (Y : Set G) := Subgroup.zpowers_le.mpr hcY
  have hYN : Y ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    (Subgroup.le_centralizer_iff.mpr hzpC).trans (Subgroup.centralizer_le_normalizer _)
  have h := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p2014a_not_dvd_card_of_le hM hYM hzpM hYN
  rwa [Nat.card_zpowers] at h

private lemma not_mem_pCore_two_of_orderOf_eq_odd_prime {K : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {w : ↥K} (hword : orderOf w = p) : w ∉ CFSG.pCore 2 ↥K := by
  intro hmem
  have hzp : Subgroup.zpowers w ≤ CFSG.pCore 2 ↥K := Subgroup.zpowers_le.mpr hmem
  have h2 : IsPGroup 2 (Subgroup.zpowers w) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).to_le hzp
  have hpz : IsPGroup p (Subgroup.zpowers w) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hword, pow_one])
  have hdis : Disjoint (Subgroup.zpowers w) (Subgroup.zpowers w) :=
    IsPGroup.disjoint_of_ne 2 p (Ne.symm hp2) _ _ h2 hpz
  have hbot : Subgroup.zpowers w = ⊥ := disjoint_self.mp hdis
  have hw1 : w = 1 := Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_zpowers w)
  rw [hw1, orderOf_one] at hword
  exact (Fact.out : p.Prime).ne_one hword.symm

private lemma normal_subgroupOf_inf_of_le_normalizer {Y K : Subgroup G}
    (hKY : K ≤ normalizer (Y : Set G)) : ((Y ⊓ K).subgroupOf K).Normal := by
  refine Subgroup.normal_subgroupOf_of_le_normalizer (N := Y ⊓ K) (H := K) ?_
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hx := Subgroup.mem_normalizer_iff.mp (hKY hk) x
  constructor
  · rintro ⟨hxY, hxK⟩
    exact ⟨hx.mp hxY, K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk)⟩
  · rintro ⟨hxY, hxK⟩
    have hKx : x ∈ K := by
      have h : k⁻¹ * (k * x * k⁻¹) * k = x := by group
      rw [← h]
      exact K.mul_mem (K.mul_mem (K.inv_mem hk) hxK) hk
    exact ⟨hx.mpr hxY, hKx⟩

private lemma eq_top_of_normal_of_not_le_pCore {K : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hKs : IsSimpleGroup (Bar2 K)) {Q : Subgroup ↥K} (hQ : Q.Normal)
    (hQn : ¬ Q ≤ CFSG.pCore 2 ↥K) : Q = ⊤ := by
  classical
  haveI : Q.Normal := hQ
  let π₀ : ↥K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  have hQmapNe : Q.map π₀ ≠ ⊥ := by
    intro hbot
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    exact hQn hbot
  have hQmapTop : Q.map π₀ = ⊤ := by
    haveI : (Q.map π₀).Normal := hQ.map π₀ (QuotientGroup.mk'_surjective _)
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Q.map π₀)).resolve_left hQmapNe
  have hsup : Q ⊔ CFSG.pCore 2 ↥K = ⊤ := by
    have h := Subgroup.comap_map_eq π₀ Q
    rw [hQmapTop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  let ρ : ↥K →* (↥K ⧸ Q) := QuotientGroup.mk' Q
  have hkerρ : ρ.ker = Q := QuotientGroup.ker_mk' Q
  have hQmapBot : Q.map ρ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    exact hkerρ.ge hx
  have hPmapTop : (CFSG.pCore 2 ↥K).map ρ = ⊤ := by
    have h := congrArg (Subgroup.map ρ) hsup
    rw [Subgroup.map_sup,
      Subgroup.map_top_of_surjective ρ (QuotientGroup.mk'_surjective _)] at h
    rw [hQmapBot, bot_sup_eq] at h
    exact h
  have hquot2 : IsPGroup 2 (↥K ⧸ Q) := by
    have h := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).map ρ
    rw [hPmapTop] at h
    exact h.of_equiv Subgroup.topEquiv
  haveI : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
  exact CFSG.ComponentClassification.LiteratureLocal.eq_top_of_isPGroup_quotient_of_perfect Q hquot2

private lemma mem_of_orderOf_eq_prime (hSch : CFSG.LocalAnalysis.RankThreeUC.S15.KSch)
    {X K Y M : Subgroup G} (hXk : CFSG.Open.IsKGroup ↥X) (hY : CFSG.Open.IsComponentOf Y X)
    (hKX : K ≤ X) (hK : ⁅K, K⁆ = K) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hM : IsStronglyPEmbedded p M) (hKM : K ≤ M) (hYM : ¬ Y ≤ M)
    (hKY : K ≤ normalizer (Y : Set G)) {w : G} (hwK : w ∈ K)
    (hword : orderOf w = p) : w ∈ Y := by
  obtain ⟨y, hyY, c, hcC, hyc⟩ :=
    CFSG.RankThree.PartOne.TAIL.mem_KC_iff.mp
      (le_sup_centralizer_of_le_normalizer hSch hXk hY hKX hK hKY hwK)
  have hcomm : Commute y c := Subgroup.mem_centralizer_iff.mp hcC y hyY
  have hcw : Commute w c := by
    rw [hyc]
    exact hcomm.mul_left (Commute.refl c)
  have hcM : c ∈ M := mem_of_commute_of_isStronglyPEmbedded hM (hKM hwK) hword hcw
  have hnot : ¬ p ∣ orderOf c := not_dvd_orderOf_of_isStronglyPEmbedded hM hYM hcM hcC
  exact Subgroup.zpowers_le.mpr hyY
    (mem_zpowers_of_mul_eq_of_orderOf_eq_prime hcomm hword hyc hnot)

theorem le_of_le_normalizer_isComponentOf (hSch : CFSG.LocalAnalysis.RankThreeUC.S15.KSch)
    {X K Y M : Subgroup G} (hXk : CFSG.Open.IsKGroup ↥X) (hY : CFSG.Open.IsComponentOf Y X)
    (hKX : K ≤ X) (hK : ⁅K, K⁆ = K) (hKs : IsSimpleGroup (Bar2 K)) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K) (hM : IsStronglyPEmbedded p M) (hKM : K ≤ M)
    (hYM : ¬ Y ≤ M) (hKY : K ≤ normalizer (Y : Set G)) : K ≤ Y := by
  obtain ⟨w, hword⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) p hpK
  have hwordG : orderOf (w : G) = p := by rw [Subgroup.orderOf_coe, hword]
  have hwY : (w : G) ∈ Y :=
    mem_of_orderOf_eq_prime hSch hXk hY hKX hK hp2 hM hKM hYM hKY w.2 hwordG
  have hwNotCore : w ∉ CFSG.pCore 2 ↥K :=
    not_mem_pCore_two_of_orderOf_eq_odd_prime hp2 hword
  have hQn : ¬ (Y ⊓ K).subgroupOf K ≤ CFSG.pCore 2 ↥K := by
    intro hle
    exact hwNotCore (hle (Subgroup.mem_subgroupOf.mpr ⟨hwY, w.2⟩))
  have hQtop : (Y ⊓ K).subgroupOf K = ⊤ :=
    eq_top_of_normal_of_not_le_pCore hK hKs
      (normal_subgroupOf_inf_of_le_normalizer hKY) hQn
  intro g hg
  have hgQ : (⟨g, hg⟩ : ↥K) ∈ (Y ⊓ K).subgroupOf K := by
    rw [hQtop]
    exact Subgroup.mem_top _
  simpa using (Subgroup.mem_subgroupOf.mp hgQ).1

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
