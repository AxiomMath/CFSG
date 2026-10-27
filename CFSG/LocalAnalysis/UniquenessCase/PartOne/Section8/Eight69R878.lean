module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69Common
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xKGammaLemmas
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.ClassicalGroups.PCoreSection
public import CFSG.Quasithin.Vol2.Ch4Sec3L4316L34
public import CFSG.Quasithin.Background.A3FactsRank
public import CFSG.LocalAnalysis.UniquenessCase.UCKPCenter
public import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsU3 IsSL3 IsSU3)

private theorem card_griessHopfMultiplier_psl3 (hgr : CFSG.Open.GriessAllModelsStatement)
    {Y : Type} [Group Y] (hY : CFSG.Blueprint.LieModel Y .PSL 3 2 2) :
    Nat.card (griessHopfMultiplier Y) = 48 := by
  have hcl : CFSG.Open.StatedClassicalModel Y .PSL 3 2 2 :=
    CFSG.Blueprint.LieModel.statedClassicalModel hY (by decide)
  have hmodel : CFSG.Models.LieModel Y .PSL 3 2 2 := ⟨hcl.1, Or.inl hcl⟩
  obtain ⟨-, ⟨g⟩⟩ := hgr Y .PSL 3 2 2 hmodel
  rw [Nat.card_congr g.toEquiv, Nat.card_prod]
  unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
  simp only [Nat.card_prod, Nat.card_zmod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _)]
  simp [CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders]

private theorem false_of_prime_dvd_card_center_of_pCoreOf_eq_bot
    {G : Type} [Group G] [Finite G] {X : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card (Subgroup.center ↥X)) (hcore : pCoreOf p X = ⊥) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥X) p hdvd
  have hz1 : ((z : Subgroup.center ↥X) : ↥X) ≠ 1 := by
    intro h
    have hz' : (z : Subgroup.center ↥X) = 1 := Subtype.ext h
    rw [hz', orderOf_one] at hz
    exact hp.ne_one hz.symm
  set w : ↥X := ((z : Subgroup.center ↥X) : ↥X) with hw
  set N : Subgroup G := Subgroup.zpowers ((w : ↥X) : G) with hN
  have hNX : N ≤ X := by
    rintro _ ⟨k, rfl⟩
    exact Subgroup.zpow_mem (K := X) w.2 k
  have hword : orderOf ((w : ↥X) : G) = p := by
    rw [Subgroup.orderOf_coe w, hw]
    exact (Subgroup.orderOf_coe (z : Subgroup.center ↥X)).trans hz
  have hNp : IsPGroup p N := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [hN, Nat.card_zpowers, hword, pow_one]
  have hnorm : ∀ x ∈ X, ∀ y ∈ N, x * y * x⁻¹ ∈ N := by
    intro x hx y hy
    rw [hN] at hy ⊢
    obtain ⟨k, rfl⟩ := hy
    rw [← conj_zpow]
    have hcomm : x * ((w : ↥X) : G) * x⁻¹ = ((w : ↥X) : G) := by
      have hzc : w ∈ Subgroup.center ↥X := z.2
      have h2 := (Subgroup.mem_center_iff.mp hzc) ⟨x, hx⟩
      have h4 := congrArg (fun t : ↥X => (t : G)) h2
      simp only [Subgroup.coe_mul] at h4
      rw [h4]
      group
    rw [hcomm]
    exact ⟨k, rfl⟩
  have hle : N ≤ pCoreOf p X :=
    CFSG.ClassicalGroups.PCoreSection.le_pCoreOf hNX hnorm hNp
  rw [hcore] at hle
  have hwN : ((w : ↥X) : G) ∈ N := Subgroup.mem_zpowers _
  have hwbot : ((w : ↥X) : G) ∈ (⊥ : Subgroup G) := hle hwN
  rw [Subgroup.mem_bot] at hwbot
  exact hz1 (Subtype.ext hwbot)

private theorem center_eq_bot_of_card_dvd_48 {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hdvd : Nat.card (Subgroup.center ↥X) ∣ 48)
    (h2 : pCoreOf 2 X = ⊥) (h3 : pCoreOf 3 X = ⊥) :
    Subgroup.center ↥X = ⊥ := by
  rw [Subgroup.eq_bot_iff_card]
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp hpdvd
  have hp48 : p ∣ 48 := hpdvd.trans hdvd
  have h48 : (48 : ℕ) = 2 ^ 4 * 3 := by norm_num
  rw [h48] at hp48
  rcases hp.dvd_mul.mp hp48 with h | h
  · have hp2dvd : p ∣ 2 := hp.dvd_of_dvd_pow h
    have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2dvd
    subst this
    exact false_of_prime_dvd_card_center_of_pCoreOf_eq_bot hp hpdvd h2
  · have : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
    subst this
    exact false_of_prime_dvd_card_center_of_pCoreOf_eq_bot hp hpdvd h3

theorem two_le_pRank_three_of_isL3 {X : Type} [Group X] [Finite X] (h : IsL3 X 2) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
  CFSG.Quasithin.H13.Ch4.L4316.two_le_pRank_three_of_isPSL
    (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))

private theorem pRank_subgroupOf_eq {G : Type} [Group G] [Finite G] {p : ℕ} (hp : 1 < p)
    {H Q : Subgroup G} (hQH : Q ≤ H) :
    CFSG.Open.pRank p (Q.subgroupOf H) = CFSG.Open.pRank p Q := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (Q.subgroupOf H),
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup Q]
  exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := p) hp
    (Subgroup.subgroupOfEquivOfLe hQH)

theorem pRank_eq_pRank_of_isSylowOf {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Q H : Subgroup G} (h : CFSG.ABGLocalTools.IsSylowOf p Q H) :
    CFSG.Open.pRank p Q = CFSG.Open.pRank p H := by
  obtain ⟨S, hS⟩ := h.exists_sylow_eq_subgroupOf
  calc CFSG.Open.pRank p Q = CFSG.Open.pRank p (Q.subgroupOf H) :=
        (pRank_subgroupOf_eq (Fact.out : p.Prime).one_lt h.le).symm
    _ = CFSG.Open.pRank p (S : Subgroup ↥H) := by rw [hS]
    _ = CFSG.Open.pRank p (⊤ : Subgroup ↥H) := (CFSG.SectionRank.pRank_sylow S).1
    _ = CFSG.Open.pRank p H := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup H).symm

theorem one_le_pRank_zpowers_of_mem_isPGroup
    {G : Type} [Group G] [Finite G] {P : Subgroup G}
    (hP : IsPGroup 3 P) {x : G} (hxP : x ∈ P) (hx1 : x ≠ 1) :
    1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers x) := by
  obtain ⟨n, hn⟩ := hP ⟨x, hxP⟩
  have hxpow : x ^ (3 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have hdvd : orderOf x ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hxpow
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hjpos : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · exfalso
      rw [h0, pow_zero] at hj
      exact hx1 (orderOf_eq_one_iff.mp hj)
    · exact hpos
  set y : G := x ^ (3 ^ (j - 1)) with hy
  have hyorder : orderOf y = 3 := by
    rw [hy, orderOf_pow, hj]
    rw [Nat.gcd_eq_right]
    · rw [Nat.pow_div (Nat.sub_le j 1) (by norm_num : 0 < 3),
        show j - (j - 1) = 1 by omega, pow_one]
    · exact pow_dvd_pow 3 (Nat.sub_le j 1)
  have hyzp : Subgroup.zpowers y ≤ Subgroup.zpowers x := by
    rw [Subgroup.zpowers_le]
    rw [hy]
    exact Subgroup.pow_mem (Subgroup.zpowers x) (Subgroup.mem_zpowers x) _
  have h1 : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers y) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    refine CFSG.Quasithin.A3Facts.one_le_pRank_of_orderOf Nat.prime_three
      (x := (⟨y, Subgroup.mem_zpowers y⟩ : ↥(Subgroup.zpowers y))) ?_
    rw [← Subgroup.orderOf_coe (⟨y, Subgroup.mem_zpowers y⟩ : ↥(Subgroup.zpowers y))]
    exact hyorder
  exact h1.trans (CFSG.SectionRank.pRank_mono (by norm_num) hyzp)

private theorem normal_of_isComponentOf_of_center_eq_bot
    {G : Type} [Group G] [Finite G] {X K : Subgroup G}
    (hcomp : CFSG.Open.IsComponentOf X K) (hZ : Subgroup.center ↥X = ⊥)
    (hrank : 2 ≤ CFSG.Open.pRank 3 X) (hKrank : CFSG.Open.pRank 3 K ≤ 3) :
    (X.subgroupOf K).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hcomp.1]
  by_contra hnot
  simp only [SetLike.le_def, not_forall] at hnot
  obtain ⟨g, hgK, hgnorm⟩ := hnot
  set Xg : Subgroup G := X.map (MulAut.conj g).toMonoidHom with hXg
  have hKg : K.map (MulAut.conj g).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgK)
  have hXgK : Xg ≤ K := by
    rw [hXg]
    exact (Subgroup.map_mono hcomp.1).trans hKg.le
  have hXgNe : Xg ≠ X := fun h =>
    hgnorm (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hXg.symm.trans h))
  have hsubXg : CFSG.Open.IsSubnormal Xg K := by
    rw [hXg]
    have h := CFSG.Open.IsSubnormal.map (MulAut.conj g).toMonoidHom hcomp.2.1
    rwa [hKg] at h
  have hqXg : CFSG.Open.IsQuasisimple ↥Xg := by
    rw [hXg]
    exact CFSG.Open.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective X (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).symm hcomp.2.2
  have hcompXg : CFSG.Open.IsComponentOf Xg K := ⟨hXgK, hsubXg, hqXg⟩
  have hXKcomp : CFSG.IsComponent (X.subgroupOf K) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hcomp.1).1
      (CFSG.Assembly.isComponentOf_iff_open.mpr hcomp)
  have hXgKcomp : CFSG.IsComponent (Xg.subgroupOf K) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hXgK).1
      (CFSG.Assembly.isComponentOf_iff_open.mpr hcompXg)
  rcases CFSG.LocalCores.distinct_components_commute hXKcomp hXgKcomp with heq | hcom
  · exfalso
    apply hXgNe
    have h1 : (X.subgroupOf K).map K.subtype = (Xg.subgroupOf K).map K.subtype := by rw [heq]
    rw [Subgroup.map_subgroupOf_eq_of_le hcomp.1,
      Subgroup.map_subgroupOf_eq_of_le hXgK] at h1
    exact h1.symm
  · have hcommX : ⁅X, Xg⁆ = ⊥ := by
      have hmap : (⁅X.subgroupOf K, Xg.subgroupOf K⁆).map K.subtype = ⁅X, Xg⁆ := by
        rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hcomp.1,
          Subgroup.map_subgroupOf_eq_of_le hXgK]
      rw [← hmap, hcom, Subgroup.map_bot]
    have hcommX' : ∀ x ∈ X, ∀ y ∈ Xg, x * y = y * x := by
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommX
      intro x hx y hy
      exact (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm
    have hinfX : X ⊓ Xg = ⊥ := by
      apply le_antisymm _ bot_le
      intro z hz
      rw [Subgroup.mem_bot]
      have hzc : (⟨z, hz.1⟩ : ↥X) ∈ Subgroup.center ↥X := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (hcommX' (y : G) y.2 z hz.2)
      rw [hZ, Subgroup.mem_bot] at hzc
      exact Subtype.ext_iff.mp hzc
    obtain ⟨E, hEX, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) X
    obtain ⟨F, hFXg, hFel, hFcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) Xg
    have h2Xg : 2 ≤ CFSG.Open.pRank 3 Xg := by
      rw [hXg]
      exact hrank.trans (CFSG.SectionRank.pRank_le_map (by norm_num)
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective X)
    have hcommEF : ∀ e ∈ E, ∀ f ∈ F, e * f = f * e :=
      fun e he f hf => hcommX' e (hEX he) f (hFXg hf)
    have hEsup_el : IsElemAbelian 3 (E ⊔ F) := hEel.sup_of_commute hFel hcommEF
    have hEFbot : E ⊓ F = ⊥ := by
      apply le_antisymm _ bot_le
      intro z hz
      have h1 : z ∈ X ⊓ Xg := ⟨hEX hz.1, hFXg hz.2⟩
      rw [hinfX, Subgroup.mem_bot] at h1
      exact h1
    have hcard_sup : Nat.card ↥(E ⊔ F) = Nat.card E * Nat.card F := by
      have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E F hcommEF).1
      rwa [hEFbot, Subgroup.card_bot, mul_one] at h
    have hcardEF : Nat.card ↥(E ⊔ F) =
        3 ^ (CFSG.Open.pRank 3 X + CFSG.Open.pRank 3 Xg) := by
      rw [hcard_sup, hEcard, hFcard, ← pow_add]
    have hle := CFSG.SectionRank.le_pRank (p := 3) (by norm_num)
      (le_rfl : E ⊔ F ≤ E ⊔ F) hEsup_el hcardEF
    have h4 : 4 ≤ CFSG.Open.pRank 3 (E ⊔ F) := by omega
    have hleK : CFSG.Open.pRank 3 (E ⊔ F) ≤ CFSG.Open.pRank 3 K :=
      CFSG.SectionRank.pRank_mono (by norm_num) (sup_le (hEX.trans hcomp.1) (hFXg.trans hXgK))
    omega

theorem strongly_closed_of_controlsFusion
    {G : Type} [Group G] [Finite G]
    {X K M Q P H : Subgroup G}
    (hKHM : K = H ⊓ M)
    (hXK : X ≤ K)
    (hPX : CFSG.ABGLocalTools.IsSylowOf 3 P X)
    (hPK : P = Q ⊓ X)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q K)
    (hXnormK : (X.subgroupOf K).Normal)
    (hfus : ControlsFusionIn M Q)
    (hNPM : Subgroup.normalizer (P : Set G) ≤ M)
    (hCen : ∀ x ∈ P, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M) :
    ∀ a ∈ P, ∀ g ∈ H, g⁻¹ * a * g ∈ Subgroup.normalizer (P : Set G) → g⁻¹ * a * g ∈ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKM : K ≤ M := hKHM.le.trans inf_le_right
  have hKH : K ≤ H := hKHM.le.trans inf_le_left
  have hXnorm : K ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mp hXnormK
  have hPH : P ≤ H := (hPK ▸ inf_le_right).trans (hXK.trans hKH)
  have hPK' : P ≤ K := (hPK ▸ inf_le_right).trans hXK
  intro a haP g hgH hbN
  set b : G := g⁻¹ * a * g with hb
  by_cases ha1 : a = 1
  · subst ha1
    rw [mul_one, inv_mul_cancel] at hb
    rw [hb]
    exact Subgroup.one_mem P
  have haH : a ∈ H := hPH haP
  have haQ : a ∈ Q := (hPK ▸ haP).1
  have haX : a ∈ X := (hPK ▸ haP).2
  have hbM : b ∈ M := hNPM hbN
  have hbH : b ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hgH) haH) hgH
  have hbK : b ∈ K := hKHM ▸ ⟨hbH, hbM⟩
  have ha3 : ∃ n, a ^ (3 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := hPX.isPGroup ⟨a, haP⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  obtain ⟨n, han⟩ := ha3
  have hbn : b ^ (3 ^ n) = 1 := by
    have h1 : (MulAut.conj g⁻¹) (a ^ (3 ^ n)) = 1 := by rw [han, map_one]
    have h2 : (MulAut.conj g⁻¹) (a ^ (3 ^ n)) = (g⁻¹ * a * g) ^ (3 ^ n) := by
      rw [map_pow]
      congr 1
      simp only [MulAut.conj_apply, inv_inv]
    rw [hb, ← h2]
    exact h1
  have hzpb : IsPGroup 3 (Subgroup.zpowers b) := by
    have hdvd : orderOf b ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hbn
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hbz2 : Subgroup.zpowers b ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.zpowers_le.mpr hbN
  have hR : IsPGroup 3 ↥(P ⊔ Subgroup.zpowers b) :=
    IsPGroup.to_sup_of_normal_left' (H := P) (K := Subgroup.zpowers b)
      hPX.isPGroup hzpb hbz2
  have hRleK : P ⊔ Subgroup.zpowers b ≤ K :=
    sup_le hPK' (Subgroup.zpowers_le.mpr hbK)
  obtain ⟨S, hSR⟩ := (hR.comap_subtype (K := K)).exists_le_sylow
  let Q₁ : Subgroup G := (S : Subgroup ↥K).map K.subtype
  have hQ₁ : CFSG.ABGLocalTools.IsSylowOf 3 Q₁ K := ⟨S, rfl⟩
  obtain ⟨k, hkK, hkconj⟩ :=
    CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hQ hQ₁
  have hkbQ : k⁻¹ * b * k ∈ Q := by
    have h1 : b ∈ Q₁ :=
      ⟨⟨b, hRleK (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))⟩,
        hSR (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)), rfl⟩
    exact (hkconj b).mp h1
  have hkaQ : k⁻¹ * a * k ∈ Q := by
    have h1 : a ∈ Q₁ :=
      ⟨⟨a, hRleK (Subgroup.mem_sup_left haP)⟩,
        hSR (Subgroup.mem_sup_left haP), rfl⟩
    exact (hkconj a).mp h1
  set c : G := k⁻¹ * b * k with hc
  have hagk : (g * k)⁻¹ * a * (g * k) = c := by
    rw [hc, hb]
    group
  have hmap : (Subgroup.zpowers a).map (MulAut.conj (g * k)⁻¹).toMonoidHom ≤ Q := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h1 : (MulEquiv.toMonoidHom (MulAut.conj (g * k)⁻¹)) a = c := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact hagk
    rw [map_zpow, h1]
    exact Q.zpow_mem hkbQ m
  obtain ⟨m, hmM, hm⟩ :=
    hfus (Subgroup.zpowers a) (Subgroup.zpowers_le.mpr haQ) (g * k) hmap
  have hca : c = m⁻¹ * a * m := by
    have h1 := hm a (Subgroup.mem_zpowers a)
    rw [hagk] at h1
    exact h1
  have hcen : g * k * m⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : (g * k * m⁻¹)⁻¹ * a * (g * k * m⁻¹) = a := by
      calc (g * k * m⁻¹)⁻¹ * a * (g * k * m⁻¹)
          = m * (k⁻¹ * (g⁻¹ * a * g) * k) * m⁻¹ := by group
        _ = m * c * m⁻¹ := by rw [← hb, ← hc]
        _ = m * (m⁻¹ * a * m) * m⁻¹ := by rw [hca]
        _ = a := by group
    have h2 : a * (g * k * m⁻¹) = (g * k * m⁻¹) * a := by
      have hy := congrArg (fun t => (g * k * m⁻¹) * t) h1
      simp only [← mul_assoc, mul_inv_cancel, one_mul] at hy
      simpa only [mul_assoc] using hy
    exact h2.symm
  have hgkmM : g * k * m⁻¹ ∈ M := hCen a haP ha1 hcen
  have hgM : g ∈ M := by
    have h1 : g = (g * k * m⁻¹) * m * k⁻¹ := by group
    rw [h1]
    exact M.mul_mem (M.mul_mem hgkmM hmM) (M.inv_mem (hKM hkK))
  have hgK : g ∈ K := hKHM ▸ ⟨hgH, hgM⟩
  have hbX : b ∈ X := by
    have hgN : g ∈ Subgroup.normalizer (X : Set G) := hXnorm hgK
    have h1 : g⁻¹ * a * g ∈ X := (Subgroup.mem_normalizer_iff''.mp hgN a).1 haX
    rw [hb]
    exact h1
  have hbP : b ∈ P := by
    have hbz3 : Subgroup.zpowers b ≤ X := Subgroup.zpowers_le.mpr hbX
    have hQ' : IsPGroup 3 ↥(P ⊔ Subgroup.zpowers b) :=
      IsPGroup.to_sup_of_normal_left' (H := P) (K := Subgroup.zpowers b)
        hPX.isPGroup hzpb hbz2
    have hQ'leX : P ⊔ Subgroup.zpowers b ≤ X := sup_le (hPK ▸ inf_le_right) hbz3
    have heq := CFSG.ABGLocalTools.IsSylowOf.eq_of_le hPX le_sup_left hQ'leX hQ'
    have hbR : b ∈ P ⊔ Subgroup.zpowers b := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
    rwa [heq] at hbR
  exact hbP

theorem r878_of_inputs {G : Type} [Group G] [Finite G]
    (D : CFSG.LocalAnalysis.UniquenessCase.UC22.Data G)
    (hK335 : K335) (hgr : CFSG.Open.GriessAllModelsStatement)
    (hSg : UC6S846.SigmaStd D) (h870 : R870 D) (h873 : R873 D) (h874 : R874 D) (h875 : R875 D)
    (h875c : R875Comp D) (h876 : R876 D) (h877 : R877 D) : R878 D := by
  intro L X H hmin
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hSL3_or_SU3, hO2⟩ := h873 L X H hmin
  have hO3 : pCoreOf 3 X = ⊥ := h877 L X H hmin
  have hq : CFSG.Open.IsQuasisimple ↥X := hSL3_or_SU3.elim (fun h => h.1) (fun h => h.1)
  have hperf : Group.IsPerfect ↥X := Group.isPerfect_def.2 hq.1
  have hdvd : Nat.card (Subgroup.center ↥X) ∣ 48 := by
    rcases hSL3_or_SU3 with hSL3 | hSU3
    · have hmult := card_griessHopfMultiplier_psl3 hgr hSL3.2
      have h := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf
        (MulEquiv.refl (↥X ⧸ Subgroup.center ↥X))
      rwa [hmult] at h
    · exact (CFSG.LocalAnalysis.UniquenessCase.UCK.u3Center_of_griess hgr ↥X 3 hSU3).trans
        (by norm_num)
  have hZ : Subgroup.center ↥X = ⊥ := center_eq_bot_of_card_dvd_48 hdvd hO2 hO3
  rcases hSL3_or_SU3 with hSL3 | hSU3
  ·
    exfalso
    have hL3X : IsL3 ↥X 2 := CFSG.Blueprint.LieModel.of_quotient_center hZ hSL3.2
    have h2X : 2 ≤ CFSG.Open.pRank 3 X := by
      rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup X]
      exact two_le_pRank_three_of_isL3 hL3X
    have hMrank : CFSG.Open.pRank 3 D.M ≤ 3 :=
      pRank_le_three_of_minCex hSg h870 hmin Nat.prime_three (by norm_num) (by omega)
    have hcomp : CFSG.Open.IsComponentOf X (H ⊓ D.M) := h875c L X H hmin
    have hXK : X ≤ H ⊓ D.M := hcomp.1
    have hXH : X ≤ H := hXK.trans inf_le_left
    have hXKc' : X ≤ H := hXH
    have hKrank : CFSG.Open.pRank 3 (H ⊓ D.M) ≤ 3 :=
      (CFSG.SectionRank.pRank_mono (by norm_num) inf_le_right).trans hMrank
    have hXnormK : ((X.subgroupOf (H ⊓ D.M))).Normal :=
      normal_of_isComponentOf_of_center_eq_bot hcomp hZ h2X hKrank
    have hXnormK' : H ⊓ D.M ≤ Subgroup.normalizer (X : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mp hXnormK
    obtain ⟨Q, hQ⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (H ⊓ D.M)
    have hPX : CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ X) X :=
      CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hQ hXK hXnormK'
    obtain ⟨hQsylH, hGammaM⟩ := h874 L X H hmin Q hQ hPX
    have hQleM : Q ≤ D.M := hQ.le.trans inf_le_right
    have hHrank : CFSG.Open.pRank 3 H ≤ 3 := by
      rw [← pRank_eq_pRank_of_isSylowOf hQsylH]
      exact (CFSG.SectionRank.pRank_mono (by norm_num) hQleM).trans hMrank
    have hPQrank : 1 ≤ CFSG.Open.pRank 3 (Q ⊓ X) := by
      rw [pRank_eq_pRank_of_isSylowOf hPX]
      omega
    have hNPM : Subgroup.normalizer (Q ⊓ X : Set G) ≤ D.M :=
      (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore le_rfl hPQrank).trans hGammaM
    have hCen : ∀ x ∈ Q ⊓ X, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ D.M := by
      intro x hx hx1
      have hxX : x ∈ X := hx.2
      have hzp_le : Subgroup.zpowers x ≤ Q ⊓ X := Subgroup.zpowers_le.mpr hx
      have hrankx : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers x) :=
        one_le_pRank_zpowers_of_mem_isPGroup hPX.isPGroup hx hx1
      have hnorm_le : Subgroup.normalizer (Subgroup.zpowers x : Set G) ≤ D.M :=
        (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hzp_le hrankx).trans hGammaM
      have hceq : Subgroup.centralizer ({x} : Set G) =
          Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      rw [hceq]
      exact (Subgroup.centralizer_le_normalizer _).trans hnorm_le
    have hfus : ControlsFusionIn D.M Q := h876 L X H hmin hL3X Q hQ hPX
    have hstrongG : ∀ a ∈ Q ⊓ X, ∀ g ∈ H,
        g⁻¹ * a * g ∈ Subgroup.normalizer (Q ⊓ X : Set G) → g⁻¹ * a * g ∈ Q ⊓ X :=
      strongly_closed_of_controlsFusion (X := X) (K := H ⊓ D.M) (M := D.M) (Q := Q)
        (P := Q ⊓ X) (H := H) rfl hXK hPX rfl hQ hXnormK hfus hNPM hCen
    have hHproper : H ≠ ⊤ := hmin.mem.1.1
    have hKGroup : CFSG.Open.IsKGroup ↥H :=
      CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_open_isKGroup
        D.standing.kProper H hHproper
    have hHrank' : CFSG.Open.pRank 3 (⊤ : Subgroup ↥H) ≤ 3 := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup H]
      exact hHrank
    have hP'H : Q ⊓ X ≤ H := (inf_le_right.trans hXH)
    have hLie : CFSG.Blueprint.LieModel (X.subgroupOf H) .PSL 3 2 2 :=
      CFSG.Blueprint.LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXH).symm hL3X
    have hP'sylow : CFSG.ABGLocalTools.IsSylowOf 3 ((Q ⊓ X).subgroupOf H) (X.subgroupOf H) := by
      have hPX' : CFSG.ABGLocalTools.IsSylowOf 3
          (((Q ⊓ X).subgroupOf H).map H.subtype) (((X.subgroupOf H)).map H.subtype) := by
        rwa [Subgroup.map_subgroupOf_eq_of_le hP'H, Subgroup.map_subgroupOf_eq_of_le hXH]
      exact (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 3) H
        (A := (Q ⊓ X).subgroupOf H) (B := X.subgroupOf H)).mp hPX'
    have hGamma : rankThreeGamma 1 3 ((Q ⊓ X).subgroupOf H) ≤
        Subgroup.normalizer ((X.subgroupOf H) : Set ↥H) := by
      change GLBCore 3 1 ((Q ⊓ X).subgroupOf H) ≤
        Subgroup.normalizer ((X.subgroupOf H) : Set ↥H)
      refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall ?_
      intro Y' hY'P' hY'rank
      set Y : Subgroup G := Y'.map H.subtype with hY
      have hYleP : Y ≤ Q ⊓ X := by
        rw [hY]
        exact (Subgroup.map_mono hY'P').trans (by
          rw [Subgroup.map_subgroupOf_eq_of_le hP'H])
      have hYrank' : 1 ≤ CFSG.Open.pRank 3 Y := by
        rw [hY]
        exact hY'rank.trans (CFSG.SectionRank.pRank_le_map (by norm_num)
          H.subtype H.subtype_injective Y')
      have hYnormM : Subgroup.normalizer (Y : Set G) ≤ D.M :=
        (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hYleP hYrank').trans hGammaM
      have h1 : (Subgroup.normalizer (Y : Set G)).subgroupOf H ≤
          (Subgroup.normalizer (X : Set G)).subgroupOf H := by
        intro z hz
        rw [Subgroup.mem_subgroupOf] at hz ⊢
        exact hXnormK' ⟨z.2, hYnormM hz⟩
      have hNY' : Subgroup.normalizer (Y' : Set ↥H) =
          (Subgroup.normalizer (Y : Set G)).subgroupOf H := by
        have hcomap : (Y'.map H.subtype).subgroupOf H = Y' :=
          Subgroup.comap_map_eq_self_of_injective (f := H.subtype) H.subtype_injective Y'
        rw [hY, Subgroup.subgroupOf_normalizer_eq (Subgroup.map_subtype_le Y'), hcomap]
      rw [hNY', ← Subgroup.subgroupOf_normalizer_eq hXH]
      exact h1
    have hstrong : ∀ a ∈ (Q ⊓ X).subgroupOf H, ∀ g : ↥H,
        g⁻¹ * a * g ∈ Subgroup.normalizer ((Q ⊓ X).subgroupOf H : Set ↥H) →
          g⁻¹ * a * g ∈ (Q ⊓ X).subgroupOf H := by
      intro a' ha' g' hg'
      have haG : (a' : G) ∈ Q ⊓ X := by
        rw [Subgroup.mem_subgroupOf] at ha'
        exact ha'
      have hbG : (g' : G)⁻¹ * (a' : G) * (g' : G) ∈
          Subgroup.normalizer (Q ⊓ X : Set G) := by
        rw [← Subgroup.subgroupOf_normalizer_eq hP'H, Subgroup.mem_subgroupOf] at hg'
        exact hg'
      have hres := hstrongG (a' : G) haG (g' : G) g'.2 hbG
      rwa [Subgroup.mem_subgroupOf]
    have hN := hK335 ↥H hKGroup hHrank' (X.subgroupOf H) ((Q ⊓ X).subgroupOf H)
      hLie hP'sylow hGamma hstrong
    have hXnormalH : (X.subgroupOf H).Normal := Subgroup.normalizer_eq_top_iff.mp hN
    have hHnormX : H ≤ Subgroup.normalizer (X : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mp hXnormalH
    obtain ⟨K, hKcomp, hXK, hKnotM⟩ := h875 L X H hmin
    have hXnormalK : (X.subgroupOf K).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hXK]
      exact (hKcomp.1).trans hHnormX
    have hKcomp' : CFSG.IsComponent (K.subgroupOf H) :=
      (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hKcomp.1).1
        (CFSG.Assembly.isComponentOf_iff_open.mpr hKcomp)
    have hXHnormal' : (X.subgroupOf H).Normal := hXnormalH
    have hXeqK : X = K := by
      have hKcH : CFSG.IsComponent (K.subgroupOf H : Subgroup ↥H) := hKcomp'
      have hXHnH : (X.subgroupOf H : Subgroup ↥H).Normal := hXHnormal'
      have hdisj : K.subgroupOf H ≤ X.subgroupOf H ∨
          ⁅K.subgroupOf H, X.subgroupOf H⁆ = ⊥ :=
        CFSG.LocalCores.component_normal_subgroup hKcH hXHnH
      rcases hdisj with hle | hcom
      · have h : K ≤ X := by
          have h1 := Subgroup.map_mono (f := H.subtype) hle
          rwa [Subgroup.map_subgroupOf_eq_of_le hKcomp.1,
            Subgroup.map_subgroupOf_eq_of_le hXH] at h1
        exact le_antisymm hXK h
      · exfalso
        have hmap : (⁅K.subgroupOf H, X.subgroupOf H⁆).map H.subtype = ⁅K, X⁆ := by
          rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKcomp.1,
            Subgroup.map_subgroupOf_eq_of_le hXH]
        have hcommKX : ⁅K, X⁆ = ⊥ := by rw [← hmap, hcom, Subgroup.map_bot]
        have hcommXX : ⁅X, X⁆ = ⊥ :=
          le_bot_iff.mp ((Subgroup.commutator_mono hXK le_rfl).trans hcommKX.le)
        have hperfX : ⁅X, X⁆ = X := by
          have h1 : ((⊤ : Subgroup ↥X)).map X.subtype = X := by
            rw [← Subgroup.subgroupOf_self X]
            exact Subgroup.map_subgroupOf_eq_of_le le_rfl
          have h2 : ((⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆)).map X.subtype = ⁅X, X⁆ := by
            rw [Subgroup.map_commutator, h1]
          have h3 : (⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆) = (⊤ : Subgroup ↥X) := hq.1
          rw [h3, h1] at h2
          exact h2.symm
        rw [hperfX] at hcommXX
        have hnt := CFSG.LocalCores.isQuasisimple_nontrivial
          ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥X).mp hq)
        have hsub : Subsingleton ↥X := by
          rw [hcommXX]
          infer_instance
        exact (not_subsingleton_iff_nontrivial.mpr hnt) hsub
    have hLleM : L ≤ D.M := hmin.hyp.1.elim (fun hL => CFSG.Open.IsSubnormal.le hL.1)
      (fun h => h.1)
    exact hKnotM (hXeqK ▸ (hmin.hyp.2.1.trans hLleM))
  ·
    exact CFSG.Blueprint.LieModel.of_quotient_center hZ hSU3.2

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
