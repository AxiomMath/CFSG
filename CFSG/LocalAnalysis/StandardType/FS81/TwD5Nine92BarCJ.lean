module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Bar
public import CFSG.ThirdParty.BrauerInduction.Background.Group.PDecomposition
public import CFSG.Mathlib.GroupTheory.SylowConj
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.Holt.H78.Prelim
import CFSG.ClassicalInvolution.SmallCases.Hat2A7Embed

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem

attribute [local instance] gLAPPrimeCoreOf_normal

theorem nineJ_inf_primeCoreCentralizerBTwo_eq_bot {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) :
    nineJ K (B.b 2) ⊓ primeCoreCentralizerBTwo (B.b 2) = ⊥ := by
  let J : Subgroup G := nineJ K (B.b 2)
  let H : Subgroup G := centralizerBTwo (B.b 2)
  let O : Subgroup G := primeCoreCentralizerBTwo (B.b 2)
  have hJH : J ≤ H := (Subgroup.commutator_le_self _).trans inf_le_right
  have hOH : O ≤ H := Subgroup.map_subtype_le _
  have hOn : (O.subgroupOf H).Normal := gLAPPrimeCoreOf_normal 3 H
  have hHnorm : H ≤ Subgroup.normalizer (O : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOH).mp hOn
  have hJnormO : J ≤ Subgroup.normalizer (O : Set G) := hJH.trans hHnorm
  have hJnormJ : J ≤ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer
  have hOJ : (O.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer_inf (H := O) (K := J)).mpr
      fun x hx => Subgroup.inf_normalizer_le_normalizer_inf (H := O) (K := J)
        ⟨hJnormO hx, hJnormJ hx⟩
  have hsimple : IsSimpleGroup ↥J := nineJ_simple_of_recOutTwD5 hstd hB hrec
  rcases hsimple.eq_bot_or_eq_top_of_normal (O.subgroupOf J) with hbot | htop
  · rw [eq_bot_iff]
    intro x hx
    have hxJ : (⟨x, (Subgroup.mem_inf.mp hx).1⟩ : ↥J) ∈ O.subgroupOf J :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp hx).2
    rw [hbot] at hxJ
    exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hxJ)
  · exfalso
    have hJO : J ≤ O := fun x hx => by
      have hxJ : (⟨x, hx⟩ : ↥J) ∈ O.subgroupOf J := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hxJ
    have h3J : 3 ∣ Nat.card ↥J := three_dvd_card_nineJ hstd hB hrec
    have hcopO : Nat.Coprime 3 (Nat.card O) := by
      change Nat.Coprime 3 (Nat.card ↥((pPrimeCore 3 ↥H).map H.subtype))
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact coprime_card_pPrimeCore 3 ↥H
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcopO
      (h3J.trans (Subgroup.card_dvd_of_le hJO))

theorem exists_isPSingular_mem_zpowers_of_map_eq {G : Type} [Group G] [Finite G]
    {b₂ : G} {y0 : ↥(centralizerBTwo b₂)} {ybar : barCentralizerBTwo b₂}
    (hy0q : twD5BarMap b₂ y0 = ybar) {m : ℕ} (hm : ybar ^ 3 ^ m = 1) :
    ∃ y : ↥(centralizerBTwo b₂), y ∈ Subgroup.zpowers y0 ∧
      twD5BarMap b₂ y = ybar ∧ IsPSingular 3 (y : G) := by
  classical
  have hmbar : IsPSingular 3 ybar := by
    obtain ⟨k, -, hk⟩ :=
      (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hm)
    exact ⟨k, hk⟩
  have hsing : IsPSingular 3 (twD5BarMap b₂ (Group.pSingular 3 y0)) :=
    IsPSingular.map (p := 3) (f := twD5BarMap b₂)
      (Group.isPSingular_pSingular 3 y0)
  have hreg : IsPRegular 3 (twD5BarMap b₂ (Group.pRegular 3 y0)) :=
    (Group.isPRegular_pRegular (p := 3) (isOfFinOrder_of_finite y0)).order_coprime
      |>.coprime_dvd_left (orderOf_map_dvd (twD5BarMap b₂) (Group.pRegular 3 y0))
  have h1 : twD5BarMap b₂ (Group.pSingular 3 y0) *
      twD5BarMap b₂ (Group.pRegular 3 y0) = ybar := by
    rw [← map_mul, (Group.pDecomp_commute 3 y0).eq,
      Group.pDecomp' (p := 3) (isOfFinOrder_of_finite y0), hy0q]
  have h2 : twD5BarMap b₂ (Group.pRegular 3 y0) *
      twD5BarMap b₂ (Group.pSingular 3 y0) = ybar := by
    rw [← map_mul, Group.pDecomp' (p := 3) (isOfFinOrder_of_finite y0), hy0q]
  obtain ⟨-, hreg_eq⟩ := Group.pSingular_pRegular_unique (p := 3)
    (isOfFinOrder_of_finite ybar) h1 h2 hsing hreg
  have hreg_one : twD5BarMap b₂ (Group.pRegular 3 y0) = 1 := by
    rw [hreg_eq]
    exact Group.isPSingular_pRegular_eq_one (p := 3) (isOfFinOrder_of_finite ybar) hmbar
  let y : ↥(centralizerBTwo b₂) := Group.pSingular 3 y0
  have hyq : twD5BarMap b₂ y = ybar := by
    calc twD5BarMap b₂ y
        = twD5BarMap b₂ (Group.pSingular 3 y0) *
            twD5BarMap b₂ (Group.pRegular 3 y0) := by rw [hreg_one, mul_one]
      _ = twD5BarMap b₂ (Group.pSingular 3 y0 * Group.pRegular 3 y0) := by rw [map_mul]
      _ = twD5BarMap b₂ y0 := by
            rw [(Group.pDecomp_commute 3 y0).eq,
              Group.pDecomp' (p := 3) (isOfFinOrder_of_finite y0)]
      _ = ybar := hy0q
  have hzy : y ∈ Subgroup.zpowers y0 := by
    change Group.pSingular 3 y0 ∈ Subgroup.zpowers y0
    unfold Group.pSingular
    exact Subgroup.zpow_mem_zpowers y0 _
  obtain ⟨n, hn⟩ := Group.isPSingular_pSingular (p := 3) y0
  exact ⟨y, hzy, hyq, ⟨n, by rw [Subgroup.orderOf_coe, hn]⟩⟩

theorem exists_isPSingular_of_mem_centralizer_bar {G : Type} [Group G] [Finite G]
    {b₀ b₂ : G} (hb0 : b₀ ∈ centralizerBTwo b₂) (hb0ord : orderOf b₀ = 3)
    {ybar : barCentralizerBTwo b₂}
    (hybar : ybar ∈ Subgroup.centralizer
      ({twD5BarBZero b₂ b₀ hb0} : Set (barCentralizerBTwo b₂)))
    {m : ℕ} (hm : ybar ^ 3 ^ m = 1) :
    ∃ y : ↥(centralizerBTwo b₂),
      y ∈ Subgroup.centralizer
        (Subgroup.zpowers (⟨b₀, hb0⟩ : ↥(centralizerBTwo b₂)) : Set _) ∧
      twD5BarMap b₂ y = ybar ∧ IsPSingular 3 (y : G) := by
  classical
  let H : Subgroup G := centralizerBTwo b₂
  let O : Subgroup G := primeCoreCentralizerBTwo b₂
  let N : Subgroup ↥H := O.subgroupOf H
  let Y : Subgroup ↥H := Subgroup.zpowers ⟨b₀, hb0⟩
  have hOH : O ≤ H := Subgroup.map_subtype_le _
  have hcopO : Nat.Coprime 3 (Nat.card O) := by
    change Nat.Coprime 3 (Nat.card ↥((pPrimeCore 3 ↥H).map H.subtype))
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact coprime_card_pPrimeCore 3 ↥H
  have hcardN : Nat.card ↥N = Nat.card O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOH).toEquiv
  have hcardY : Nat.card ↥Y = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hb0ord]
  have hN3 : ¬ 3 ∣ Nat.card ↥N := by
    rw [hcardN]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcopO
  have hY3 : IsPGroup 3 ↥Y := IsPGroup.of_card (n := 1) (by rw [hcardY, pow_one])
  have hcent := (CFSG.Holt.H78.lemma_1_8_centralizer N hN3 hY3).symm
  have hYmap : Y.map (twD5BarMap b₂) =
      Subgroup.zpowers (twD5BarBZero b₂ b₀ hb0) := by
    rw [MonoidHom.map_zpowers]
  have hcentbar : Subgroup.centralizer
      ({twD5BarBZero b₂ b₀ hb0} : Set (barCentralizerBTwo b₂)) =
      Subgroup.centralizer
        (Subgroup.zpowers (twD5BarBZero b₂ b₀ hb0) : Set _) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hy1 : ybar ∈ (Subgroup.centralizer (Y : Set ↥H)).map (twD5BarMap b₂) := by
    rw [← hcent, hYmap, ← hcentbar]
    exact hybar
  obtain ⟨y0, hy0C, hy0q⟩ := Subgroup.mem_map.mp hy1
  obtain ⟨y, hzy, hyq, hysing⟩ := exists_isPSingular_mem_zpowers_of_map_eq hy0q hm
  exact ⟨y, (Subgroup.zpowers_le.mpr hy0C) hzy, hyq, hysing⟩

abbrev twD5BarNineJ {G : Type} [Group G] (b₂ : G) (K : Subgroup G) :
    Subgroup (barCentralizerBTwo b₂) :=
  twD5BarSub b₂ ((nineJ K b₂).subgroupOf (centralizerBTwo b₂))

theorem mem_centralizer_twD5BarNineJ_of_mul_eq {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E)
    {y : ↥(centralizerBTwo (B.b 2))} {d b2i j : G}
    (hy : (y : G) = d * (b2i * j)) (hb2i : b2i ∈ Subgroup.zpowers (B.b 2))
    (hjH : j ∈ centralizerBTwo (B.b 2))
    (hd : d ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G))
    (hybarJ : twD5BarMap (B.b 2) y ∈ Subgroup.centralizer
      (twD5BarNineJ (B.b 2) K : Set (barCentralizerBTwo (B.b 2)))) :
    twD5BarMap (B.b 2) ⟨j, hjH⟩ ∈ Subgroup.centralizer
      (twD5BarNineJ (B.b 2) K : Set (barCentralizerBTwo (B.b 2))) := by
  classical
  let H : Subgroup G := centralizerBTwo (B.b 2)
  let J : Subgroup G := nineJ K (B.b 2)
  let Jbar : Subgroup (barCentralizerBTwo (B.b 2)) := twD5BarNineJ (B.b 2) K
  have hJH : J ≤ H := (Subgroup.commutator_le_self _).trans inf_le_right
  have hb2K : B.b 2 ∈ K := hB.2.2 2 (by decide)
  have hb2iK : b2i ∈ K := (Subgroup.zpowers_le.mpr hb2K) hb2i
  have hb2H : B.b 2 ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hdH : d ∈ H := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hd.2 (B.b 2) hb2K).symm
  have hb2iH : b2i ∈ H := (Subgroup.zpowers_le.mpr hb2H) hb2i
  have hdJ : twD5BarMap (B.b 2) ⟨d, hdH⟩ ∈
      Subgroup.centralizer (Jbar : Set (barCentralizerBTwo (B.b 2))) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    have hxJ : (x : G) ∈ J := Subgroup.mem_subgroupOf.mp hx
    have hxK : (x : G) ∈ K := (Subgroup.commutator_le_self _).trans inf_le_left hxJ
    have hdx : (⟨d, hdH⟩ : ↥H) * x = x * ⟨d, hdH⟩ :=
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hd.2 (x : G) hxK).symm
    rw [← map_mul, ← map_mul, hdx]
  have hb2iJ : twD5BarMap (B.b 2) ⟨b2i, hb2iH⟩ ∈
      Subgroup.centralizer (Jbar : Set (barCentralizerBTwo (B.b 2))) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    have hxJ : (x : G) ∈ J := Subgroup.mem_subgroupOf.mp hx
    have hcomm : Commute (⟨b2i, hb2iH⟩ : ↥H) x := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb2i
      have hcx : Commute (B.b 2) (x : G) :=
        (Subgroup.mem_centralizer_singleton_iff.mp x.2).symm
      exact Subtype.ext (hcx.zpow_left i).eq
    rw [← map_mul, ← map_mul, hcomm.eq]
  have hqdc : twD5BarMap (B.b 2) (⟨d, hdH⟩ * ⟨b2i, hb2iH⟩) ∈
      Subgroup.centralizer (Jbar : Set (barCentralizerBTwo (B.b 2))) :=
    (Subgroup.centralizer (Jbar : Set (barCentralizerBTwo (B.b 2)))).mul_mem hdJ hb2iJ
  have hyH : y = (⟨d, hdH⟩ : ↥H) * (⟨b2i, hb2iH⟩ * ⟨j, hjH⟩) := by
    apply Subtype.ext
    simpa [mul_assoc] using hy
  have hqj_eq : twD5BarMap (B.b 2) ⟨j, hjH⟩ =
      (twD5BarMap (B.b 2) (⟨d, hdH⟩ * ⟨b2i, hb2iH⟩))⁻¹ * twD5BarMap (B.b 2) y := by
    rw [hyH, map_mul, map_mul, map_mul]
    group
  rw [hqj_eq]
  exact (Subgroup.centralizer (Jbar : Set (barCentralizerBTwo (B.b 2)))).mul_mem
    ((Subgroup.centralizer (Jbar : Set (barCentralizerBTwo (B.b 2)))).inv_mem hqdc) hybarJ

theorem eq_one_of_mem_nineJ_of_mem_centralizer_twD5BarNineJ {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) {j : G}
    (hjH : j ∈ centralizerBTwo (B.b 2)) (hjJ : j ∈ nineJ K (B.b 2))
    (hjbar : twD5BarMap (B.b 2) ⟨j, hjH⟩ ∈ Subgroup.centralizer
      (twD5BarNineJ (B.b 2) K : Set (barCentralizerBTwo (B.b 2)))) :
    j = 1 := by
  classical
  let H : Subgroup G := centralizerBTwo (B.b 2)
  let O : Subgroup G := primeCoreCentralizerBTwo (B.b 2)
  let J : Subgroup G := nineJ K (B.b 2)
  let Jbar : Subgroup (barCentralizerBTwo (B.b 2)) := twD5BarNineJ (B.b 2) K
  have hJH : J ≤ H := (Subgroup.commutator_le_self _).trans inf_le_right
  have hJO : J ⊓ O = ⊥ := nineJ_inf_primeCoreCentralizerBTwo_eq_bot hstd hB hrec
  have hcenter : (⟨j, hjJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    change (x : G) * j = j * (x : G)
    have hxH : (x : G) ∈ H := hJH x.2
    let z : ↥H := ⟨j, hjH⟩ * ⟨(x : G), hxH⟩ * ⟨j, hjH⟩⁻¹ * ⟨(x : G), hxH⟩⁻¹
    have hxbar : twD5BarMap (B.b 2) ⟨(x : G), hxH⟩ ∈ Jbar :=
      Subgroup.mem_map.mpr ⟨⟨(x : G), hxH⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hjbar _ hxbar
    have hq1 : twD5BarMap (B.b 2) z = 1 := by
      change twD5BarMap (B.b 2) (⟨j, hjH⟩ * ⟨(x : G), hxH⟩ * ⟨j, hjH⟩⁻¹ *
        ⟨(x : G), hxH⟩⁻¹) = 1
      simp only [map_mul, map_inv]
      rw [← hcomm]
      group
    have hmemO : (z : G) ∈ O :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hq1)
    have hmemJ : (z : G) ∈ J := by
      change j * (x : G) * j⁻¹ * (x : G)⁻¹ ∈ J
      exact J.mul_mem (J.mul_mem (J.mul_mem hjJ x.2) (J.inv_mem hjJ)) (J.inv_mem x.2)
    have hz1 : (z : G) = 1 := by
      have hmem := Subgroup.mem_inf.mpr ⟨hmemJ, hmemO⟩
      exact Subgroup.mem_bot.mp (by rwa [hJO] at hmem)
    have h1' : (j : G) * (x : G) * (j : G)⁻¹ = (x : G) := by
      have hz' : (j : G) * (x : G) * (j : G)⁻¹ * (x : G)⁻¹ = 1 := hz1
      exact mul_inv_eq_one.mp hz'
    have h2 : (j : G) * (x : G) = (x : G) * j := by
      calc (j : G) * (x : G) = (j * (x : G) * (j : G)⁻¹) * (j : G) := by group
        _ = (x : G) * (j : G) := by rw [h1']
    exact h2.symm
  have hmem : (⟨j, hjJ⟩ : ↥J) ∈ (⊥ : Subgroup ↥J) := by
    rw [← center_nineJ_eq_bot hstd hB hrec]
    exact hcenter
  exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hmem)

theorem mem_zpowers_of_eq_mul_mem_zpowers_of_isPSingular {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) (hfus : Fus42 B b₀)
    {y d b2i : G} (hy : y = d * b2i) (hyH : y ∈ centralizerBTwo (B.b 2))
    (hb2i : b2i ∈ Subgroup.zpowers (B.b 2)) (hysing : IsPSingular 3 y)
    (hd : d ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G)) :
    d ∈ Subgroup.zpowers b₀ := by
  have hb2i_dvd : orderOf b2i ∣ 3 := by
    have h := orderOf_dvd_of_mem_zpowers hb2i
    rwa [B.ord 2] at h
  have hcomm_y_b2i : Commute y b2i := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb2i
    have hcomm : Commute y (B.b 2) := Subgroup.mem_centralizer_singleton_iff.mp hyH
    exact hcomm.zpow_right i
  obtain ⟨n, hn⟩ := hysing
  have hdvd : orderOf d ∣ 3 ^ (n + 1) := by
    have hd_eq : d = y * b2i⁻¹ := by rw [hy]; group
    have h := hcomm_y_b2i.inv_right.orderOf_mul_dvd_mul_orderOf
    rw [orderOf_inv, hn] at h
    rw [hd_eq, pow_succ]
    exact h.trans (mul_dvd_mul_left (3 ^ n) hb2i_dvd)
  obtain ⟨q, -, hq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  exact mem_zpowers_of_mem_inf_centralizer_of_pow_eq_one hstd hB hrec hfus hd (by
    show d ^ 3 ^ q = 1
    rw [← hq]
    exact pow_orderOf_eq_one d)

theorem twD5Bar_centralizer_inf_centralizer_le_zpowers_sup {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀) (hfus : Fus42 B b₀)
    (hb0 : b₀ ∈ centralizerBTwo (B.b 2)) :
    ∀ ybar ∈ Subgroup.centralizer
        ({twD5BarBZero (B.b 2) b₀ hb0} : Set (barCentralizerBTwo (B.b 2))),
      ybar ∈ Subgroup.centralizer
        (twD5BarNineJ (B.b 2) K : Set (barCentralizerBTwo (B.b 2))) →
      ∀ m : ℕ, ybar ^ 3 ^ m = 1 →
      ybar ∈ Subgroup.zpowers (twD5BarBZero (B.b 2) b₀ hb0) ⊔
        Subgroup.zpowers (twD5BarBTwo (B.b 2)) := by
  intro ybar hybar hybarJ m hm
  classical
  let H : Subgroup G := centralizerBTwo (B.b 2)
  let J : Subgroup G := nineJ K (B.b 2)
  let S : Subgroup G := Subgroup.zpowers b₀ ⊔ Subgroup.zpowers (B.b 2)
  have hb2H : B.b 2 ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hJH : J ≤ H := (Subgroup.commutator_le_self _).trans inf_le_right
  obtain ⟨y, hyC, hyq, hysing⟩ :=
    exists_isPSingular_of_mem_centralizer_bar hb0 hstd.2.1.1 hybar hm
  have hyC0 : (y : G) ∈ Subgroup.centralizer ({b₀} : Set G) := by
    have h := Subgroup.mem_centralizer_iff.mp hyC ⟨b₀, hb0⟩ (Subgroup.mem_zpowers _)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      simpa using (congrArg Subtype.val h).symm)
  obtain ⟨d, hd, k, hk, hydec⟩ :=
    exists_mul_eq_of_mem_centralizer_inf_centralizer hstd hB hrec ⟨hyC0, y.2⟩
  have hKJ : k ∈ Subgroup.zpowers (B.b 2) ⊔ J := by
    rw [← inf_centralizer_eq_zpowers_sup_nineJ hstd hB hrec]
    exact hk
  have hcommBJ : ∀ a ∈ Subgroup.zpowers (B.b 2), ∀ b ∈ J, Commute a b := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hcomm : Commute (B.b 2) b :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hJH hb)).symm
    exact hcomm.zpow_left i
  obtain ⟨b2i, hb2i, j, hjJ, hk_eq⟩ := (CFSG.mem_sup_of_commute hcommBJ).mp hKJ
  have hjH : j ∈ H := hJH hjJ
  have hy_dec : (y : G) = d * (b2i * j) := by rw [hydec, hk_eq]
  have hybarJ' : twD5BarMap (B.b 2) y ∈ Subgroup.centralizer
      (twD5BarNineJ (B.b 2) K : Set _) := by rwa [hyq]
  have hqj := mem_centralizer_twD5BarNineJ_of_mul_eq hB hy_dec hb2i hjH hd hybarJ'
  have hj1 : j = 1 :=
    eq_one_of_mem_nineJ_of_mem_centralizer_twD5BarNineJ hstd hB hrec hjH hjJ hqj
  have hk_b2i : k = b2i := by rw [← hk_eq, hj1, mul_one]
  have hy_db2i : (y : G) = d * b2i := by rw [hydec, hk_b2i]
  have hdzp : d ∈ Subgroup.zpowers b₀ :=
    mem_zpowers_of_eq_mul_mem_zpowers_of_isPSingular hstd hB hrec hfus
      hy_db2i y.2 hb2i hysing hd
  have hyS : (y : G) ∈ S := by
    rw [hy_db2i]
    exact Subgroup.mul_mem_sup hdzp hb2i
  have hmem : ybar ∈ (S.subgroupOf H).map (twD5BarMap (B.b 2)) :=
    Subgroup.mem_map.mpr ⟨⟨(y : G), y.2⟩, Subgroup.mem_subgroupOf.mpr hyS, hyq⟩
  rwa [map_subgroupOf_zpowers_sup_eq hb0 hb2H] at hmem

end CFSG.StandardType.FrameRoute.FS81

end
