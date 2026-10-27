module

public import CFSG.RankThree.OddKernel.ComponentRanks
public import CFSG.RankThree.OddKernel.RankOneQuotients
public import CFSG.RankThree.CentralLift.EvenCenterTrivial

public section

namespace CFSG.RankThree.OddKernel

open Subgroup CFSG.SectionRank CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (localRank)
open scoped Pointwise

universe u

section ComponentModels

variable {p : ℕ}

theorem card_inf_le_pow_pRank (hp : p.Prime) {G : Type*} [Group G] [Finite G] {B : Subgroup G}
    (hB : CFSG.Open.IsElemAbelian p B) (N : Subgroup G) :
    Nat.card (B ⊓ N : Subgroup G) ≤ p ^ pRank p N := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := ((IsPGroup.of_card (n := 0) (by simp) : IsPGroup p (⊥ : Subgroup G)) |>
    fun _ => (show IsPGroup p (B ⊓ N : Subgroup G) from fun x =>
      ⟨1, by rw [pow_one]; exact Subtype.ext (hB.2 x x.2.1)⟩)).exists_card_eq
  have hE : CFSG.Open.IsElemAbelian p ((B ⊓ N).subgroupOf N) := by
    have h1 := isElemAbelian_inf_left hB N
    have := h1.1
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext (h1.2 _ hx)⟩
    change ((a : N) : G) * ((b : N) : G) = ((b : N) : G) * ((a : N) : G)
    exact congrArg Subtype.val (mul_comm' (⟨a, a.2⟩ : (B ⊓ N : Subgroup G)) ⟨b, b.2⟩)
  have hcard : Nat.card ((B ⊓ N).subgroupOf N) = p ^ k := by
    rw [← hk]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
  have h := CFSG.SectionRank.le_pRank hp.one_lt le_top hE hcard
  rw [← pRank_eq_open_pRank_top] at h
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos h

theorem pRank_le_add_of_normal (hp : p.Prime) {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    [N.Normal] : pRank p G ≤ pRank p N + pRank p (G ⧸ N) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [pRank_eq_open_pRank_top]
  refine CFSG.SectionRank.pRank_le hp.one_lt fun B _ hB => ?_
  have hcard := CFSG.RankThree.SubgroupLists.card_eq_card_map_mul_card_inf_ker
    (QuotientGroup.mk' N) B
  rw [QuotientGroup.ker_mk'] at hcard
  have h1 := card_inf_le_pow_pRank hp hB N
  have h2 : Nat.card (B.map (QuotientGroup.mk' N)) ≤ p ^ pRank p (G ⧸ N) := by
    obtain ⟨k, hk⟩ := (show IsPGroup p (B.map (QuotientGroup.mk' N)) from
      (show IsPGroup p B from fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hB.2 x x.2)⟩).map
        _).exists_card_eq
    have h := CFSG.SectionRank.le_pRank hp.one_lt le_top
      (CFSG.SectionRank.isElemAbelian_map hB (QuotientGroup.mk' N)) hk
    rw [← pRank_eq_open_pRank_top] at h
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos h
  rw [hcard, pow_add, mul_comm]
  exact Nat.mul_le_mul h1 h2

theorem add_le_pRank_of_commute (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    {E₁ E₂ H : Subgroup G} (hE₁ : CFSG.Open.IsElemAbelian p E₁)
    (hE₂ : CFSG.Open.IsElemAbelian p E₂) {r₁ r₂ : ℕ} (h₁ : Nat.card E₁ = p ^ r₁)
    (h₂ : Nat.card E₂ = p ^ r₂) (hc : ∀ x ∈ E₁, ∀ y ∈ E₂, Commute x y) (hdisj : E₁ ⊓ E₂ = ⊥)
    (h₁H : E₁ ≤ H) (h₂H : E₂ ≤ H) : r₁ + r₂ ≤ CFSG.Open.pRank p H := by
  let f : E₁ × E₂ →* G := MonoidHom.noncommCoprod E₁.subtype E₂.subtype
    (fun x y => hc x x.2 y y.2)
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    have h : (x : G) * y = 1 := hxy
    have hx : (x : G) ∈ E₁ ⊓ E₂ := Subgroup.mem_inf.2 ⟨x.2, by
      rw [eq_inv_of_mul_eq_one_left h]
      exact E₂.inv_mem y.2⟩
    rw [hdisj, mem_bot] at hx
    have hy : (y : G) = 1 := by rw [hx, one_mul] at h; exact h
    rw [mem_bot, Prod.mk_eq_one]
    exact ⟨Subtype.ext hx, Subtype.ext hy⟩
  have hc₁ := hE₁.1
  have hc₂ := hE₂.1
  refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt (A := E₁ × E₂) ?_ ?_ ?_ f hf ?_
  · rintro ⟨a, b⟩ ⟨c, d⟩
    exact Prod.ext (mul_comm' a c) (mul_comm' b d)
  · rintro ⟨a, b⟩
    exact Prod.ext (Subtype.ext (hE₁.2 a a.2)) (Subtype.ext (hE₂.2 b b.2))
  · rw [Nat.card_prod, h₁, h₂, pow_add]
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    exact H.mul_mem (h₁H a.2) (h₂H b.2)

theorem succ_le_localRank_of_commute (hp : p.Prime) {Y : Type*} [Group Y] [Finite Y]
    {T E : Subgroup Y} (hT0 : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hE : CFSG.Open.IsElemAbelian p E)
    {r : ℕ} (hEcard : Nat.card E = p ^ r) (hET : E ≤ normalizer (T : Set Y)) {b : Y}
    (hbc : ∀ e ∈ E, Commute e b) (hbp : b ^ p = 1) (hbE : b ∉ E)
    (hbT : b ∈ normalizer (T : Set Y)) : r + 1 ≤ localRank p Y :=
  (succ_le_pRank_of_commute hp hE hEcard hbc hbp hbE hET hbT).trans
    (CFSG.RankThree.Classical.pRank_le_localRank hp.one_lt ⟨T, hT0, hT2, rfl⟩)

theorem le_normalizer_of_le_centralizer {Y : Type*} [Group Y] {T E : Subgroup Y}
    (h : E ≤ centralizer (T : Set Y)) : E ≤ normalizer (T : Set Y) :=
  h.trans (centralizer_le_normalizer _)

theorem two_components_facts {Y : Type*} [Group Y] [Finite Y] (hE : CFSG.layer Y = ⊤)
    {K₁ K₂ : Subgroup Y} (hK₁ : CFSG.IsComponent K₁) (hK₂ : CFSG.IsComponent K₂) (hne : K₁ ≠ K₂)
    (hall : ∀ K : Subgroup Y, CFSG.IsComponent K → K = K₁ ∨ K = K₂) :
    K₁ ≤ centralizer (K₂ : Set Y) ∧ K₂ ≤ centralizer (K₁ : Set Y) ∧ K₁ ⊔ K₂ = ⊤ ∧
      K₁.Normal ∧ K₂.Normal ∧
      center Y = (center K₁).map K₁.subtype ⊔ (center K₂).map K₂.subtype ∧
      K₁ ⊓ K₂ = (center K₁).map K₁.subtype ⊓ (center K₂).map K₂.subtype := by
  have h12 := le_centralizer_of_components hK₁ hK₂ hne
  have h21 := le_centralizer_of_components hK₂ hK₁ (Ne.symm hne)
  have hsup : K₁ ⊔ K₂ = ⊤ := by
    rw [eq_top_iff, ← hE]
    refine sSup_le fun K hK => ?_
    rcases hall K hK with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  refine ⟨h12, h21, hsup, component_normal_of_layer_eq_top hE hK₁,
    component_normal_of_layer_eq_top hE hK₂, ?_, ?_⟩
  · rw [center_eq_iSup_of_layer_eq_top hE]
    refine le_antisymm (iSup_le fun K => ?_) (sup_le (le_iSup (fun K : ComponentIndex Y =>
      (center K.1).map K.1.subtype) ⟨K₁, hK₁⟩) (le_iSup (fun K : ComponentIndex Y =>
      (center K.1).map K.1.subtype) ⟨K₂, hK₂⟩))
    rcases hall K.1 K.2 with h | h
    · obtain ⟨K, hK⟩ := K
      subst h
      exact le_sup_left
    · obtain ⟨K, hK⟩ := K
      subst h
      exact le_sup_right
  · refine le_antisymm (fun x hx => ⟨(CFSG.LocalCores.mem_map_center_iff K₁).2 ⟨hx.1, h21 hx.2⟩,
      (CFSG.LocalCores.mem_map_center_iff K₂).2 ⟨hx.2, h12 hx.1⟩⟩) (inf_le_inf (map_subtype_le _)
      (map_subtype_le _))

theorem disjoint_components_ranks (hp : p.Prime) (hp2 : p ≠ 2) {Y : Type*} [Group Y] [Finite Y]
    (hE : CFSG.layer Y = ⊤) (hPp : IsPGroup p (center Y)) (hloc : localRank p Y ≤ 2)
    {K₁ K₂ : Subgroup Y} (hK₁ : CFSG.IsComponent K₁) (hK₂ : CFSG.IsComponent K₂)
    (hne : K₁ ≠ K₂) (hdisj : K₁ ⊓ K₂ = ⊥) (hZ₁ : center K₁ ≠ ⊥) (hK₁rank : pRank p K₁ = 2)
    (hpK₂ : p ∣ Nat.card K₂) :
    localRank p K₂ = 0 ∧ pRank p K₂ ≤ 1 ∧ localRank p K₁ ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h12 := le_centralizer_of_components hK₁ hK₂ hne
  have h21 := le_centralizer_of_components hK₂ hK₁ (Ne.symm hne)
  have hmem12 : ∀ x ∈ K₁, ∀ y ∈ K₂, Commute x y := fun x hx y hy =>
    (mem_centralizer_iff.1 (h12 hx) y hy).symm
  have hnot : ∀ x ∈ K₁, x ∈ K₂ → x = 1 := fun x h1 h2 => by
    have : x ∈ K₁ ⊓ K₂ := ⟨h1, h2⟩
    rwa [hdisj, mem_bot] at this
  have hr₁ : CFSG.Open.pRank p K₁ = 2 := by
    rw [pRank_eq_pRank_top_subgroup, ← pRank_eq_open_pRank_top]
    exact hK₁rank
  obtain ⟨E₀, hE₀K, hE₀, hE₀card⟩ := CFSG.SectionRank.exists_pRank hp.one_lt K₁
  rw [hr₁] at hE₀card
  refine ⟨Nat.eq_zero_of_le_zero (csSup_le' ?_), ?_, csSup_le' ?_⟩
  · rintro k ⟨M, ⟨T, hT0, hT2, rfl⟩, rfl⟩
    by_contra hpos
    push Not at hpos
    obtain ⟨E', hE'M, hE', hE'card⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
      (normalizer (T : Set K₂))
    obtain ⟨b, hbE', hb1⟩ : ∃ b ∈ E', b ≠ 1 := by
      by_contra hall
      push Not at hall
      have hbot : E' = ⊥ := eq_bot_iff.2 fun b hb => (mem_bot).2 (hall b hb)
      rw [hbot, card_bot] at hE'card
      have hpos' : 0 < CFSG.Open.pRank p (normalizer (T : Set K₂)) := hpos
      exact (Nat.one_lt_pow hpos'.ne' hp.one_lt).ne hE'card
    have hb1' : (b : Y) ≠ 1 := fun h => hb1 (Subtype.ext h)
    have hT'0 : T.map K₂.subtype ≠ ⊥ := fun h => hT0
      ((Subgroup.map_eq_bot_iff_of_injective _ K₂.subtype_injective).1 h)
    have h3 := succ_le_localRank_of_commute hp hT'0 (hT2.map _) hE₀ hE₀card
      (le_normalizer_of_le_centralizer (hE₀K.trans (h12.trans (centralizer_le
        (map_subtype_le T))))) (b := (b : Y)) (fun e he => hmem12 e (hE₀K he) b b.2)
      (by rw [← SubgroupClass.coe_pow, hE'.2 b hbE', OneMemClass.coe_one])
      (fun h => hb1' (hnot _ (hE₀K h) b.2))
      (le_normalizer_map K₂.subtype (mem_map_of_mem _ (hE'M hbE')))
    omega
  ·
    have hZp := isPGroup_center_component hE hPp hK₁
    have hdvd : p ∣ Nat.card (center K₁) := by
      rcases hZp.card_eq_or_dvd with h | h
      · exact absurd (card_eq_one.1 h) hZ₁
      · exact h
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
    obtain ⟨t, htK, ht⟩ := exists_involution_mem_component hp2 hE hPp hK₁
    have ht1 : t ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at ht
      exact absurd ht (by norm_num)
    have hT2 : IsPGroup 2 (zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
    have hT0 : zpowers t ≠ ⊥ := fun h => ht1 (by
      have : t ∈ zpowers t := mem_zpowers t
      rwa [h, mem_bot] at this)
    have hTK : zpowers t ≤ K₁ := zpowers_le.2 htK
    rw [pRank_eq_open_pRank_top, ← pRank_eq_pRank_top_subgroup]
    obtain ⟨F, hFK, hF, hFcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt K₂
    obtain ⟨z', hz'⟩ : ∃ z' : Y, z' = (((z : center K₁) : K₁) : Y) := ⟨_, rfl⟩
    have hz'K : z' ∈ K₁ := hz' ▸ ((z : center K₁) : K₁).2
    have hz'1 : z' ≠ 1 := by
      intro h
      rw [hz'] at h
      have h1 : z = 1 := Subtype.ext (Subtype.ext h)
      rw [h1, orderOf_one] at hz
      exact hp.one_lt.ne hz
    have hz'p : z' ^ p = 1 := by
      rw [hz', ← SubgroupClass.coe_pow, ← SubgroupClass.coe_pow, ← hz, pow_orderOf_eq_one]
      rfl
    have hz'c : z' ∈ centralizer (zpowers t : Set Y) := by
      rw [mem_centralizer_iff]
      rintro _ ⟨k, rfl⟩
      have hzc : (z : K₁) ∈ center K₁ := z.2
      have h1 : (⟨t, htK⟩ : K₁) * (z : K₁) = (z : K₁) * ⟨t, htK⟩ := mem_center_iff.1 hzc _
      have h2 : t * z' = z' * t := by rw [hz']; exact congrArg Subtype.val h1
      exact ((Commute.zpow_left (show Commute t z' from h2) k)).eq
    have h3 := succ_le_localRank_of_commute hp hT0 hT2 hF hFcard
      (le_normalizer_of_le_centralizer (hFK.trans (h21.trans (centralizer_le hTK))))
      (b := z') (fun f hf => (hmem12 z' hz'K f (hFK hf)).symm) hz'p
      (fun h => hz'1 (hnot _ hz'K (hFK h)))
      (centralizer_le_normalizer _ hz'c)
    omega
  ·
    rintro k ⟨M, ⟨T, hT0, hT2, rfl⟩, rfl⟩
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' p hpK₂
    have hb1' : (b : Y) ≠ 1 := by
      intro h
      have h1 : b = 1 := Subtype.ext h
      rw [h1, orderOf_one] at hb
      exact hp.one_lt.ne hb
    have hbp : (b : Y) ^ p = 1 := by
      rw [← SubgroupClass.coe_pow, ← hb, pow_orderOf_eq_one, OneMemClass.coe_one]
    obtain ⟨E', hE'M, hE', hE'card⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
      (normalizer (T : Set K₁))
    have hT'0 : T.map K₁.subtype ≠ ⊥ := fun h => hT0
      ((Subgroup.map_eq_bot_iff_of_injective _ K₁.subtype_injective).1 h)
    have hEm : CFSG.Open.IsElemAbelian p (E'.map K₁.subtype) := isElemAbelian_map hE' _
    have hEmcard : Nat.card (E'.map K₁.subtype) = p ^ CFSG.Open.pRank p
        (normalizer (T : Set K₁)) := by
      rw [card_map_of_injective K₁.subtype_injective, hE'card]
    have h3 := succ_le_localRank_of_commute hp hT'0 (hT2.map _) hEm hEmcard
      ((map_mono hE'M).trans (le_normalizer_map K₁.subtype)) (b := (b : Y))
      (fun e he => hmem12 e (map_subtype_le _ he) b b.2) hbp
      (fun h => hb1' (hnot _ (map_subtype_le _ h) b.2))
      (le_normalizer_of_le_centralizer (h21.trans (centralizer_le (map_subtype_le T))) b.2)
    change CFSG.Open.pRank p (normalizer (T : Set K₁)) ≤ 1
    omega

theorem card_le_pow_pRank_of_le (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    {B H : Subgroup G} (hB : CFSG.Open.IsElemAbelian p B) (hBH : B ≤ H) :
    Nat.card B ≤ p ^ CFSG.Open.pRank p H := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (show IsPGroup p B from fun x =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (hB.2 x x.2)⟩).exists_card_eq
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos (CFSG.SectionRank.le_pRank hp.one_lt hBH hB hk)

theorem disjoint_components_quotient_bounds (hp : p.Prime) (hp3 : 3 < p) {Y : Type*}
    [Group Y] [Finite Y] (hE : CFSG.layer Y = ⊤) (hPp : IsPGroup p (center Y))
    (hloc : localRank p Y ≤ 2) {K₁ K₂ : Subgroup Y} (hK₁ : CFSG.IsComponent K₁)
    (hK₂ : CFSG.IsComponent K₂) (hne : K₁ ≠ K₂)
    (hall : ∀ K : Subgroup Y, CFSG.IsComponent K → K = K₁ ∨ K = K₂) (hZ₁ : center K₁ ≠ ⊥)
    (hZ₂ : center K₂ = ⊥) (hK₁rank : pRank p K₁ = 2) (hpK₂ : p ∣ Nat.card K₂)
    (A : Subgroup Y) [A.Normal] (hAZ : A ≤ center Y) :
    pRank p (Y ⧸ A) ≤ pRank p Y ∧ localRank p (Y ⧸ A) ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨h12, h21, hsup, hn₁, hn₂, hcen, hinter⟩ := two_components_facts hE hK₁ hK₂ hne hall
  have hdisj : K₁ ⊓ K₂ = ⊥ := by
    rw [hinter, hZ₂, Subgroup.map_bot, inf_bot_eq]
  obtain ⟨hl₂, hr₂, hl₁⟩ :=
    disjoint_components_ranks hp hp2 hE hPp hloc hK₁ hK₂ hne hdisj hZ₁ hK₁rank hpK₂
  have hAK : A ≤ K₁ := by
    rw [hcen, hZ₂, Subgroup.map_bot, sup_bot_eq] at hAZ
    exact hAZ.trans (map_subtype_le _)
  have hJn : (K₁.map (QuotientGroup.mk' A)).Normal := hn₁.map _ (QuotientGroup.mk'_surjective A)
  let φ : K₁ →* K₁.map (QuotientGroup.mk' A) :=
    ((QuotientGroup.mk' A).domRestrict K₁).codRestrict _ fun x => mem_map_of_mem _ x.2
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨k, hk, rfl⟩ := mem_map.1 hy
    exact ⟨⟨k, hk⟩, rfl⟩
  have hφker : φ.ker = A.subgroupOf K₁ := by
    ext k
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      exact (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).2 h)
  have eJ : K₁ ⧸ A.subgroupOf K₁ ≃* K₁.map (QuotientGroup.mk' A) :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  have hAc : A.subgroupOf K₁ ≤ center K₁ := fun a ha => mem_center_iff.2 fun g =>
    Subtype.ext (mem_center_iff.1 (hAZ (mem_subgroupOf.1 ha)) g)
  have : Group.IsPerfect K₁ := hK₁.1.1
  have hJr : pRank p (K₁.map (QuotientGroup.mk' A)) ≤ 2 := by
    rw [pRank_eq_open_pRank_top, ← pRank_top_eq_of_mulEquiv hp.one_lt eJ,
      ← pRank_eq_open_pRank_top]
    exact perfect_rank_two_large_prime_quotient_pRank_le_two hp hp3 hK₁rank.le _ hAc
  have hJl : localRank p (K₁.map (QuotientGroup.mk' A)) ≤ 1 :=
    (CFSG.RankThree.CentralLift.localRank_le_of_mulEquiv eJ.symm hp).trans
      (odd_prime_two_local_rank_one_quotients hp hp2 _ hl₁)
  let ψ₂ : K₂ →* (Y ⧸ A) ⧸ K₁.map (QuotientGroup.mk' A) :=
    (QuotientGroup.mk' _).comp ((QuotientGroup.mk' A).comp K₂.subtype)
  have hψ₂s : Function.Surjective ψ₂ := by
    intro q
    obtain ⟨q', rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective A q'
    have hy : y ∈ ((K₁ ⊔ K₂ : Subgroup Y) : Set Y) := by rw [hsup]; exact Set.mem_univ y
    rw [mul_normal, Set.mem_mul] at hy
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hy
    refine ⟨⟨k₂, hk₂⟩, ?_⟩
    have h1 : QuotientGroup.mk' (K₁.map (QuotientGroup.mk' A)) (QuotientGroup.mk' A k₁) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (mem_map_of_mem _ hk₁)
    change _ = QuotientGroup.mk' _ (QuotientGroup.mk' A (k₁ * k₂))
    rw [map_mul, map_mul, h1, one_mul]
    rfl
  have hψ₂i : Function.Injective ψ₂ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    have h1 : QuotientGroup.mk' A (k : Y) ∈ K₁.map (QuotientGroup.mk' A) :=
      (QuotientGroup.eq_one_iff _).1 hk
    obtain ⟨k₁, hk₁, hk₁k⟩ := mem_map.1 h1
    have h2 : k₁⁻¹ * k ∈ A := QuotientGroup.eq.1 hk₁k
    have hkK : (k : Y) ∈ K₁ := by
      have : (k : Y) = k₁ * (k₁⁻¹ * k) := by group
      rw [this]
      exact K₁.mul_mem hk₁ (hAK h2)
    have : (k : Y) ∈ K₁ ⊓ K₂ := ⟨hkK, k.2⟩
    rw [hdisj, mem_bot] at this
    exact (mem_bot).2 (Subtype.ext this)
  let eQ : K₂ ≃* (Y ⧸ A) ⧸ K₁.map (QuotientGroup.mk' A) := MulEquiv.ofBijective ψ₂ ⟨hψ₂i, hψ₂s⟩
  have hQr : pRank p ((Y ⧸ A) ⧸ K₁.map (QuotientGroup.mk' A)) ≤ 1 := by
    rw [pRank_eq_open_pRank_top, ← pRank_top_eq_of_mulEquiv hp.one_lt eQ,
      ← pRank_eq_open_pRank_top]
    exact hr₂
  have hQl : localRank p ((Y ⧸ A) ⧸ K₁.map (QuotientGroup.mk' A)) = 0 :=
    Nat.eq_zero_of_le_zero ((CFSG.RankThree.CentralLift.localRank_le_of_mulEquiv eQ.symm
      hp).trans hl₂.le)
  have hQeq : pRank p ((Y ⧸ A) ⧸ K₁.map (QuotientGroup.mk' A)) = pRank p K₂ := by
    rw [pRank_eq_open_pRank_top, ← pRank_top_eq_of_mulEquiv hp.one_lt eQ,
      ← pRank_eq_open_pRank_top]
  refine ⟨?_, csSup_le' ?_⟩
  ·
    have h1 := pRank_le_add_of_normal hp (K₁.map (QuotientGroup.mk' A))
    have e1 : pRank p K₁ = CFSG.Open.pRank p K₁ :=
      (pRank_eq_open_pRank_top p K₁).trans (pRank_eq_pRank_top_subgroup K₁).symm
    have e2 : pRank p K₂ = CFSG.Open.pRank p K₂ :=
      (pRank_eq_open_pRank_top p K₂).trans (pRank_eq_pRank_top_subgroup K₂).symm
    obtain ⟨E₁, hE₁K, hE₁, hE₁c⟩ := CFSG.SectionRank.exists_pRank hp.one_lt K₁
    obtain ⟨E₂, hE₂K, hE₂, hE₂c⟩ := CFSG.SectionRank.exists_pRank hp.one_lt K₂
    have h2 := add_le_pRank_of_commute hp hE₁ hE₂ hE₁c hE₂c
      (fun x hx y hy => (mem_centralizer_iff.1 (h12 (hE₁K hx)) y (hE₂K hy)).symm)
      (le_bot_iff.1 (hdisj ▸ inf_le_inf hE₁K hE₂K)) (le_top (a := E₁)) (le_top (a := E₂))
    rw [← e1, ← e2, ← pRank_eq_open_pRank_top] at h2
    omega
  ·
    rintro k ⟨M, ⟨T, hT0, hT2, rfl⟩, rfl⟩
    refine CFSG.SectionRank.pRank_le hp.one_lt fun B hBM hB => ?_
    have hcard := CFSG.RankThree.SubgroupLists.card_eq_card_map_mul_card_inf_ker
      (QuotientGroup.mk' (K₁.map (QuotientGroup.mk' A))) B
    rw [QuotientGroup.ker_mk'] at hcard
    have hBp : IsPGroup p B := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hB.2 x x.2)⟩
    have hBQ : CFSG.Open.IsElemAbelian p (B.map (QuotientGroup.mk' (K₁.map
        (QuotientGroup.mk' A)))) := isElemAbelian_map hB _
    by_cases hTJ : T ≤ K₁.map (QuotientGroup.mk' A)
    ·
      have hT0' : T.subgroupOf (K₁.map (QuotientGroup.mk' A)) ≠ ⊥ := by
        intro h
        apply hT0
        rw [eq_bot_iff]
        intro t ht
        have : (⟨t, hTJ ht⟩ : K₁.map (QuotientGroup.mk' A)) ∈
            T.subgroupOf (K₁.map (QuotientGroup.mk' A)) := mem_subgroupOf.2 ht
        rw [h, mem_bot] at this
        exact (mem_bot).2 (congrArg Subtype.val this)
      have hT2' : IsPGroup 2 (T.subgroupOf (K₁.map (QuotientGroup.mk' A))) :=
        hT2.of_equiv (subgroupOfEquivOfLe hTJ).symm
      have hBJ : (B ⊓ K₁.map (QuotientGroup.mk' A)).subgroupOf (K₁.map (QuotientGroup.mk' A)) ≤
          normalizer ((T.subgroupOf (K₁.map (QuotientGroup.mk' A))) :
            Set (K₁.map (QuotientGroup.mk' A))) := by
        intro x hx
        rw [mem_normalizer_iff]
        intro t
        rw [mem_subgroupOf, mem_subgroupOf]
        have hxM : (x : (Y ⧸ A)) ∈ normalizer (T : Set (Y ⧸ A)) := hBM (mem_subgroupOf.1 hx).1
        exact (mem_normalizer_iff.1 hxM t)
      have hBJe : CFSG.Open.IsElemAbelian p ((B ⊓ K₁.map (QuotientGroup.mk' A)).subgroupOf
          (K₁.map (QuotientGroup.mk' A))) := by
        have h1 := isElemAbelian_inf_left hB (K₁.map (QuotientGroup.mk' A))
        have := h1.1
        refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext (h1.2 _ hx)⟩
        change ((a : K₁.map (QuotientGroup.mk' A)) : Y ⧸ A) * ((b : K₁.map
          (QuotientGroup.mk' A)) : Y ⧸ A) = ((b : K₁.map (QuotientGroup.mk' A)) : Y ⧸ A) *
          ((a : K₁.map (QuotientGroup.mk' A)) : Y ⧸ A)
        exact congrArg Subtype.val (mul_comm' (⟨_, a.2⟩ : (B ⊓ K₁.map (QuotientGroup.mk' A) :
          Subgroup (Y ⧸ A))) ⟨_, b.2⟩)
      have h1 : Nat.card (B ⊓ K₁.map (QuotientGroup.mk' A) : Subgroup (Y ⧸ A)) ≤ p ^ 1 := by
        rw [← Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv]
        refine (card_le_pow_pRank_of_le hp hBJe hBJ).trans (Nat.pow_le_pow_right hp.pos ?_)
        exact (CFSG.RankThree.Classical.pRank_le_localRank hp.one_lt
          ⟨_, hT0', hT2', rfl⟩).trans hJl
      have h2 : Nat.card (B.map (QuotientGroup.mk' (K₁.map (QuotientGroup.mk' A)))) ≤ p ^ 1 := by
        refine (card_le_pow_pRank_of_le hp hBQ le_top).trans (Nat.pow_le_pow_right hp.pos ?_)
        rw [← pRank_eq_open_pRank_top]
        exact hQr
      rw [hcard]
      calc _ ≤ p ^ 1 * p ^ 1 := Nat.mul_le_mul h2 h1
        _ = p ^ 2 := by ring
    ·
      have hT0' : T.map (QuotientGroup.mk' (K₁.map (QuotientGroup.mk' A))) ≠ ⊥ := by
        rw [Ne, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
        exact hTJ
      have h2 : Nat.card (B.map (QuotientGroup.mk' (K₁.map (QuotientGroup.mk' A)))) ≤ p ^ 0 := by
        refine (card_le_pow_pRank_of_le hp hBQ ((map_mono hBM).trans
          (le_normalizer_map _))).trans (Nat.pow_le_pow_right hp.pos ?_)
        rw [← hQl]
        exact CFSG.RankThree.Classical.pRank_le_localRank hp.one_lt ⟨_, hT0', hT2.map _, rfl⟩
      have h1 : Nat.card (B ⊓ K₁.map (QuotientGroup.mk' A) : Subgroup (Y ⧸ A)) ≤ p ^ 2 :=
        (card_inf_le_pow_pRank hp hB _).trans (Nat.pow_le_pow_right hp.pos hJr)
      rw [hcard]
      calc _ ≤ p ^ 0 * p ^ 2 := Nat.mul_le_mul h2 h1
        _ = p ^ 2 := by ring

theorem isElemAbelian_zpowers_of_orderOf {G : Type*} [Group G] {z : G} (hz : orderOf z = p) :
    CFSG.Open.IsElemAbelian p (zpowers z) ∧ Nat.card (zpowers z) = p ^ 1 := by
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, by rw [Nat.card_zpowers, hz, pow_one]⟩
  · obtain ⟨a, i, rfl⟩ := a
    obtain ⟨b, j, rfl⟩ := b
    exact Subtype.ext (Commute.zpow_zpow_self z i j).eq
  · obtain ⟨i, rfl⟩ := hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hz, pow_orderOf_eq_one,
      one_zpow]

theorem localRank_component_eq_one (hp : p.Prime) (hp2 : p ≠ 2) {Y : Type*} [Group Y]
    [Finite Y] (hE : CFSG.layer Y = ⊤) (hPp : IsPGroup p (center Y)) (hloc : localRank p Y ≤ 2)
    (hYc : IsCyclic (center Y)) {K₁ K₂ : Subgroup Y} (hK₁ : CFSG.IsComponent K₁)
    (hK₂ : CFSG.IsComponent K₂) (hne : K₁ ≠ K₂) (hinter : K₁ ⊓ K₂ ≤ center Y)
    (hZ₁ : center K₁ ≠ ⊥) (hr₂ : pRank p K₂ = 2) : localRank p K₁ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h12 := le_centralizer_of_components hK₁ hK₂ hne
  have h21 := le_centralizer_of_components hK₂ hK₁ (Ne.symm hne)
  have hmem12 : ∀ x ∈ K₁, ∀ y ∈ K₂, Commute x y := fun x hx y hy =>
    (mem_centralizer_iff.1 (h12 hx) y hy).symm
  have hZp := isPGroup_center_component hE hPp hK₁
  have hdvd : p ∣ Nat.card (center K₁) := by
    rcases hZp.card_eq_or_dvd with h | h
    · exact absurd (card_eq_one.1 h) hZ₁
    · exact h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  obtain ⟨t, htK, ht⟩ := exists_involution_mem_component hp2 hE hPp hK₁
  refine le_antisymm (csSup_le' ?_) ?_
  · rintro k ⟨M, ⟨T, hT0, hT2, rfl⟩, rfl⟩
    by_contra hk
    push Not at hk
    obtain ⟨E', hE'M, hE', hE'card⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
      (normalizer (T : Set K₁))
    have hEm : CFSG.Open.IsElemAbelian p (E'.map K₁.subtype) := isElemAbelian_map hE' _
    have hEmcard : Nat.card (E'.map K₁.subtype) = p ^ CFSG.Open.pRank p
        (normalizer (T : Set K₁)) := by
      rw [card_map_of_injective K₁.subtype_injective, hE'card]
    have hr₂' : CFSG.Open.pRank p K₂ = 2 := by
      rw [pRank_eq_pRank_top_subgroup, ← pRank_eq_open_pRank_top]
      exact hr₂
    obtain ⟨F, hFK, hF, hFcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt K₂
    rw [hr₂'] at hFcard
    obtain ⟨b, hbF, hbE⟩ : ∃ b ∈ F, b ∉ E'.map K₁.subtype := by
      by_contra hall
      push Not at hall
      have hFZ : F ≤ center Y := fun f hf => hinter ⟨map_subtype_le _ (hall f hf), hFK hf⟩
      have h1 := card_le_of_le_cyclic hF hFZ hYc
      rw [hFcard] at h1
      have : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      rw [pow_one] at this
      omega
    have hT'0 : T.map K₁.subtype ≠ ⊥ := fun h => hT0
      ((Subgroup.map_eq_bot_iff_of_injective _ K₁.subtype_injective).1 h)
    have h3 := succ_le_localRank_of_commute hp hT'0 (hT2.map _) hEm hEmcard
      ((map_mono hE'M).trans (le_normalizer_map K₁.subtype)) (b := b)
      (fun e he => hmem12 e (map_subtype_le _ he) b (hFK hbF)) (hF.2 b hbF) hbE
      (le_normalizer_of_le_centralizer (h21.trans (centralizer_le (map_subtype_le T)))
        (hFK hbF))
    change 2 ≤ CFSG.Open.pRank p (normalizer (T : Set K₁)) at hk
    omega
  ·
    have ht1 : (⟨t, htK⟩ : K₁) ≠ 1 := by
      intro h
      have : t = 1 := congrArg Subtype.val h
      rw [this, orderOf_one] at ht
      exact absurd ht (by norm_num)
    have ht' : orderOf (⟨t, htK⟩ : K₁) = 2 := by rw [← orderOf_coe]; exact ht
    have hT2 : IsPGroup 2 (zpowers (⟨t, htK⟩ : K₁)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht', pow_one])
    have hT0 : zpowers (⟨t, htK⟩ : K₁) ≠ ⊥ := fun h => ht1 (by
      have : (⟨t, htK⟩ : K₁) ∈ zpowers (⟨t, htK⟩ : K₁) := mem_zpowers _
      rwa [h, mem_bot] at this)
    have hz' : orderOf (z : K₁) = p := (orderOf_coe z).trans hz
    obtain ⟨hzE, hzc⟩ := isElemAbelian_zpowers_of_orderOf hz'
    have hzN : zpowers (z : K₁) ≤ normalizer (zpowers (⟨t, htK⟩ : K₁) : Set K₁) :=
      le_normalizer_of_le_centralizer (zpowers_le.2 (mem_centralizer_iff.2 fun g _ =>
        mem_center_iff.1 z.2 g))
    exact (CFSG.SectionRank.le_pRank hp.one_lt hzN hzE hzc).trans
      (CFSG.RankThree.Classical.pRank_le_localRank hp.one_lt ⟨_, hT0, hT2, rfl⟩)

theorem inf_ne_bot_of_centers (hp : p.Prime) {Y : Type*} [Group Y] [Finite Y]
    (hE : CFSG.layer Y = ⊤) (hPp : IsPGroup p (center Y)) (hYc : IsCyclic (center Y))
    {K₁ K₂ : Subgroup Y} (hK₁ : CFSG.IsComponent K₁) (hK₂ : CFSG.IsComponent K₂)
    (hZ₁ : center K₁ ≠ ⊥) (hZ₂ : center K₂ ≠ ⊥) : K₁ ⊓ K₂ ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hel : ∀ {K : Subgroup Y}, CFSG.IsComponent K → center K ≠ ⊥ →
      ∃ z : Y, z ∈ (center K).map K.subtype ∧ orderOf z = p := by
    intro K hK hZ
    have hZp := isPGroup_center_component hE hPp hK
    have hdvd : p ∣ Nat.card (center K) := by
      rcases hZp.card_eq_or_dvd with h | h
      · exact absurd (card_eq_one.1 h) hZ
      · exact h
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
    exact ⟨((z : K) : Y), ⟨z, z.2, rfl⟩, by rw [orderOf_coe, orderOf_coe, hz]⟩
  obtain ⟨z₁, hz₁, ho₁⟩ := hel hK₁ hZ₁
  obtain ⟨z₂, hz₂, ho₂⟩ := hel hK₂ hZ₂
  have hz₁c : z₁ ∈ center Y :=
    (inf_center_eq_of_layer_eq_top hE hK₁ ▸ hz₁ : z₁ ∈ K₁ ⊓ center Y).2
  have hz₂c : z₂ ∈ center Y :=
    (inf_center_eq_of_layer_eq_top hE hK₂ ▸ hz₂ : z₂ ∈ K₂ ⊓ center Y).2
  have heq : (zpowers z₁).subgroupOf (center Y) = (zpowers z₂).subgroupOf (center Y) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq]
    rw [Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.2 hz₁c)).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.2 hz₂c)).toEquiv, Nat.card_zpowers,
      Nat.card_zpowers, ho₁, ho₂]
  have hz₂1 : z₂ ∈ zpowers z₁ := by
    have : (⟨z₂, hz₂c⟩ : center Y) ∈ (zpowers z₁).subgroupOf (center Y) := by
      rw [heq, mem_subgroupOf]
      exact mem_zpowers z₂
    exact mem_subgroupOf.1 this
  have hz₂K₁ : z₂ ∈ K₁ := (zpowers_le.2 (map_subtype_le _ hz₁)) hz₂1
  intro h
  have : z₂ ∈ K₁ ⊓ K₂ := ⟨hz₂K₁, map_subtype_le _ hz₂⟩
  rw [h, mem_bot] at this
  rw [this, orderOf_one] at ho₂
  exact hp.one_lt.ne ho₂

theorem stationary_central_prime_cover_failure_component_models (hp : p.Prime) (hp3 : 3 < p)
    {Y : Type u} [Group Y] [Finite Y] (hE : CFSG.layer Y = ⊤) (hP1 : center Y ≠ ⊥)
    (hPp : IsPGroup p (center Y)) (hloc : localRank p Y ≤ 2) (A : Subgroup Y) [A.Normal]
    (_hA1 : A ≠ ⊥) (hAZ : A ≤ center Y)
    (hfail : 2 < localRank p (Y ⧸ A) ∨ (pRank p Y ≤ 3 ∧ pRank p Y < pRank p (Y ⧸ A))) :
    (CFSG.IsQuasisimple Y ∧ Nat.card (ComponentIndex Y) = 1) ∨
    (Nat.card (ComponentIndex Y) = 2 ∧
      ∃ K₁ K₂ : Subgroup Y, CFSG.IsComponent K₁ ∧ CFSG.IsComponent K₂ ∧ K₁ ≠ K₂ ∧
        (∀ K : Subgroup Y, CFSG.IsComponent K → K = K₁ ∨ K = K₂) ∧
        IsCyclic (center Y) ∧ center K₁ ≠ ⊥ ∧ IsCyclic (center K₁) ∧ center K₂ ≠ ⊥ ∧
        IsCyclic (center K₂) ∧
        K₁ ⊓ K₂ = (center K₁).map K₁.subtype ⊓ (center K₂).map K₂.subtype ∧ K₁ ⊓ K₂ ≠ ⊥ ∧
        pRank p K₁ = 2 ∧ pRank p K₂ = 2 ∧ localRank p K₁ = 1 ∧ localRank p K₂ = 1 ∧
        K₁ ⊔ K₂ = ⊤ ∧ center Y = (center K₁).map K₁.subtype ⊔ (center K₂).map K₂.subtype ∧
        ∃ μ : K₁ × K₂ →* Y, (∀ x : K₁ × K₂, μ x = (x.1 : Y) * x.2) ∧
          Function.Surjective μ ∧
          ∀ x : K₁ × K₂, μ x = 1 ↔ ∃ z ∈ K₁ ⊓ K₂, (x.1 : Y) = z ∧ (x.2 : Y) = z⁻¹) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hlocq : localRank p (Y ⧸ A) ≤ pRank p (Y ⧸ A) := by
    have h := CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_pRank p hp (Y ⧸ A)
    refine h.trans ?_
    change CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ A)) ≤ _
    rw [← pRank_eq_open_pRank_top]
  have hcomp0 : 0 < Nat.card (ComponentIndex Y) := by
    by_contra h0
    push Not at h0
    have hemp : IsEmpty (ComponentIndex Y) := Finite.card_eq_zero_iff.1 (by omega)
    have hbot : CFSG.layer Y = ⊥ :=
      layer_eq_bot_of_forall fun K hK => hemp.elim ⟨K, hK⟩
    apply hP1
    rw [eq_bot_iff]
    intro z _
    have : z ∈ CFSG.layer Y := hE ▸ mem_top z
    rwa [hbot] at this
  rcases (show Nat.card (ComponentIndex Y) = 1 ∨ 2 ≤ Nat.card (ComponentIndex Y) by omega)
    with h1 | h2
  ·
    left
    obtain ⟨⟨K, hK⟩⟩ : Nonempty (ComponentIndex Y) := Finite.card_pos_iff.1 hcomp0
    have hall : ∀ K' : Subgroup Y, CFSG.IsComponent K' → K' = K := fun K' hK' => by
      have := Finite.card_le_one_iff_subsingleton.1 h1.le
      exact congrArg Subtype.val (Subsingleton.elim (⟨K', hK'⟩ : ComponentIndex Y) ⟨K, hK⟩)
    have hKtop : K = ⊤ := by
      rw [← hE]
      exact le_antisymm (le_sSup hK) (sSup_le fun K' hK' => (hall K' hK').le)
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MulEquiv.subgroupCongr hKtop).trans Subgroup.topEquiv) hK.1, h1⟩
  right
  have hYc := isCyclic_center_of_components hp hp3 hE hP1 hPp hloc h2
  obtain ⟨K₀, hK₀, hZ₀⟩ := exists_component_center_ne_bot hE hP1
  have hr₀ := component_pRank_eq_two hp hp3 hE hPp hloc h2 hK₀ hZ₀
  have hZp₀ := isPGroup_center_component hE hPp hK₀
  have hpK₀ : p ∣ Nat.card K₀ := by
    have hdvd : p ∣ Nat.card (center K₀) := by
      rcases hZp₀.card_eq_or_dvd with h | h
      · exact absurd (card_eq_one.1 h) hZ₀
      · exact h
    exact hdvd.trans (card_subgroup_dvd_card _)
  have huniq : ¬ ∀ K' : Subgroup Y, CFSG.IsComponent K' → p ∣ Nat.card K' → K' = K₀ := by
    intro huniq
    obtain ⟨-, -, -, -, -, hquot, hrank⟩ :=
      component_product_structure hp hp3 hE hPp hloc h2 hK₀ hZ₀ huniq
    have := hquot A hAZ
    rcases hfail with hf | ⟨-, hf⟩ <;> omega
  push Not at huniq
  obtain ⟨K', hK', hpK', hne'⟩ := huniq
  have hne : K₀ ≠ K' := Ne.symm hne'
  have ht2 : Nat.card (ComponentIndex Y) = 2 := by
    by_contra h3
    obtain ⟨K, -, -, -, hK⟩ :=
      exists_unique_component_dvd hp hp3 hE hP1 hPp hloc (by omega)
    exact hne (by rw [hK K₀ hK₀ hpK₀, hK K' hK' hpK'])
  have hall : ∀ K : Subgroup Y, CFSG.IsComponent K → K = K₀ ∨ K = K' := by
    intro K hK
    have hcard : ({⟨K₀, hK₀⟩, ⟨K', hK'⟩} : Finset (ComponentIndex Y)).card =
        Fintype.card (ComponentIndex Y) := by
      rw [Finset.card_pair (fun h => hne (congrArg Subtype.val h)), ← Nat.card_eq_fintype_card,
        ht2]
    have hmem := (Finset.eq_univ_of_card _ hcard) ▸ Finset.mem_univ (⟨K, hK⟩ : ComponentIndex Y)
    simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq] at hmem
    exact hmem
  have hZ' : center K' ≠ ⊥ := by
    intro hZ'
    obtain ⟨h1, h2'⟩ := disjoint_components_quotient_bounds hp hp3 hE hPp hloc hK₀ hK' hne hall
      hZ₀ hZ' hr₀ hpK' A hAZ
    rcases hfail with hf | ⟨-, hf⟩ <;> omega
  obtain ⟨h12, h21, hsup, hn₁, hn₂, hcen, hinter⟩ := two_components_facts hE hK₀ hK' hne hall
  have hcyc₀ := (component_pRank_le_two_and_isCyclic_center hp hp3 hE hPp hloc h2 hK₀).2
  have hcyc' := (component_pRank_le_two_and_isCyclic_center hp hp3 hE hPp hloc h2 hK').2
  have hr' := component_pRank_eq_two hp hp3 hE hPp hloc h2 hK' hZ'
  have hinterZ : K₀ ⊓ K' ≤ center Y := by
    rw [hinter]
    exact inf_le_left.trans (by rw [← inf_center_eq_of_layer_eq_top hE hK₀]; exact inf_le_right)
  have hinterZ' : K' ⊓ K₀ ≤ center Y := by rw [inf_comm]; exact hinterZ
  have hcomm : ∀ (x : K₀) (y : K'), Commute (K₀.subtype x) (K'.subtype y) := fun x y =>
    (mem_centralizer_iff.1 (h12 x.2) y y.2).symm
  let μ : K₀ × K' →* Y := MonoidHom.noncommCoprod K₀.subtype K'.subtype hcomm
  have hμ : ∀ x : K₀ × K', μ x = (x.1 : Y) * x.2 := fun x => rfl
  refine ⟨ht2, K₀, K', hK₀, hK', hne, hall, hYc, hZ₀, hcyc₀, hZ', hcyc', hinter,
    inf_ne_bot_of_centers hp hE hPp hYc hK₀ hK' hZ₀ hZ', hr₀, hr',
    localRank_component_eq_one hp hp2 hE hPp hloc hYc hK₀ hK' hne hinterZ hZ₀ hr',
    localRank_component_eq_one hp hp2 hE hPp hloc hYc hK' hK₀ (Ne.symm hne) hinterZ' hZ' hr₀,
    hsup, hcen, μ, hμ, fun y => ?_, fun x => ?_⟩
  · have hy : y ∈ ((K₀ ⊔ K' : Subgroup Y) : Set Y) := by rw [hsup]; exact Set.mem_univ y
    rw [mul_normal, Set.mem_mul] at hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  · rw [hμ]
    constructor
    · intro h
      refine ⟨x.1, ⟨x.1.2, ?_⟩, rfl, ?_⟩
      · rw [eq_inv_of_mul_eq_one_left h]
        exact K'.inv_mem x.2.2
      · rw [eq_inv_of_mul_eq_one_right h]
    · rintro ⟨z, -, h1, h2⟩
      rw [h1, h2, mul_inv_cancel]

end ComponentModels

end CFSG.RankThree.OddKernel
