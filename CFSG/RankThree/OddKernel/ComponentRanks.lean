module

public import CFSG.RankThree.OddKernel.PerfectCentralQuotient
public import CFSG.RankThree.OddKernel.FixedPlaneKernel
public import CFSG.LocalAnalysis.SectionRank.CyclicCenter
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.GroupTheory.PRankCoprimeQuotient

public section

namespace CFSG.RankThree.OddKernel

open Subgroup CFSG.SectionRank
open scoped commutatorElement Pointwise

universe u

section ComponentRanks

open CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (localRank)

variable {p : ℕ}

theorem map_center_layer_eq {Y : Type*} [Group Y] (hE : CFSG.layer Y = ⊤) :
    (center (CFSG.layer Y)).map (CFSG.layer Y).subtype = center Y := by
  ext z
  rw [CFSG.LocalCores.mem_map_center_iff, hE, coe_top, centralizer_univ]
  exact ⟨fun h => h.2, fun h => ⟨mem_top z, h⟩⟩

theorem inf_center_eq_of_layer_eq_top {Y : Type*} [Group Y] [Finite Y]
    (hE : CFSG.layer Y = ⊤) {K : Subgroup Y} (hK : CFSG.IsComponent K) :
    K ⊓ center Y = (center K).map K.subtype := by
  have h := (layer_center (G := Y)).2 K hK
  rwa [map_center_layer_eq hE] at h

theorem center_eq_iSup_of_layer_eq_top {Y : Type*} [Group Y] [Finite Y]
    (hE : CFSG.layer Y = ⊤) :
    center Y = ⨆ K : ComponentIndex Y, (center K.1).map K.1.subtype := by
  have h := (layer_center (G := Y)).1
  rwa [map_center_layer_eq hE] at h

theorem isPGroup_center_component {Y : Type*} [Group Y] [Finite Y] (hE : CFSG.layer Y = ⊤)
    (hPp : IsPGroup p (center Y)) {K : Subgroup Y} (hK : CFSG.IsComponent K) :
    IsPGroup p (center K) := by
  have h : IsPGroup p ((center K).map K.subtype) :=
    hPp.to_le ((inf_center_eq_of_layer_eq_top hE hK).symm ▸ inf_le_right)
  exact h.of_equiv ((center K).equivMapOfInjective _ K.subtype_injective).symm

theorem exists_involution_mem_component [Fact p.Prime] (hp2 : p ≠ 2) {Y : Type*} [Group Y]
    [Finite Y] (hE : CFSG.layer Y = ⊤) (hPp : IsPGroup p (center Y)) {K : Subgroup Y}
    (hK : CFSG.IsComponent K) : ∃ t ∈ K, orderOf t = 2 := by
  have hsimple := hK.1.2.1
  have hnab := hK.1.2.2
  obtain ⟨-, s, hs⟩ := CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnab
  have hker : Odd (Nat.card (QuotientGroup.mk' (center K)).ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨k, hk⟩ := (isPGroup_center_component hE hPp hK).exists_card_eq
    rw [hk]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  obtain ⟨t, ht, -⟩ := exists_involution_lift (QuotientGroup.mk' (center K))
    (QuotientGroup.mk'_surjective _) hker hs
  exact ⟨t, t.2, by rw [orderOf_coe, ht]⟩

theorem le_centralizer_of_components {Y : Type*} [Group Y] [Finite Y] {K K' : Subgroup Y}
    (hK : CFSG.IsComponent K) (hK' : CFSG.IsComponent K') (hne : K ≠ K') :
    K ≤ centralizer (K' : Set Y) := by
  rcases distinct_components_commute hK hK' with h | h
  · exact absurd h hne
  · exact commutator_eq_bot_iff_le_centralizer.1 h

theorem pRank_le_localRank_of_le_centralizer [Fact p.Prime] (hp2 : p ≠ 2) {Y : Type*} [Group Y]
    [Finite Y] (hE : CFSG.layer Y = ⊤) (hPp : IsPGroup p (center Y)) {K' X : Subgroup Y}
    (hK' : CFSG.IsComponent K') (hX : X ≤ centralizer (K' : Set Y)) :
    CFSG.Open.pRank p X ≤ localRank p Y := by
  obtain ⟨t, htK, ht⟩ := exists_involution_mem_component hp2 hE hPp hK'
  have hXt : X ≤ centralizer {t} :=
    hX.trans (centralizer_le (Set.singleton_subset_iff.2 htK))
  have h := pRank_centralizer_le_localRank (Fact.out : p.Prime).one_lt ht
  rw [pRank_eq_open_pRank_top, ← pRank_eq_pRank_top_subgroup] at h
  exact (CFSG.SectionRank.pRank_mono (Fact.out : p.Prime).one_lt hXt).trans h

theorem succ_le_pRank_of_commute {G : Type*} [Group G] [Finite G] (hp : p.Prime)
    {E H : Subgroup G} (hE : CFSG.Open.IsElemAbelian p E) {r : ℕ} (hEcard : Nat.card E = p ^ r)
    {b : G} (hbc : ∀ e ∈ E, Commute e b) (hbp : b ^ p = 1) (hbE : b ∉ E) (hEH : E ≤ H)
    (hbH : b ∈ H) : r + 1 ≤ CFSG.Open.pRank p H := by
  have : Fact p.Prime := ⟨hp⟩
  have hb1 : b ≠ 1 := fun h => hbE (h ▸ one_mem E)
  have hbord : orderOf b = p := orderOf_eq_prime hbp hb1
  have hcomm : ∀ (e : E) (c : zpowers b), Commute (E.subtype e) ((zpowers b).subtype c) := by
    rintro e ⟨c, k, rfl⟩
    exact (hbc e e.2).zpow_right k
  let f : E × zpowers b →* G := MonoidHom.noncommCoprod E.subtype (zpowers b).subtype hcomm
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨e, c⟩ hx
    have hx' : (e : G) * c = 1 := hx
    have hcE : (c : G) ∈ E := by
      rw [eq_inv_of_mul_eq_one_right hx']
      exact inv_mem e.2
    have hc1 : c = 1 := by
      by_contra hc
      have htop := zpowers_eq_top_of_prime_card (G := zpowers b)
        (by rw [Nat.card_zpowers, hbord]) hc
      have hbmem : (⟨b, mem_zpowers b⟩ : zpowers b) ∈ zpowers c := htop ▸ mem_top _
      obtain ⟨m, hm⟩ := hbmem
      apply hbE
      have : (c : G) ^ m = b := congrArg Subtype.val hm
      rw [← this]
      exact zpow_mem hcE m
    rw [hc1, OneMemClass.coe_one, mul_one] at hx'
    have he1 : e = 1 := Subtype.ext hx'
    rw [he1, hc1]
    rfl
  have hEc := hE.1
  refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt (A := E × zpowers b) ?_ ?_ ?_ f hf ?_
  · rintro ⟨e₁, c₁⟩ ⟨e₂, c₂⟩
    refine Prod.ext (mul_comm' e₁ e₂) ?_
    obtain ⟨c₁, k₁, rfl⟩ := c₁
    obtain ⟨c₂, k₂, rfl⟩ := c₂
    exact Subtype.ext (Commute.zpow_zpow_self b k₁ k₂).eq
  · rintro ⟨e, c⟩
    refine Prod.ext (Subtype.ext (hE.2 e e.2)) ?_
    obtain ⟨c, k, rfl⟩ := c
    apply Subtype.ext
    change (b ^ k) ^ p = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hbp, one_zpow]
  · rw [Nat.card_prod, hEcard, Nat.card_zpowers, hbord, pow_succ]
  · rintro _ ⟨⟨e, c⟩, rfl⟩
    obtain ⟨c, k, rfl⟩ := c
    exact H.mul_mem (hEH e.2) (zpow_mem hbH k)

theorem exists_other_component {Y : Type*} [Group Y] [Finite Y]
    (ht : 2 ≤ Nat.card (ComponentIndex Y)) {K : Subgroup Y} (hK : CFSG.IsComponent K) :
    ∃ K' : Subgroup Y, CFSG.IsComponent K' ∧ K ≠ K' := by
  have h1 : 1 < Nat.card (ComponentIndex Y) := ht
  have := Finite.one_lt_card_iff_nontrivial.1 h1
  obtain ⟨K', hK'⟩ := exists_ne (⟨K, hK⟩ : ComponentIndex Y)
  exact ⟨K'.1, K'.2, fun h => hK' (Subtype.ext h.symm)⟩

theorem component_pRank_le_two_and_isCyclic_center (hp : p.Prime) (hp3 : 3 < p) {Y : Type*}
    [Group Y] [Finite Y] (hE : CFSG.layer Y = ⊤) (hPp : IsPGroup p (center Y))
    (hloc : localRank p Y ≤ 2) (ht : 2 ≤ Nat.card (ComponentIndex Y)) {K : Subgroup Y}
    (hK : CFSG.IsComponent K) : pRank p K ≤ 2 ∧ IsCyclic (center K) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨K', hK', hne⟩ := exists_other_component ht hK
  have hrank : pRank p K ≤ 2 := by
    rw [pRank_eq_open_pRank_top, ← pRank_eq_pRank_top_subgroup]
    exact (pRank_le_localRank_of_le_centralizer hp2 hE hPp hK'
      (le_centralizer_of_components hK hK' hne)).trans hloc
  have : Group.IsPerfect K := hK.1.1
  exact ⟨hrank, isCyclic_of_le_center_of_perfect hp hp3 hrank le_rfl
    (isPGroup_center_component hE hPp hK)⟩

theorem component_pRank_eq_two (hp : p.Prime) (hp3 : 3 < p) {Y : Type*} [Group Y] [Finite Y]
    (hE : CFSG.layer Y = ⊤) (hPp : IsPGroup p (center Y)) (hloc : localRank p Y ≤ 2)
    (ht : 2 ≤ Nat.card (ComponentIndex Y)) {K : Subgroup Y} (hK : CFSG.IsComponent K)
    (hZ : center K ≠ ⊥) : pRank p K = 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Group.IsPerfect K := hK.1.1
  have hZp := isPGroup_center_component hE hPp hK
  have hdvd : p ∣ Nat.card (center K) := by
    rcases hZp.card_eq_or_dvd with h | h
    · exact absurd (card_eq_one.1 h) hZ
    · exact h
  have hpK : p ∣ Nat.card K := hdvd.trans (card_subgroup_dvd_card _)
  exact le_antisymm (component_pRank_le_two_and_isCyclic_center hp hp3 hE hPp hloc ht hK).1
    ((CFSG.SectionRank.perfect_cyclic_center_odd_elements hp2 hpK).2 hdvd)

theorem exists_component_center_ne_bot {Y : Type*} [Group Y] [Finite Y]
    (hE : CFSG.layer Y = ⊤) (hP1 : center Y ≠ ⊥) :
    ∃ K : Subgroup Y, CFSG.IsComponent K ∧ center K ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  apply hP1
  rw [center_eq_iSup_of_layer_eq_top hE]
  refine iSup_eq_bot.2 fun K => ?_
  rw [hcon K.1 K.2, Subgroup.map_bot]

theorem card_le_of_le_cyclic {G : Type*} [Group G] [Finite G] [Fact p.Prime] {B C : Subgroup G}
    (hB : CFSG.Open.IsElemAbelian p B) (hBC : B ≤ C) (hC : IsCyclic C) : Nat.card B ≤ p := by
  have : IsCyclic B := Subgroup.isCyclic_of_le hBC
  exact CFSG.RankThree.SubgroupLists.card_le_of_pow_eq_one_of_isCyclic fun b =>
    Subtype.ext (hB.2 b b.2)

theorem isCyclic_center_of_components (hp : p.Prime) (hp3 : 3 < p) {Y : Type*} [Group Y]
    [Finite Y] (hE : CFSG.layer Y = ⊤) (hP1 : center Y ≠ ⊥) (hPp : IsPGroup p (center Y))
    (hloc : localRank p Y ≤ 2) (ht : 2 ≤ Nat.card (ComponentIndex Y)) :
    IsCyclic (center Y) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨K₀, hK₀, hZ₀⟩ := exists_component_center_ne_bot hE hP1
  obtain ⟨K', hK', hne⟩ := exists_other_component ht hK₀
  have h2 := component_pRank_eq_two hp hp3 hE hPp hloc ht hK₀ hZ₀
  have hZcyc := (component_pRank_le_two_and_isCyclic_center hp hp3 hE hPp hloc ht hK₀).2
  obtain ⟨E₀, hE₀K, hE₀, hE₀card⟩ := CFSG.SectionRank.exists_pRank hp.one_lt K₀
  have hr : CFSG.Open.pRank p K₀ = 2 := by
    rw [pRank_eq_pRank_top_subgroup, ← pRank_eq_open_pRank_top]
    exact h2
  rw [hr] at hE₀card
  have hcycZ : IsCyclic ((center K₀).map K₀.subtype) :=
    isCyclic_of_surjective (K₀.subtype.subgroupMap _) (K₀.subtype.subgroupMap_surjective _)
  have hrank : pRank p (center Y) ≤ 1 := by
    rw [pRank_eq_open_pRank_top, ← pRank_eq_pRank_top_subgroup]
    refine CFSG.SectionRank.pRank_le hp.one_lt fun B hBZ hB => ?_
    rw [pow_one]
    by_contra hcard
    push Not at hcard
    obtain ⟨b, hbB, hbE⟩ : ∃ b ∈ B, b ∉ E₀ := by
      by_contra hall
      push Not at hall
      have hBle : B ≤ (center K₀).map K₀.subtype := by
        rw [← inf_center_eq_of_layer_eq_top hE hK₀]
        exact fun b hb => ⟨hE₀K (hall b hb), hBZ hb⟩
      exact absurd (card_le_of_le_cyclic hB hBle hcycZ) (not_le.2 hcard)
    have hcentral : b ∈ center Y := hBZ hbB
    have h3 := succ_le_pRank_of_commute hp hE₀ hE₀card
      (fun e _ => mem_center_iff.1 hcentral e) (hB.2 b hbB) hbE
      (hE₀K.trans (le_centralizer_of_components hK₀ hK' hne))
      (center_le_centralizer _ hcentral)
    have h4 := (pRank_le_localRank_of_le_centralizer hp2 hE hPp hK' le_rfl).trans hloc
    omega
  exact ((CFSG.LocalAnalysis.ComponentInitial.pgroup_rank_one_classification hp hPp).1
    hrank).resolve_right fun h => hp2 h.1

theorem exists_unique_component_dvd (hp : p.Prime) (hp3 : 3 < p) {Y : Type*} [Group Y]
    [Finite Y] (hE : CFSG.layer Y = ⊤) (hP1 : center Y ≠ ⊥) (hPp : IsPGroup p (center Y))
    (hloc : localRank p Y ≤ 2) (ht3 : 3 ≤ Nat.card (ComponentIndex Y)) :
    ∃ K : Subgroup Y, CFSG.IsComponent K ∧ p ∣ Nat.card K ∧ center K ≠ ⊥ ∧
      ∀ K' : Subgroup Y, CFSG.IsComponent K' → p ∣ Nat.card K' → K' = K := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have ht : 2 ≤ Nat.card (ComponentIndex Y) := by omega
  obtain ⟨K₀, hK₀, hZ₀⟩ := exists_component_center_ne_bot hE hP1
  have hZp := isPGroup_center_component hE hPp hK₀
  have hdvdZ : p ∣ Nat.card (center K₀) := by
    rcases hZp.card_eq_or_dvd with h | h
    · exact absurd (card_eq_one.1 h) hZ₀
    · exact h
  have hpK₀ : p ∣ Nat.card K₀ := hdvdZ.trans (card_subgroup_dvd_card _)
  refine ⟨K₀, hK₀, hpK₀, hZ₀, fun K' hK' hpK' => ?_⟩
  by_contra hne
  have h2 := component_pRank_eq_two hp hp3 hE hPp hloc ht hK₀ hZ₀
  obtain ⟨E₀, hE₀K, hE₀, hE₀card⟩ := CFSG.SectionRank.exists_pRank hp.one_lt K₀
  have hr : CFSG.Open.pRank p K₀ = 2 := by
    rw [pRank_eq_pRank_top_subgroup, ← pRank_eq_open_pRank_top]
    exact h2
  rw [hr] at hE₀card
  have hZ'cyc := (component_pRank_le_two_and_isCyclic_center hp hp3 hE hPp hloc ht hK').2
  have hZ'rank : pRank p (center K') ≤ 1 :=
    (CFSG.LocalAnalysis.ComponentInitial.pgroup_rank_one_classification hp
      (isPGroup_center_component hE hPp hK')).2 (Or.inl hZ'cyc)
  have : Group.IsPerfect K' := hK'.1.1
  obtain ⟨g, hg, hgZ⟩ := (CFSG.SectionRank.perfect_cyclic_center_odd_elements hp2 hpK').1 hZ'rank
  have hK₀K' := le_centralizer_of_components hK₀ hK' (Ne.symm hne)
  have hgE : (g : Y) ∉ E₀ := fun h => hgZ (mem_center_iff.2 fun k => Subtype.ext
    (mem_centralizer_iff.1 (hK₀K' (hE₀K h)) k k.2))
  obtain ⟨K'', -, hK''⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({⟨K₀, hK₀⟩, ⟨K', hK'⟩} : Finset (ComponentIndex Y))) (t := Finset.univ) (by
      calc ({⟨K₀, hK₀⟩, ⟨K', hK'⟩} : Finset (ComponentIndex Y)).card ≤ 2 :=
            (Finset.card_insert_le _ _).trans (by rw [Finset.card_singleton])
        _ < Finset.univ.card := by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
  have h0 : K''.1 ≠ K₀ := fun h => hK'' (by simp [← h])
  have h1 : K''.1 ≠ K' := fun h => hK'' (by simp [← h])
  have hgp : (g : Y) ^ p = 1 := by
    rw [← SubgroupClass.coe_pow, ← hg, pow_orderOf_eq_one, OneMemClass.coe_one]
  have h3 := succ_le_pRank_of_commute hp hE₀ hE₀card
    (fun e he => (mem_centralizer_iff.1 (hK₀K' (hE₀K he)) g g.2).symm) hgp hgE
    (hE₀K.trans (le_centralizer_of_components hK₀ K''.2 (Ne.symm h0)))
    (le_centralizer_of_components hK' K''.2 (Ne.symm h1) g.2)
  have h4 := (pRank_le_localRank_of_le_centralizer hp2 hE hPp K''.2 le_rfl).trans hloc
  omega

theorem component_product_structure (hp : p.Prime) (hp3 : 3 < p) {Y : Type*} [Group Y]
    [Finite Y] (hE : CFSG.layer Y = ⊤) (hPp : IsPGroup p (center Y))
    (hloc : localRank p Y ≤ 2) (ht : 2 ≤ Nat.card (ComponentIndex Y)) {K₀ : Subgroup Y}
    (hK₀ : CFSG.IsComponent K₀) (hZ₀ : center K₀ ≠ ⊥)
    (huniq : ∀ K' : Subgroup Y, CFSG.IsComponent K' → p ∣ Nat.card K' → K' = K₀) :
    let L := ⨆ K' : {K' : Subgroup Y // CFSG.IsComponent K' ∧ K' ≠ K₀}, K'.1
    K₀ ⊓ L = ⊥ ∧ K₀ ⊔ L = ⊤ ∧ L ≤ centralizer (K₀ : Set Y) ∧ ¬ p ∣ Nat.card L ∧
      center L = ⊥ ∧ (∀ (A : Subgroup Y) [A.Normal], A ≤ center Y → pRank p (Y ⧸ A) ≤ 2) ∧
      pRank p Y = 2 := by
  intro L
  have : Fact p.Prime := ⟨hp⟩
  have hndvd : ∀ K' : Subgroup Y, CFSG.IsComponent K' → K' ≠ K₀ → ¬ p ∣ Nat.card K' :=
    fun K' hK' hne hdvd => hne (huniq K' hK' hdvd)
  have hcen : ∀ K' : Subgroup Y, CFSG.IsComponent K' → K' ≠ K₀ → center K' = ⊥ := by
    intro K' hK' hne
    obtain ⟨k, hk⟩ := (isPGroup_center_component hE hPp hK').exists_card_eq
    have hdvd : p ^ k ∣ Nat.card K' := hk ▸ card_subgroup_dvd_card _
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, pow_zero] at hk
      exact card_eq_one.1 hk
    · exact absurd ((dvd_pow_self p hpos.ne').trans hdvd) (hndvd K' hK' hne)
  have hZY : center Y ≤ K₀ := by
    rw [center_eq_iSup_of_layer_eq_top hE]
    refine iSup_le fun K => ?_
    by_cases hK : K.1 = K₀
    · obtain ⟨K, hKc⟩ := K
      subst hK
      exact map_subtype_le _
    · rw [hcen K.1 K.2 hK, Subgroup.map_bot]
      exact bot_le
  have hLc : L ≤ centralizer (K₀ : Set Y) :=
    iSup_le fun K' => le_centralizer_of_components K'.2.1 hK₀ K'.2.2
  have hcompn : ∀ K' : {K' : Subgroup Y // CFSG.IsComponent K' ∧ K' ≠ K₀}, K'.1.Normal :=
    fun K' => CFSG.LocalCores.component_normal_of_layer_eq_top hE K'.2.1
  have hLn : L.Normal := Subgroup.iSup_normal _
  have hLp : ¬ p ∣ Nat.card L := by
    have hle : L ≤ CFSG.pPrimeCore p Y := iSup_le fun K' => le_sSup ⟨hcompn K',
      (Nat.Prime.coprime_iff_not_dvd hp).2 (hndvd K'.1 K'.2.1 K'.2.2)⟩
    intro h
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
      (h.trans (card_dvd_of_le hle))
  have hdisj : K₀ ⊓ L = ⊥ := by
    have hle : K₀ ⊓ L ≤ (center K₀).map K₀.subtype := fun g hg =>
      (CFSG.LocalCores.mem_map_center_iff K₀).2 ⟨hg.1, hLc hg.2⟩
    have hZp : IsPGroup p ((center K₀).map K₀.subtype) :=
      (isPGroup_center_component hE hPp hK₀).map _
    obtain ⟨k, hk⟩ := (hZp.to_le hle).exists_card_eq
    have hdvd : p ^ k ∣ Nat.card L := hk ▸ card_dvd_of_le inf_le_right
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, pow_zero] at hk
      exact card_eq_one.1 hk
    · exact absurd ((dvd_pow_self p hpos.ne').trans hdvd) hLp
  have hsup : K₀ ⊔ L = ⊤ := by
    rw [eq_top_iff, ← hE]
    refine sSup_le fun K hK => ?_
    by_cases hKK : K = K₀
    · exact hKK ▸ le_sup_left
    · exact (le_iSup (fun K' : {K' : Subgroup Y // CFSG.IsComponent K' ∧ K' ≠ K₀} => K'.1)
        ⟨K, hK, hKK⟩).trans le_sup_right
  have hdec : ∀ g : Y, ∃ k ∈ K₀, ∃ l ∈ L, k * l = g := fun g => by
    have hg : g ∈ ((K₀ ⊔ L : Subgroup Y) : Set Y) := by rw [hsup]; exact Set.mem_univ g
    rw [mul_normal] at hg
    obtain ⟨k, hk, l, hl, hkl⟩ := Set.mem_mul.1 hg
    exact ⟨k, hk, l, hl, hkl⟩
  have hZL : center L = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    have hzY : (z : Y) ∈ center Y := by
      rw [mem_center_iff]
      intro g
      obtain ⟨k, hk, l, hl, rfl⟩ := hdec g
      have h1 : k * z = z * k := mem_centralizer_iff.1 (hLc z.2) k hk
      have h2 : l * z = z * l := congrArg Subtype.val (mem_center_iff.1 hz ⟨l, hl⟩)
      rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
    have hz0 : (z : Y) ∈ K₀ ⊓ L := ⟨hZY hzY, z.2⟩
    rw [hdisj, mem_bot] at hz0
    exact (mem_bot).2 (Subtype.ext hz0)
  have hK₀rank : pRank p K₀ ≤ 2 :=
    (component_pRank_le_two_and_isCyclic_center hp hp3 hE hPp hloc ht hK₀).1
  have : Group.IsPerfect K₀ := hK₀.1.1
  have hquot : ∀ (A : Subgroup Y) [A.Normal], A ≤ center Y → pRank p (Y ⧸ A) ≤ 2 := by
    intro A _ hAZ
    have hπLn : (L.map (QuotientGroup.mk' A)).Normal := hLn.map _ (QuotientGroup.mk'_surjective A)
    have hπLp : ¬ p ∣ Nat.card (L.map (QuotientGroup.mk' A)) := fun h =>
      hLp (h.trans (card_map_dvd L _))
    let φ : K₀ →* (Y ⧸ A) ⧸ L.map (QuotientGroup.mk' A) :=
      (QuotientGroup.mk' _).comp ((QuotientGroup.mk' A).comp K₀.subtype)
    have hφ : Function.Surjective φ := by
      intro q
      obtain ⟨q', rfl⟩ := QuotientGroup.mk'_surjective _ q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective A q'
      obtain ⟨k, hk, l, hl, rfl⟩ := hdec g
      refine ⟨⟨k, hk⟩, ?_⟩
      change QuotientGroup.mk' _ (QuotientGroup.mk' A k) =
        QuotientGroup.mk' _ (QuotientGroup.mk' A (k * l))
      have hl1 : (QuotientGroup.mk' (L.map (QuotientGroup.mk' A))) (QuotientGroup.mk' A l) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (mem_map_of_mem _ hl)
      rw [map_mul, map_mul, hl1, mul_one]
    have hφker : φ.ker ≤ center K₀ := by
      intro k hk
      have h1 : QuotientGroup.mk' A (k : Y) ∈ L.map (QuotientGroup.mk' A) :=
        (QuotientGroup.eq_one_iff _).1 hk
      obtain ⟨l, hl, hlk⟩ := mem_map.1 h1
      have h2 : l⁻¹ * k ∈ A := QuotientGroup.eq.1 hlk
      have h3 : l ∈ K₀ := by
        have : l = k * (l⁻¹ * k)⁻¹ := by group
        rw [this]
        exact K₀.mul_mem k.2 (K₀.inv_mem (hZY (hAZ h2)))
      have hl1 : l = 1 := by
        have : l ∈ K₀ ⊓ L := ⟨h3, hl⟩
        rwa [hdisj, mem_bot] at this
      rw [hl1, inv_one, one_mul] at h2
      exact mem_center_iff.2 fun k' => Subtype.ext (mem_center_iff.1 (hAZ h2) k')
    have h1 := perfect_rank_two_large_prime_quotient_pRank_le_two hp hp3 hK₀rank φ.ker hφker
    have e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
    rw [← CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp _ hπLp,
      pRank_eq_open_pRank_top, ← pRank_top_eq_of_mulEquiv hp.one_lt e, ← pRank_eq_open_pRank_top]
    exact h1
  refine ⟨hdisj, hsup, hLc, hLp, hZL, hquot, le_antisymm ?_ ?_⟩
  · have h := hquot ⊥ bot_le
    rwa [pRank_eq_open_pRank_top, pRank_top_eq_of_mulEquiv hp.one_lt QuotientGroup.quotientBot,
      ← pRank_eq_open_pRank_top] at h
  · rw [← component_pRank_eq_two hp hp3 hE hPp hloc ht hK₀ hZ₀, pRank_eq_open_pRank_top,
      pRank_eq_open_pRank_top]
    exact pRank_top_le_of_injective hp.one_lt K₀.subtype K₀.subtype_injective

end ComponentRanks

end CFSG.RankThree.OddKernel
