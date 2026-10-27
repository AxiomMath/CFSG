module

public import CFSG.RankThree.PartOne.S12.BaseNodes
import CFSG.RankThree.PartOne.S12.Sec1210
import CFSG.RankThree.PartOne.S12.Sec127
import CFSG.RankThree.PartOne.S12.Sec12Three
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.PartOne.Torsion37
open scoped commutatorElement

namespace Sec13Base

section Reflection

variable {G : Type} [Group G] {p : ℕ} {E : Subgroup G}

@[expose] def moveHom (hcomm : ∀ a b : E, a * b = b * a) (t : MulAut E) : E →* E where
  toFun e := t e * e⁻¹
  map_one' := by simp
  map_mul' a b := by
    show t (a * b) * (a * b)⁻¹ = (t a * a⁻¹) * (t b * b⁻¹)
    calc t (a * b) * (a * b)⁻¹ = t a * ((t b * b⁻¹) * a⁻¹) := by
          rw [map_mul, mul_inv_rev]
          group
      _ = t a * (a⁻¹ * (t b * b⁻¹)) := by rw [hcomm (t b * b⁻¹) a⁻¹]
      _ = (t a * a⁻¹) * (t b * b⁻¹) := by group

variable (hcomm : ∀ a b : E, a * b = b * a) (t : MulAut E)

theorem moveHom_apply (e : E) : moveHom hcomm t e = t e * e⁻¹ := rfl

theorem ker_moveHom : (moveHom hcomm t).ker = autFixed E t := by
  ext e
  rw [MonoidHom.mem_ker, moveHom_apply, mul_inv_eq_one]
  rfl

theorem range_moveHom : (moveHom hcomm t).range = autMoved E t := by
  apply le_antisymm
  · rintro _ ⟨e, rfl⟩
    exact Subgroup.subset_closure ⟨e, rfl⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨e, rfl⟩
    exact ⟨e, rfl⟩

include hcomm in
theorem card_eq_mul [Finite E] :
    Nat.card E = Nat.card (autFixed E t) * Nat.card (autMoved E t) := by
  have h := Subgroup.card_mul_index (moveHom hcomm t).ker
  rw [Subgroup.index_ker, ker_moveHom hcomm t, range_moveHom hcomm t] at h
  exact h.symm

include hcomm in
theorem fixed_inf_moved (hprime : p.Prime) (hp2 : p ≠ 2) (hpow : ∀ a : E, a ^ p = 1)
    (htt : t * t = 1) : autFixed E t ⊓ autMoved E t = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxf, hxm⟩
  rw [← range_moveHom hcomm t] at hxm
  obtain ⟨e, rfl⟩ := hxm
  have htte : t (t e) = e := by simpa using congrArg (fun m : MulAut E => m e) htt
  have h1 : t (moveHom hcomm t e) = (moveHom hcomm t e)⁻¹ := by
    rw [moveHom_apply, map_mul, map_inv, htte, mul_inv_rev, inv_inv, hcomm]
  have h2 : t (moveHom hcomm t e) = moveHom hcomm t e := hxf
  have h3 : moveHom hcomm t e * moveHom hcomm t e = 1 := by
    rw [h2] at h1
    exact mul_eq_one_iff_eq_inv.2 h1
  have h4 : orderOf (moveHom hcomm t e) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  have h5 : orderOf (moveHom hcomm t e) ∣ p := orderOf_dvd_of_pow_eq_one (hpow _)
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hprime).2 (Ne.symm hp2)
  have h6 : orderOf (moveHom hcomm t e) ∣ 1 := hcop ▸ Nat.dvd_gcd h4 h5
  rw [Subgroup.mem_bot]
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h6)

include hcomm in
theorem fixed_sup_moved [Finite E] (hprime : p.Prime) (hp2 : p ≠ 2) (hpow : ∀ a : E, a ^ p = 1)
    (htt : t * t = 1) : autFixed E t ⊔ autMoved E t = ⊤ := by
  have hdisj : Disjoint (autFixed E t) (autMoved E t) :=
    disjoint_iff.2 (fixed_inf_moved hcomm t hprime hp2 hpow htt)
  have hcard := Torsion37.card_sup_of_commute_disjoint (fun k _ l _ => hcomm k l) hdisj
  rw [← Subgroup.card_eq_iff_eq_top, hcard, card_eq_mul hcomm t]

end Reflection

theorem reflection_facts {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) {t : MulAut E} (ht : t ∈ reflectionSet p E) :
    autFixed E t ⊔ autMoved E t = ⊤ ∧ autFixed E t ⊓ autMoved E t = ⊥ ∧
      Nat.card (autMoved E t) = p ∧ Nat.card E = Nat.card (autFixed E t) * p := by
  obtain ⟨⟨hord, hcard⟩, -⟩ := ht
  have hp := h.prime
  have hp2 : p ≠ 2 := by
    have := Sec12Three.five_le h
    omega
  have hcomm : ∀ a b : E, a * b = b * a := fun a b => h.E_elem.is_comm.comm a b
  have hpow : ∀ a : E, a ^ p = 1 := fun a =>
    Subtype.ext (by simpa using Sec12Three.pow_eq_one_of_mem_E h a.2)
  have htt : t * t = 1 := by
    have h2 : t ^ 2 = 1 := hord ▸ pow_orderOf_eq_one t
    rwa [pow_two] at h2
  refine ⟨fixed_sup_moved hcomm t hp hp2 hpow htt, fixed_inf_moved hcomm t hp hp2 hpow htt,
    hcard, ?_⟩
  rw [card_eq_mul hcomm t, hcard]

section Normalizer

variable {G : Type} [Group G]

theorem le_closure_pElements [Finite G] {p : ℕ} (hp : p.Prime) {L : Subgroup G}
    (hq : CFSG.IsQuasisimple L) (hZ : ¬ p ∣ Nat.card (Subgroup.center L)) (hdvd : p ∣ Nat.card L) :
    L ≤ Subgroup.closure {y : G | y ∈ L ∧ y ^ p = 1} := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' p hdvd
  obtain ⟨T, hT⟩ : ∃ T : Set ↥L, T = {y | y ^ p = 1} := ⟨_, rfl⟩
  have hy₀T : y₀ ∈ T := by
    rw [hT]
    exact hy₀ ▸ pow_orderOf_eq_one y₀
  have hNn : (Subgroup.normalClosure T).Normal := Subgroup.normalClosure_normal
  have hNtop : Subgroup.normalClosure T = ⊤ := by
    have hsimple : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2.1
    have hNmap : ((Subgroup.normalClosure T).map
        (QuotientGroup.mk' (Subgroup.center ↥L))).Normal :=
      hNn.map _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((Subgroup.normalClosure T).map (QuotientGroup.mk' (Subgroup.center ↥L))) with hbot | htop
    · exfalso
      have hy₀Z : y₀ ∈ Subgroup.center ↥L := by
        have hmem : QuotientGroup.mk' (Subgroup.center ↥L) y₀ ∈
            (Subgroup.normalClosure T).map (QuotientGroup.mk' (Subgroup.center ↥L)) :=
          ⟨y₀, Subgroup.subset_normalClosure hy₀T, rfl⟩
        rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
        exact hmem
      apply hZ
      have hdvd' := orderOf_dvd_natCard (⟨y₀, hy₀Z⟩ : Subgroup.center ↥L)
      have hord : orderOf (⟨y₀, hy₀Z⟩ : Subgroup.center ↥L) = p := by
        rw [← hy₀, ← Subgroup.orderOf_coe]
      rwa [hord] at hdvd'
    · have hsup : Subgroup.normalClosure T ⊔ Subgroup.center ↥L = ⊤ := by
        rw [eq_top_iff]
        intro a _
        have hmem : QuotientGroup.mk' (Subgroup.center ↥L) a ∈
            (Subgroup.normalClosure T).map (QuotientGroup.mk' (Subgroup.center ↥L)) := by
          rw [htop]
          trivial
        obtain ⟨n, hn, hna⟩ := hmem
        have hz : n⁻¹ * a ∈ Subgroup.center ↥L := by
          rw [← QuotientGroup.eq]
          exact hna
        have ha : a = n * (n⁻¹ * a) := by group
        rw [ha]
        exact Subgroup.mul_mem_sup hn hz
      have hcomm := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
      rw [hq.1.commutator_eq_top] at hcomm
      exact top_le_iff.1 hcomm
  have hconj : Group.conjugatesOfSet T ⊆ T := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hax
    rw [hT] at ha ⊢
    show (c * a * c⁻¹) ^ p = 1
    rw [conj_pow, show a ^ p = 1 from ha, mul_one, mul_inv_cancel]
  have hNle : Subgroup.normalClosure T ≤ Subgroup.closure T := Subgroup.closure_mono hconj
  intro y hy
  have h1 : (⟨y, hy⟩ : ↥L) ∈ Subgroup.closure T := hNle (hNtop ▸ Subgroup.mem_top _)
  have h2 : y ∈ (Subgroup.closure T).map L.subtype := ⟨_, h1, rfl⟩
  rw [MonoidHom.map_closure] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨z, hz, rfl⟩
  rw [hT] at hz
  exact ⟨z.2, by simpa using congrArg Subtype.val (show z ^ p = 1 from hz)⟩

theorem commutator_sup_le_of_central {K Z : Subgroup G}
    (hZ : ∀ z ∈ Z, ∀ w ∈ K ⊔ Z, z * w = w * z) : ⁅K ⊔ Z, K ⊔ Z⁆ ≤ ⁅K, K⁆ := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨k, hk, z, hz, rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute
    (fun k hk z hz => (hZ z hz k (Subgroup.mem_sup_left hk)).symm) hx
  obtain ⟨k', hk', z', hz', rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute
    (fun k hk z hz => (hZ z hz k (Subgroup.mem_sup_left hk)).symm) hy
  have h1 : ⁅z, k' * z'⁆ = 1 := (Commute.commutator_eq (hZ z hz _ hy))
  have h2 : ⁅k, z'⁆ = 1 :=
    Commute.commutator_eq (hZ z' hz' k (Subgroup.mem_sup_left hk)).symm
  rw [commutatorElement_mul_left_eq_conj_mul, h1, commutatorElement_mul_right_eq_mul_conj, h2]
  simp only [mul_one, mul_assoc, mul_inv_cancel, one_mul]
  exact Subgroup.commutator_mem_commutator hk hk'

end Normalizer

section Commute

variable {G : Type} [Group G]

@[expose] def fixSubgroup (E : Subgroup G) (Λ : Subgroup (MulAut E)) : Subgroup ↥E where
  carrier := {e | ∀ φ ∈ Λ, φ e = e}
  mul_mem' ha hb φ hφ := by rw [map_mul, ha φ hφ, hb φ hφ]
  one_mem' φ _ := map_one φ
  inv_mem' ha φ hφ := by rw [map_inv, ha φ hφ]

theorem mem_fixSubgroup {E : Subgroup G} {Λ : Subgroup (MulAut E)} {e : ↥E} :
    e ∈ fixSubgroup E Λ ↔ ∀ φ ∈ Λ, φ e = e :=
  Iff.rfl

theorem eq_top_of_map_subtype_eq {E : Subgroup G} {S : Subgroup ↥E} (h : S.map E.subtype = E) :
    S = ⊤ := by
  rw [eq_top_iff]
  intro e _
  obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.1 (h.ge e.2)
  have : s = e := Subtype.ext hse
  rwa [← this]

variable [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem invariant_cases (h124 : Node124) (h : Sec12Hyp G p A c L E) {S : Subgroup ↥E}
    (hS : ∀ φ ∈ torusImage E L, ∀ s ∈ S, φ s ∈ S) (hS0 : S ≠ ⊥) (hS1 : S ≠ ⊤) :
    S.map E.subtype = Subgroup.zpowers c ∨ S.map E.subtype = ⁅E, L ⊓ torusNormalizer E⁆ := by
  have hS'E : S.map E.subtype ≤ E := Subgroup.map_subtype_le S
  have hinv : torusInvariant E L (S.map E.subtype) := by
    rw [LinAlg.torusInvariant_iff_forall_torusImage L hS'E]
    intro φ hφ b hb
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hb
    exact Subgroup.mem_map.2 ⟨φ s, hS φ hφ s hs, rfl⟩
  refine (h124 G p A c L E h).1 _ hS'E hinv ?_ ?_
  · exact fun hbot => hS0 ((Subgroup.map_eq_bot_iff_of_injective S E.subtype_injective).1 hbot)
  · exact fun heq => hS1 (eq_top_of_map_subtype_eq heq)

theorem fixes_c_of_mem_torusImage (h : Sec12Hyp G p A c L E) (hcE : c ∈ E) {φ : MulAut E}
    (hφ : φ ∈ torusImage E L) : φ ⟨c, hcE⟩ = ⟨c, hcE⟩ := by
  obtain ⟨x, hxL, hxE, rfl⟩ := Sec12Three.mem_torusImage_iff.1 hφ
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  show x * c * x⁻¹ = c
  rw [← Sec12Three.comm_c_L h x hxL]
  group

end Commute

end Sec13Base

theorem node121a_of_hyp :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
      Sec12Hyp G p A c L E → ∀ t ∈ reflectionSet p E,
        E = autFixedInG E t ⊔ autMovedInG E t ∧ autFixedInG E t ⊓ autMovedInG E t = ⊥ ∧
          Nat.card ↥(autMovedInG E t) = p := by
  intro G _ _ p A c L E h t ht
  obtain ⟨hsup, hinf, hcard, -⟩ := Sec13Base.reflection_facts h ht
  have hmap : (⊤ : Subgroup E).map E.subtype = E := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  refine ⟨?_, ?_, ?_⟩
  · unfold autFixedInG autMovedInG
    rw [← Subgroup.map_sup, hsup, hmap]
  · unfold autFixedInG autMovedInG
    rw [← Subgroup.map_inf _ _ _ E.subtype_injective, hinf, Subgroup.map_bot]
  · unfold autMovedInG
    rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact hcard

theorem node134one_of_hyp :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
      Sec12Hyp G p A c L E → ∀ t ∈ reflectionSet p E, ∀ s ∈ reflectionSet p E,
        autFixedInG E t ⊓ autFixedInG E s ≠ ⊥ := by
  intro G _ _ p A c L E h t ht s hs
  obtain ⟨-, -, -, hct⟩ := Sec13Base.reflection_facts h ht
  obtain ⟨-, -, -, hcs⟩ := Sec13Base.reflection_facts h hs
  have hp := h.prime
  have hindex : ∀ {X : Subgroup E}, Nat.card E = Nat.card X * p → X.index = p := fun {X} hX =>
    Nat.eq_of_mul_eq_mul_left Nat.card_pos ((Subgroup.card_mul_index X).trans hX)
  have hXi := hindex hct
  have hYi := hindex hcs
  have hE3 : p ^ 3 ≤ Nat.card E := Nat.le_of_dvd Nat.card_pos h.pow_three_dvd_card_E
  have hcardXY : p ≤ Nat.card ↥(autFixed E t ⊓ autFixed E s) := by
    by_contra hlt
    push Not at hlt
    have h1 := Subgroup.card_mul_index (autFixed E t ⊓ autFixed E s)
    have h2 : (autFixed E t ⊓ autFixed E s).index ≤ p * p := by
      have := Subgroup.index_inf_le (H := autFixed E t) (K := autFixed E s)
      rwa [hXi, hYi] at this
    have h3 : Nat.card ↥(autFixed E t ⊓ autFixed E s) * (autFixed E t ⊓ autFixed E s).index ≤
        (p - 1) * (p * p) := Nat.mul_le_mul (by omega) h2
    have h4 : (p - 1) * (p * p) < p ^ 3 := by
      have : 0 < p := hp.pos
      calc (p - 1) * (p * p) < p * (p * p) := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
        _ = p ^ 3 := by ring
    omega
  intro hbot
  unfold autFixedInG at hbot
  rw [← Subgroup.map_inf _ _ _ E.subtype_injective] at hbot
  have hXY : autFixed E t ⊓ autFixed E s = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ E.subtype_injective).1 hbot
  rw [hXY, Subgroup.card_bot] at hcardXY
  have := hp.two_le
  omega

theorem node136b_of_node122 (h122 : Node122) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
      Sec12Hyp G p A c L E → ¬ p ∣ Nat.card (Subgroup.center L) →
        Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro G _ _ p A c L E h hZ
  have hp := h.prime
  have hG : Sec12TwoGeneric p c L E := (h122 G p A c L E h).resolve_right fun hS =>
    hZ (by rw [hS.center_card, hS.p_eq])
  have hcL : c ∉ L := h.c_not_mem_of_generic hG
  have R := h.restr_of_generic hG
  have hdvd : p ∣ Nat.card L := by
    have hEcard := R.card_E hp (Sec12Three.orderOf_c h) hcL
    have h3 := h.pow_three_dvd_card_E
    rw [hEcard] at h3
    have h4 : p ^ 2 ∣ Nat.card ↥(E ⊓ L) := by
      have : p * p ^ 2 ∣ p * Nat.card ↥(E ⊓ L) := by
        rw [← pow_succ', mul_comm]
        exact h3
      exact Nat.dvd_of_mul_dvd_mul_left hp.pos this
    exact ((dvd_pow_self p (by norm_num)).trans h4).trans
      (Subgroup.card_dvd_of_le inf_le_right)
  obtain ⟨S, hS⟩ : ∃ S : Set G, S = {x | x ∈ Subgroup.centralizer ({c} : Set G) ∧ x ^ p = 1} :=
    ⟨_, rfl⟩
  have hPM : Subgroup.closure S ≤ Subgroup.zpowers c ⊔ L := by
    refine (Subgroup.closure_le _).2 ?_
    rw [hS]
    rintro x ⟨hxc, hxp⟩
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · have : Fact p.Prime := ⟨hp⟩
      have hord : orderOf x = p := orderOf_eq_prime hxp hx1
      have hxN : x ∈ cNormalizer c := by
        refine Subgroup.centralizer_le_normalizer _ ?_
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        have hcx : c * x = x * c := (Subgroup.mem_centralizer_singleton_iff.1 hxc).symm
        exact (Commute.zpow_left (hcx : Commute c x) j).eq
      exact hG.pElements x hxN hord
  have hLP : L ≤ Subgroup.closure S := by
    refine (Sec13Base.le_closure_pElements hp hG.quasisimple hZ hdvd).trans
      (Subgroup.closure_mono ?_)
    rw [hS]
    rintro y ⟨hyL, hyp⟩
    exact ⟨Subgroup.mem_centralizer_singleton_iff.2 (Sec12Three.comm_c_L h y hyL).symm, hyp⟩
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.1 hG.quasisimple.1
  have hZc : ∀ z ∈ Subgroup.zpowers c, ∀ w ∈ L ⊔ Subgroup.zpowers c, z * w = w * z := by
    intro z hz w hw
    obtain ⟨l, hl, z', hz', rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute
      (fun l hl z hz => (Sec12Three.zpowers_comm_L h z hz l hl).symm) hw
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
    rw [← mul_assoc, (Sec12Three.zpowers_comm_L h _ hz l hl), mul_assoc, mul_assoc,
      (Commute.zpow_zpow_self c i j).eq]
  have hPP : ⁅Subgroup.closure S, Subgroup.closure S⁆ = L := by
    apply le_antisymm
    · calc ⁅Subgroup.closure S, Subgroup.closure S⁆
          ≤ ⁅L ⊔ Subgroup.zpowers c, L ⊔ Subgroup.zpowers c⁆ :=
            Subgroup.commutator_mono (hPM.trans_eq (sup_comm _ _)) (hPM.trans_eq (sup_comm _ _))
        _ ≤ ⁅L, L⁆ := Sec13Base.commutator_sup_le_of_central hZc
        _ = L := hperf
    · calc L = ⁅L, L⁆ := hperf.symm
        _ ≤ ⁅Subgroup.closure S, Subgroup.closure S⁆ := Subgroup.commutator_mono hLP hLP
  have hconjP : ∀ g ∈ Subgroup.centralizer ({c} : Set G),
      (Subgroup.closure S).map (MulAut.conj g).toMonoidHom ≤ Subgroup.closure S := by
    intro g hg
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rw [hS]
    rintro y ⟨hyc, hyp⟩
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · exact (Subgroup.centralizer ({c} : Set G)).mul_mem
        ((Subgroup.centralizer ({c} : Set G)).mul_mem hg hyc)
        ((Subgroup.centralizer ({c} : Set G)).inv_mem hg)
    · show (g * y * g⁻¹) ^ p = 1
      rw [conj_pow, hyp, mul_one, mul_inv_cancel]
  have hconjL : ∀ g ∈ Subgroup.centralizer ({c} : Set G),
      L.map (MulAut.conj g).toMonoidHom ≤ L := by
    intro g hg
    rw [← hPP, Subgroup.map_commutator]
    exact Subgroup.commutator_mono (hconjP g hg) (hconjP g hg)
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro l
  constructor
  · intro hl
    exact hconjL x hx ⟨l, hl, rfl⟩
  · intro hl
    have := hconjL x⁻¹ ((Subgroup.centralizer ({c} : Set G)).inv_mem hx) ⟨x * l * x⁻¹, hl, rfl⟩
    simpa [mul_assoc] using this

theorem node138b_of_inputs (h124 : Node124) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
      Sec12Hyp G p A c L E → ∀ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)),
        w ∉ cNormalizer c → ∃ x ∈ torusImage E L, ∃ y ∈ torusImage E L,
          x * (E.normalizerMonoidHom ⟨w, hw⟩ * y * (E.normalizerMonoidHom ⟨w, hw⟩)⁻¹) ≠
            (E.normalizerMonoidHom ⟨w, hw⟩ * y * (E.normalizerMonoidHom ⟨w, hw⟩)⁻¹) * x := by
  intro G _ _ p A c L E h w hw hwH
  have hp := h.prime
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hc1 : (⟨c, hcE⟩ : ↥E) ≠ 1 := fun h1 => h.c_ne_one (congrArg Subtype.val h1)
  by_contra hcon
  push Not at hcon
  obtain ⟨ω, hωdef⟩ : ∃ ω : MulAut ↥E, ω = E.normalizerMonoidHom ⟨w, hw⟩ := ⟨_, rfl⟩
  rw [← hωdef] at hcon
  have hEcard3 : p ^ 3 ≤ Nat.card E := Nat.le_of_dvd Nat.card_pos h.pow_three_dvd_card_E
  have hpos : 0 < p := hp.pos
  obtain ⟨B, hBdef⟩ : ∃ B : Subgroup G, B = ⁅E, L ⊓ torusNormalizer E⁆ := ⟨_, rfl⟩
  have hBE : B ≤ E := hBdef ▸ Sec12Three.commutator_le_left E L
  have hBdata : (Subgroup.zpowers c ⊓ B = ⊥ ∨ B = E) ∧ p ^ 2 ≤ Nat.card B := by
    rcases (h124 G p A c L E h).2 with ⟨hsup, hinf⟩ | ⟨-, hBE'⟩
    · rw [← hBdef] at hsup hinf
      refine ⟨Or.inl hinf, ?_⟩
      have hcomm : ∀ k ∈ Subgroup.zpowers c, ∀ l ∈ B, k * l = l * k :=
        fun k hk l hl => zpowers_comm_E h k hk l (hBE hl)
      have hcard := card_sup_of_commute_disjoint hcomm (disjoint_iff.2 hinf)
      rw [← hsup, Nat.card_zpowers, Sec12Three.orderOf_c h] at hcard
      have : p * p ^ 2 ≤ p * Nat.card B := by
        calc p * p ^ 2 = p ^ 3 := by ring
          _ ≤ Nat.card E := hEcard3
          _ = _ := hcard
      exact Nat.le_of_mul_le_mul_left this hpos
    · rw [← hBdef] at hBE'
      refine ⟨Or.inr hBE', ?_⟩
      rw [hBE']
      exact le_trans (Nat.pow_le_pow_right hpos (by norm_num)) hEcard3
  have hB0 : B ≠ ⊥ := by
    intro hbot
    have h2 := hBdata.2
    rw [hbot, Subgroup.card_bot] at h2
    have := hp.two_le
    nlinarith
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup ↥E, C = Sec13Base.fixSubgroup E (torusImage E L) :=
    ⟨_, rfl⟩
  have hcC : (⟨c, hcE⟩ : ↥E) ∈ C := by
    rw [hCdef, Sec13Base.mem_fixSubgroup]
    intro φ hφ
    exact Sec13Base.fixes_c_of_mem_torusImage h hcE hφ
  have hC0 : C ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hcC
    exact hc1 hcC
  have hCtop : C ≠ ⊤ := by
    intro htop
    apply hB0
    rw [hBdef, eq_bot_iff, Subgroup.commutator_le]
    intro e he l hl
    obtain ⟨hlL, hlW⟩ := Subgroup.mem_inf.1 hl
    have hφ : E.normalizerMonoidHom ⟨l, hlW⟩ ∈ torusImage E L :=
      Subgroup.mem_map.2 ⟨⟨l, hlW⟩, hlL, rfl⟩
    have hfix : E.normalizerMonoidHom ⟨l, hlW⟩ ⟨e, he⟩ = ⟨e, he⟩ := by
      have hmem : (⟨e, he⟩ : ↥E) ∈ C := htop ▸ Subgroup.mem_top _
      rw [hCdef, Sec13Base.mem_fixSubgroup] at hmem
      exact hmem _ hφ
    have hlel : l * e * l⁻¹ = e := by
      have := congrArg Subtype.val hfix
      rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at this
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (mul_inv_eq_iff_eq_mul.1 hlel).symm
  have hCinv : ∀ φ ∈ torusImage E L, ∀ s ∈ C, φ s ∈ C := by
    intro φ hφ s hs
    have hφs : φ s = s := by
      rw [hCdef] at hs
      exact hs φ hφ
    rw [hφs]
    exact hs
  have hCsub : C.map E.subtype = Subgroup.zpowers c := by
    rcases Sec13Base.invariant_cases h124 h hCinv hC0 hCtop with hc | hc
    · exact hc
    · exfalso
      have hcB : c ∈ B := by
        rw [hBdef, ← hc]
        exact ⟨⟨c, hcE⟩, hcC, rfl⟩
      rcases hBdata.1 with hinf | hBE'
      · have hmem : c ∈ Subgroup.zpowers c ⊓ B := ⟨Subgroup.mem_zpowers c, hcB⟩
        rw [hinf, Subgroup.mem_bot] at hmem
        exact h.c_ne_one hmem
      · apply hCtop
        apply Sec13Base.eq_top_of_map_subtype_eq
        rw [hc, ← hBdef, hBE']
  have hCcard : Nat.card C = p := by
    rw [← Subgroup.card_map_of_injective E.subtype_injective, hCsub, Nat.card_zpowers,
      Sec12Three.orderOf_c h]
  obtain ⟨D, hDdef⟩ : ∃ D : Subgroup ↥E, D = C.map ω.toMonoidHom := ⟨_, rfl⟩
  have hDcard : Nat.card D = p := by
    rw [hDdef, Subgroup.card_map_of_injective ω.injective, hCcard]
  have hDinv : ∀ x ∈ torusImage E L, ∀ s ∈ D, x s ∈ D := by
    intro x hx s hs
    rw [hDdef] at hs ⊢
    obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.1 hs
    refine Subgroup.mem_map.2 ⟨(ω⁻¹ * x * ω) c', ?_, ?_⟩
    · rw [hCdef, Sec13Base.mem_fixSubgroup] at hc' ⊢
      intro z hz
      have hcomm := hcon x hx z hz
      have h1 : z * (ω⁻¹ * x * ω) = (ω⁻¹ * x * ω) * z := by
        calc z * (ω⁻¹ * x * ω) = ω⁻¹ * ((ω * z * ω⁻¹) * x) * ω := by group
          _ = ω⁻¹ * (x * (ω * z * ω⁻¹)) * ω := by rw [hcomm]
          _ = (ω⁻¹ * x * ω) * z := by group
      calc z ((ω⁻¹ * x * ω) c') = (z * (ω⁻¹ * x * ω)) c' := rfl
        _ = ((ω⁻¹ * x * ω) * z) c' := by rw [h1]
        _ = (ω⁻¹ * x * ω) (z c') := rfl
        _ = (ω⁻¹ * x * ω) c' := by rw [hc' z hz]
    · show ω ((ω⁻¹ * x * ω) c') = x (ω c')
      have h2 : ω * (ω⁻¹ * x * ω) = x * ω := by group
      calc ω ((ω⁻¹ * x * ω) c') = (ω * (ω⁻¹ * x * ω)) c' := rfl
        _ = (x * ω) c' := by rw [h2]
        _ = x (ω c') := rfl
  have hD0 : D ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hDcard
    have := hp.two_le
    omega
  have hDtop : D ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.card_top] at hDcard
    have := hp.two_le
    nlinarith
  rcases Sec13Base.invariant_cases h124 h hDinv hD0 hDtop with hc | hc
  · have hωc : ((ω ⟨c, hcE⟩ : ↥E) : G) ∈ Subgroup.zpowers c := by
      rw [← hc]
      refine Subgroup.mem_map.2 ⟨ω ⟨c, hcE⟩, ?_, rfl⟩
      rw [hDdef]
      exact Subgroup.mem_map.2 ⟨⟨c, hcE⟩, hcC, rfl⟩
    rw [hωdef, Subgroup.normalizerMonoidHom_apply_apply_coe] at hωc
    exact hwH (Sec127.mem_cNormalizer_of_conj_mem hωc)
  · have h1 : Nat.card B = p := by
      rw [hBdef, ← hc, Subgroup.card_map_of_injective E.subtype_injective, hDcard]
    have h2 := hBdata.2
    rw [h1] at h2
    have := hp.two_le
    nlinarith

end CFSG.RankThree.PartOne
