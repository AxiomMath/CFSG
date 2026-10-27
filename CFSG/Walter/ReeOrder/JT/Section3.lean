module

public import CFSG.Walter.ReeOrder.JT.Section2

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise

theorem mem_of_normal_of_odd_index {G : Type*} [Group G] {H : Subgroup G} (hH : H.Normal)
    (hodd : Odd H.index) {x : G} {n : ℕ} (hx : orderOf x = 2 ^ n) : x ∈ H := by
  have h1 : orderOf (QuotientGroup.mk x : G ⧸ H) ∣ 2 ^ n :=
    hx ▸ orderOf_map_dvd (QuotientGroup.mk' H) x
  have h2 : orderOf (QuotientGroup.mk x : G ⧸ H) ∣ H.index := by
    rw [Subgroup.index]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (QuotientGroup.mk x : G ⧸ H) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1
      (Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd))) h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

namespace JTHyp

variable {G : Type} [Group G] [Finite G] (h : JTHyp G)

theorem even_card_F
    (hp : h.p ≠ 2) : Even (Nat.card h.F) := by
  obtain ⟨U, w, hU, -⟩ := (h.facts hp).odd_torus
  have hw : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hU.w_mul_self)
    (fun h0 => hU.w_not_mem (h0 ▸ U.one_mem))
  rw [even_iff_two_dvd, ← hw]
  exact Subgroup.orderOf_dvd_natCard _ hU.w_mem

theorem inf_centralizer_eq_bot
    (hp : h.p ≠ 2) {K : Subgroup G} (hK : K.Normal)
    (hodd : Odd (Nat.card K)) : K ⊓ Subgroup.centralizer ({h.t} : Set G) = ⊥ := by
  set K' := K ⊓ Subgroup.centralizer ({h.t} : Set G)
  have hK'odd : Odd (Nat.card K') := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left)
  have hK'F : K' ≤ h.F := h.le_F_of_odd inf_le_right hK'odd
  have hnorm : (K'.subgroupOf h.F).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨hK.conj_mem _ hx.1 _, Subgroup.mul_mem _ (Subgroup.mul_mem _
      (h.le_centralizer g.2) hx.2) (Subgroup.inv_mem _ (h.le_centralizer g.2))⟩
  have := (h.facts hp).simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K'.subgroupOf h.F) with h1 | h1
  · rw [Subgroup.subgroupOf_eq_bot] at h1
    rw [← inf_eq_left.mpr hK'F]
    exact disjoint_iff.mp h1
  · exfalso
    rw [Subgroup.subgroupOf_eq_top] at h1
    have := Odd.of_dvd_nat hK'odd (Subgroup.card_dvd_of_le h1)
    exact (Nat.not_even_iff_odd.mpr this) (h.even_card_F hp)

theorem eq_bot_of_normal_of_odd
    (hp : h.p ≠ 2) {K : Subgroup G} (hK : K.Normal)
    (hodd : Odd (Nat.card K)) : K = ⊥ := by
  obtain ⟨U, w, hU, -⟩ := (h.facts hp).odd_torus
  have hw1 : w ≠ 1 := fun h0 => hU.w_not_mem (h0 ▸ U.one_mem)
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hU.w_mul_self) hw1
  have htw : h.t ≠ w := fun h0 => h.t_not_mem (h0 ▸ hU.w_mem)
  have hcw : Commute h.t w := (h.commute_of_mem_F hU.w_mem).symm
  have hinv : ∀ u : G, orderOf u = 2 → K ⊓ Subgroup.centralizer ({u} : Set G) = ⊥ := by
    intro u hu
    obtain ⟨g, hg⟩ := h.exists_conj_eq_t hp hu
    have h' := (h.conj g⁻¹).inf_centralizer_eq_bot hp hK hodd
    rw [JTHyp.conj_t, ← hg] at h'
    simpa [mul_assoc] using h'
  have htw2 : orderOf (h.t * w) = 2 := by
    refine orderOf_eq_prime ?_ (fun h0 => htw ?_)
    · rw [pow_two, mul_assoc, ← mul_assoc w, ← hcw.eq, ← mul_assoc, ← mul_assoc, h.t_mul_t,
        one_mul, hU.w_mul_self]
    · rw [← mul_one h.t, ← h0, ← mul_assoc, h.t_mul_t, one_mul]
  have hN := Subgroup.normalizer_eq_top_iff.mpr hK
  have hBW := card_mul_card_sq_eq_mul h.t_mul_t hU.w_mul_self h.t_ne_one hw1 htw hcw K
    (by rw [hN]; trivial) (by rw [hN]; trivial) hodd
  rw [hinv _ h.orderOf_t, hinv _ hw2, hinv _ htw2, bot_inf_eq, Subgroup.card_bot] at hBW
  simpa using hBW

@[expose] noncomputable def restrict (H : Subgroup G)
    (hCH : Subgroup.centralizer ({h.t} : Set G) ≤ H) (hH : ∀ K : Subgroup H, K.index ≠ 2) :
    JTHyp H where
  p := h.p
  f := h.f
  five_lt := h.five_lt
  abelian_sylow := fun P => by
    obtain ⟨S, hS⟩ := (P.isPGroup'.map H.subtype).exists_le_sylow
    have hab := h.abelian_sylow S
    refine ⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩
    have := hab.is_comm.comm ⟨((a : H) : G), hS ⟨a, a.2, rfl⟩⟩ ⟨((b : H) : G), hS ⟨b, b.2, rfl⟩⟩
    have h2 := congrArg Subtype.val this
    exact h2
  index_ne_two := hH
  t := ⟨h.t, hCH h.t_mem_centralizer⟩
  orderOf_t := by rw [Subgroup.orderOf_mk, h.orderOf_t]
  F := h.F.subgroupOf H
  le_centralizer := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (Subtype.ext (h.commute_of_mem_F hx))
  t_not_mem := fun ht => h.t_not_mem ht
  centralizer_eq := by
    apply le_antisymm
    · intro x hx
      have hxC : (x : G) ∈ Subgroup.centralizer ({h.t} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hx))
      rcases h.mem_centralizer_t.mp hxC with hxF | hxF
      · exact Subgroup.mem_sup_right hxF
      · set t' : H := ⟨h.t, hCH h.t_mem_centralizer⟩
        have : x = t'⁻¹ * (t' * x) := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.inv_mem _
          (Subgroup.mem_zpowers _))) (Subgroup.mem_sup_right hxF)
    · refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
      · intro x hx
        exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext (h.commute_of_mem_F hx))
  iso := (Subgroup.subgroupOfEquivOfLe (h.le_centralizer.trans hCH)).trans h.iso

@[simp] theorem restrict_p (H : Subgroup G) (hCH) (hH) : (h.restrict H hCH hH).p = h.p := rfl

@[simp] theorem restrict_t (H : Subgroup G) (hCH) (hH) :
    ((h.restrict H hCH hH).t : G) = h.t := rfl

theorem centralizer_le_of_normal_of_odd_index
    (hp : h.p ≠ 2) {H : Subgroup G} (hH : H.Normal)
    (hodd : Odd H.index) : Subgroup.centralizer ({h.t} : Set G) ≤ H := by
  have htH : h.t ∈ H := mem_of_normal_of_odd_index hH hodd (n := 1) (by rw [h.orderOf_t]; rfl)
  obtain ⟨U, w, hU, -⟩ := (h.facts hp).odd_torus
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hU.w_mul_self)
    (fun h0 => hU.w_not_mem (h0 ▸ U.one_mem))
  have hwH : w ∈ H := mem_of_normal_of_odd_index hH hodd (n := 1) (by rw [hw2]; rfl)
  have := (h.facts hp).simple
  have hnorm : ((h.F ⊓ H).subgroupOf h.F).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hx.1) (Subgroup.inv_mem _ g.2),
      hH.conj_mem _ hx.2 _⟩
  have hFH : h.F ≤ H := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((h.F ⊓ H).subgroupOf h.F) with h1 | h1
    · exfalso
      rw [Subgroup.subgroupOf_eq_bot] at h1
      have : w ∈ (h.F ⊓ H) ⊓ h.F := ⟨⟨hU.w_mem, hwH⟩, hU.w_mem⟩
      rw [disjoint_iff.mp h1] at this
      exact hU.w_not_mem ((Subgroup.mem_bot.mp this) ▸ U.one_mem)
    · rw [Subgroup.subgroupOf_eq_top] at h1
      exact h1.trans inf_le_right
  rw [h.centralizer_eq]
  exact sup_le ((Subgroup.zpowers_le).mpr htH) hFH

theorem index_ne_two_of_normal_of_odd_index
    (hp : h.p ≠ 2) {H : Subgroup G} (hH : H.Normal)
    (hodd : Odd H.index) (K : Subgroup H) : K.index ≠ 2 := by
  classical
  intro hK2
  set K' := K.map H.subtype
  set D := K'.normalCore
  have hDK' : D ≤ K' := K'.normalCore_le
  have hK'H : K' ≤ H := Subgroup.map_subtype_le K
  have hDH : D ≤ H := hDK'.trans hK'H
  have hsq : ∀ x ∈ H, x * x ∈ D := by
    intro x hx b
    have hy : b * x * b⁻¹ ∈ H := hH.conj_mem x hx b
    have h1 := Subgroup.mul_self_mem_of_index_two hK2 ⟨b * x * b⁻¹, hy⟩
    refine ⟨_, h1, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul]
    group
  rcases Nat.even_or_odd (Nat.card D) with hDe | hDo
  ·
    obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 hDe.two_dvd
    have hd2 : orderOf (d : G) = 2 := by rw [Subgroup.orderOf_coe, hd]
    have ht2 : IsPGroup 2 (Subgroup.zpowers h.t) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, h.orderOf_t, pow_one])
    obtain ⟨S, hS⟩ := ht2.exists_le_sylow
    have htS : h.t ∈ S := hS (Subgroup.mem_zpowers _)
    have hSD : (S : Subgroup G) ≤ D := by
      intro s hs
      by_cases hs1 : s = 1
      · rw [hs1]
        exact D.one_mem
      have hs2 : orderOf s = 2 := orderOf_eq_prime
        (by rw [pow_two]; exact h.mul_self_of_mem_sylow hp S htS hs) hs1
      obtain ⟨g, hg⟩ := isConj_iff.mp (h.isConj_of_orderOf_eq_two hp hd2 hs2)
      rw [← hg]
      exact (Subgroup.normalCore_normal K').conj_mem _ d.2 g
    have hSH : (S : Subgroup G) ≤ H := hSD.trans hDH
    have hQ : IsPGroup 2 (H ⧸ D.subgroupOf H) := by
      intro x
      refine ⟨1, ?_⟩
      induction x using QuotientGroup.induction_on with
      | H y =>
        rw [pow_one, pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff,
          Subgroup.mem_subgroupOf]
        exact hsq y y.2
    obtain ⟨n, hn⟩ := hQ.exists_card_eq
    have hidx : (D.subgroupOf H).index = 2 ^ n := by rw [Subgroup.index, hn]
    have hdvd : (D.subgroupOf H).index ∣ (S : Subgroup G).index :=
      (Subgroup.index_dvd_of_le (fun x hx => hSD hx :
        (S : Subgroup G).subgroupOf H ≤ D.subgroupOf H)).trans
        (Subgroup.relIndex_dvd_index_of_le hSH)
    have hn0 : n = 0 := by
      by_contra hn0
      apply S.not_dvd_index
      exact (dvd_pow_self 2 hn0).trans (hidx ▸ hdvd)
    rw [hn0, pow_zero, Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at hidx
    have hKtop : K = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨y, hy, hyx⟩ := hDK' (hidx x.2)
      rw [← Subtype.ext hyx]
      exact hy
    rw [hKtop, Subgroup.index_top] at hK2
    omega
  ·
    have hD1 : D = ⊥ := h.eq_bot_of_normal_of_odd hp (Subgroup.normalCore_normal K') hDo
    have hF := h.facts hp
    have hpF : h.p ∣ Nat.card h.F := by
      rw [hF.card]
      have h2 : 2 ∣ (h.p ^ h.f) ^ 2 - 1 := by
        have := Nat.odd_iff.mp (hF.odd_p.pow (n := h.f))
        have : (h.p ^ h.f) ^ 2 % 2 = 1 := by
          rw [Nat.pow_mod, this]
        omega
      rw [Nat.mul_div_assoc _ h2]
      exact (dvd_pow_self h.p hF.pos.ne').mul_right _
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := h.F) h.p hpF
    have hxH : (x : G) ∈ H := h.centralizer_le_of_normal_of_odd_index hp hH hodd
      (h.le_centralizer x.2)
    have hxx := hsq _ hxH
    rw [hD1, Subgroup.mem_bot] at hxx
    have h2 : orderOf (x : G) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hxx)
    rw [Subgroup.orderOf_coe, hx] at h2
    exact hp (le_antisymm (Nat.le_of_dvd (by norm_num) h2) hF.prime.two_le)

theorem eq_top_of_normal_of_odd_index
    (hp : h.p ≠ 2) {H : Subgroup G} (hH : H.Normal)
    (hodd : Odd H.index) : H = ⊤ := by
  have hCH := h.centralizer_le_of_normal_of_odd_index hp hH hodd
  set h' := h.restrict H hCH (h.index_ne_two_of_normal_of_odd_index hp hH hodd)
  rw [eq_top_iff]
  intro g _
  have hx2 : orderOf (g * h.t * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h.orderOf_t]
  have hxH : g * h.t * g⁻¹ ∈ H := mem_of_normal_of_odd_index hH hodd (n := 1)
    (by rw [hx2]; rfl)
  obtain ⟨k, hk⟩ := h'.exists_conj_eq_t hp (x := ⟨_, hxH⟩) (by rw [Subgroup.orderOf_mk, hx2])
  have hk' : (k : G) * (g * h.t * g⁻¹) * (k : G)⁻¹ = h.t := congrArg Subtype.val hk
  have hkg : (k : G) * g ∈ Subgroup.centralizer ({h.t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (k : G) * g * h.t = ((k : G) * (g * h.t * g⁻¹) * (k : G)⁻¹) * (k * g) := by group
      _ = h.t * (k * g) := by rw [hk']
  have : g = (k : G)⁻¹ * ((k : G) * g) := by group
  rw [this]
  exact H.mul_mem (H.inv_mem k.2) (hCH hkg)

end JTHyp

theorem lemma_3_1
    {G : Type} [Group G] [Finite G] (h : JTHyp G) (hp : h.p ≠ 2) :
    IsSimpleGroup G := by
  have : Nontrivial G := ⟨⟨h.t, 1, h.t_ne_one⟩⟩
  refine ⟨fun L hL => ?_⟩
  rcases Nat.even_or_odd (Nat.card L) with he | ho
  · right
    obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := L) 2 he.two_dvd
    have hd2 : orderOf (d : G) = 2 := by rw [Subgroup.orderOf_coe, hd]
    have ht2 : IsPGroup 2 (Subgroup.zpowers h.t) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, h.orderOf_t, pow_one])
    obtain ⟨S, hS⟩ := ht2.exists_le_sylow
    have htS : h.t ∈ S := hS (Subgroup.mem_zpowers _)
    have hSL : (S : Subgroup G) ≤ L := by
      intro s hs
      by_cases hs1 : s = 1
      · rw [hs1]
        exact L.one_mem
      have hs2 : orderOf s = 2 := orderOf_eq_prime
        (by rw [pow_two]; exact h.mul_self_of_mem_sylow hp S htS hs) hs1
      obtain ⟨g, hg⟩ := isConj_iff.mp (h.isConj_of_orderOf_eq_two hp hd2 hs2)
      rw [← hg]
      exact hL.conj_mem _ d.2 g
    refine h.eq_top_of_normal_of_odd_index hp hL ?_
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact fun h2 => S.not_dvd_index (h2.trans (Subgroup.index_dvd_of_le hSL))
  · left
    exact h.eq_bot_of_normal_of_odd hp hL ho

end CFSG.Walter.JT
