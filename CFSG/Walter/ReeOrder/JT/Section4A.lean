module

public import CFSG.Walter.ReeOrder.JT.Section2

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise

section General

variable {X : Type*} [Group X]

theorem exists_oddPart_of_cyclic [Finite X] {U : Subgroup X} (hU : IsCyclic U) {m : ℕ}
    (hm : Odd m) (hUm : Nat.card U = 2 * m) :
    ∃ Q : Subgroup X, Q ≤ U ∧ IsCyclic Q ∧ Nat.card Q = m ∧
      ∀ x ∈ U, Odd (orderOf x) → x ∈ Q := by
  obtain ⟨g, hg⟩ := hU.exists_generator
  have hgo : orderOf (g : X) = 2 * m := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hUm]
  refine ⟨Subgroup.zpowers ((g : X) ^ 2), (Subgroup.zpowers_le).mpr (U.pow_mem g.2 2),
    inferInstance, ?_, ?_⟩
  · rw [Nat.card_zpowers, orderOf_pow' _ (by norm_num), hgo]
    have : Nat.gcd (2 * m) 2 = 2 := Nat.gcd_eq_right (dvd_mul_right 2 m)
    rw [this]
    omega
  · intro x hx hodd
    obtain ⟨k, hk⟩ := hg ⟨x, hx⟩
    have hk' : (g : X) ^ k = x := congrArg Subtype.val hk
    have hxm : x ^ m = 1 := by
      have h1 : orderOf x ∣ 2 * m := hUm ▸ Subgroup.orderOf_dvd_natCard U hx
      have h2 : orderOf x ∣ m :=
        (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hodd) h1)
      exact orderOf_dvd_iff_pow_eq_one.mp h2
    obtain ⟨j, hj⟩ := hm
    have : x = ((g : X) ^ 2) ^ (k * (j + 1)) := by
      calc x = x ^ (m + 1) := by rw [pow_succ, hxm, one_mul]
        _ = ((g : X) ^ k) ^ (m + 1) := by rw [hk']
        _ = ((g : X) ^ 2) ^ (k * (j + 1)) := by
          rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast (g : X) 2, ← zpow_mul, hj]
          congr 1
          push_cast
          ring
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _

theorem oddCoreOf_eq_of [Finite X] {H N : Subgroup X} (hNH : N ≤ H)
    (hnorm : (N.subgroupOf H).Normal) (hodd : Odd (Nat.card N))
    (hall : ∀ x ∈ H, Odd (orderOf x) → x ∈ N) : GorensteinWalter.oddCoreOf H = N := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    refine hall _ y.2 ?_
    change Odd (orderOf (y : X))
    have h1 : orderOf y ∣ Nat.card (pPrimeCore 2 H) := Subgroup.orderOf_dvd_natCard _ hy
    have h2 := pPrimeCore_coprime_card (p := 2) (G := H)
    rw [Subgroup.orderOf_coe]
    exact Nat.odd_iff.mpr (by
      have := Nat.Coprime.coprime_dvd_right h1 h2
      rw [Nat.coprime_two_left] at this
      exact Nat.odd_iff.mp this)
  · intro x hx
    have hmem : N.subgroupOf H ≤ pPrimeCore 2 H := le_sSup ⟨hnorm, by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv, Nat.coprime_two_left]
      exact hodd⟩
    exact ⟨⟨x, hNH hx⟩, hmem (by rw [Subgroup.mem_subgroupOf]; exact hx), rfl⟩

theorem eq_of_orderOf_eq_two_of_isCyclic [Finite X] {U : Subgroup X} (hU : IsCyclic U)
    {a b : X} (ha : a ∈ U) (hb : b ∈ U) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) :
    a = b := by
  have ha' : orderOf (⟨a, ha⟩ : U) = 2 := by rw [Subgroup.orderOf_mk, ha2]
  have hb' : orderOf (⟨b, hb⟩ : U) = 2 := by rw [Subgroup.orderOf_mk, hb2]
  have heq : Subgroup.zpowers (⟨a, ha⟩ : U) = Subgroup.zpowers ⟨b, hb⟩ :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [Nat.card_zpowers, Nat.card_zpowers, ha', hb'])
  have hmem : (⟨a, ha⟩ : U) ∈ Subgroup.zpowers ⟨b, hb⟩ := heq ▸ Subgroup.mem_zpowers _
  rcases (mem_zpowers_of_orderOf_eq_two hb').mp hmem with h1 | h1
  · rw [h1, orderOf_one] at ha'
    omega
  · exact congrArg Subtype.val h1

theorem card_eq_two_mul_of_xor {H K : Subgroup X} (hHK : H ≤ K) {a : X} (haK : a ∈ K)
    (hxor : ∀ b ∈ K, (b * a ∈ H ↔ b ∉ H)) : Nat.card K = 2 * Nat.card H := by
  have hidx : H.relIndex K = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨a, haK⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    have := hxor b b.2
    by_cases hb : (b : X) ∈ H
    · exact Or.inr ⟨hb, fun h1 => (this.mp h1) hb⟩
    · exact Or.inl ⟨this.mpr hb, hb⟩
  have h1 := Subgroup.relIndex_mul_card H K
  rw [hidx, inf_eq_left.mpr hHK] at h1
  exact h1.symm

theorem TorusData.conj_eq {L U : Subgroup X} {w : X} (hU : TorusData L U w) {y : X}
    (hy : y ∈ U ⊔ Subgroup.zpowers w) {x : X} (hx : x ∈ U) :
    (y ∈ U ∧ y * x * y⁻¹ = x) ∨ (y * w ∈ U ∧ y * x * y⁻¹ = x⁻¹) := by
  have hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb => by
    have := hU.cyclic
    have := (IsCyclic.commGroup (α := U)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hU.w_mul_self
  rcases hU.mem_sup_iff.mp hy with hyU | hyU
  · left
    exact ⟨hyU, by rw [hcomm y hyU x hx, mul_inv_cancel_right]⟩
  · right
    refine ⟨hyU, ?_⟩
    have hy' : y = (y * w) * w := by rw [mul_assoc, hU.w_mul_self, mul_one]
    rw [hy', mul_inv_rev, show (y * w) * w * x * (w⁻¹ * (y * w)⁻¹) =
      (y * w) * (w * x * w⁻¹) * (y * w)⁻¹ by group, hU.inv x hx,
      hcomm _ hyU _ (U.inv_mem hx), mul_inv_cancel_right]

end General

theorem lemma_4_1
    {G : Type} [Group G] [Finite G] (h : JTHyp G) (hp : h.p ≠ 2)
    (h3 : ∃ k, h.q = 3 ^ k) : ∃ n, 1 ≤ n ∧ h.q = 3 ^ (2 * n + 1) := by
  obtain ⟨k, hk⟩ := h3
  have h8 := h.mod_eight hp
  have h5 := h.five_lt
  rcases Nat.even_or_odd k with ⟨n, hn⟩ | ⟨n, hn⟩
  · exfalso
    have : h.q % 8 = 1 := by
      rw [hk, hn, ← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    omega
  · refine ⟨n, ?_, hn ▸ hk⟩
    by_contra hn0
    have : n = 0 := by omega
    rw [this] at hn
    rw [JTHyp.q_eq] at hk
    rw [hk, hn] at h5
    norm_num at h5

structure Setup {G : Type} [Group G] [Finite G] (h : JTHyp G) where
  S : Sylow 2 G
  t_mem_S : h.t ∈ S
  T : Subgroup G
  le_S : T ≤ S
  four : IsKleinFour T
  t_mem_T : h.t ∈ T

namespace Setup

variable {G : Type} [Group G] [Finite G] {h : JTHyp G} (s : Setup h)

@[expose] noncomputable def Q : Subgroup G :=
  GorensteinWalter.oddCoreOf (Subgroup.centralizer (s.T : Set G))

structure Data where
  v : G
  U : Subgroup G
  w : G
  v_mem_F : v ∈ h.F
  v_ne_one : v ≠ 1
  mem_T : ∀ x, x ∈ s.T ↔ x = h.t * v ∨ x = h.t ∨ x = v ∨ x = 1
  torus : TorusData h.F U w
  v_mem_U : v ∈ U
  two_mul_card_U : 2 * (Nat.card U : ℤ) = h.q + h.eps

theorem nonempty_data
    (hp : h.p ≠ 2) : Nonempty s.Data := by
  classical
  have hT := s.four
  have hTS : s.T ≤ (s.S : Subgroup G) := s.le_S
  obtain ⟨τ, hτT, hτ1, hτt⟩ : ∃ τ ∈ s.T, τ ≠ 1 ∧ τ ≠ h.t := by
    by_contra hcon
    push Not at hcon
    have hsub : (s.T : Set G) ⊆ {1, h.t} := fun x hx => by
      by_cases h1 : x = 1
      · exact Or.inl h1
      · exact Or.inr (hcon x hx h1)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair (Ne.symm h.t_ne_one), ← Nat.card_coe_set_eq, SetLike.coe_sort_coe,
      hT.card_four] at this
    omega
  have hτC := h.sylow_le_centralizer s.S s.t_mem_S (hTS hτT)
  obtain ⟨v, hvT, hvF, hv1⟩ : ∃ v ∈ s.T, v ∈ h.F ∧ v ≠ 1 := by
    rcases h.mem_centralizer_t.mp hτC with hτF | hτF
    · exact ⟨τ, hτT, hτF, hτ1⟩
    · refine ⟨h.t * τ, s.T.mul_mem s.t_mem_T hτT, hτF, fun h1 => hτt ?_⟩
      rw [← mul_one h.t, ← h1, ← mul_assoc, h.t_mul_t, one_mul]
  have hvt : h.t ≠ v := fun h0 => h.t_not_mem (h0 ▸ hvF)
  have hvv : v * v = 1 := mul_self_of_isKleinFour' hT hvT
  have hv2 : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hvv) hv1
  set T₀ := GorensteinWalter.kleinFourOfCommutingInvolutions h.t v h.t_mul_t hvv
    (h.commute_of_mem_F hvF).symm
  have hT₀ : IsKleinFour T₀ := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions _ _
    _ _ h.t_ne_one hv1 hvt _
  have hT₀T : T₀ ≤ s.T := by
    intro x hx
    change x ∈ ({h.t * v, h.t, v, 1} : Set G) at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact s.T.mul_mem s.t_mem_T hvT
    · exact s.t_mem_T
    · exact hvT
    · exact s.T.one_mem
  have hTeq : T₀ = s.T := Subgroup.eq_of_le_of_card_ge hT₀T (by rw [hT.card_four, hT₀.card_four])
  obtain ⟨U, w, hU, hvU, hUcard⟩ := (h.facts hp).even_torus v hvF hv2
  refine ⟨⟨v, U, w, hvF, hv1, fun x => ?_, hU, hvU, ?_⟩⟩
  · rw [← hTeq]
    change x ∈ ({h.t * v, h.t, v, 1} : Set G) ↔ _
    simp
  · have := h.mod_eight hp
    rw [JTHyp.eps, JTHyp.q_eq]
    rcases hUcard with ⟨h4, hc⟩ | ⟨h4, hc⟩
    · rw [ite_eq_left h4]
      exact_mod_cast hc
    · rw [ite_eq_right (by omega)]
      have : ((2 * Nat.card U + 1 : ℕ) : ℤ) = ((h.p ^ h.f : ℕ) : ℤ) := by rw [hc]
      push_cast at this ⊢
      linarith

noncomputable def data
    (hp : h.p ≠ 2) : s.Data := Classical.choice (s.nonempty_data hp)

namespace Data

variable {s} (d : s.Data)

theorem v_mem_T : d.v ∈ s.T := (d.mem_T _).mpr (Or.inr (Or.inr (Or.inl rfl)))

theorem v_mul_v : d.v * d.v = 1 := mul_self_of_isKleinFour' s.four d.v_mem_T

theorem orderOf_v : orderOf d.v = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact d.v_mul_v) d.v_ne_one

theorem t_ne_v : h.t ≠ d.v := fun h0 => h.t_not_mem (h0 ▸ d.v_mem_F)

theorem centralizer_T :
    Subgroup.centralizer (s.T : Set G) =
      Subgroup.centralizer ({h.t} : Set G) ⊓ Subgroup.centralizer ({d.v} : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe,
    Set.mem_singleton_iff, forall_eq]
  constructor
  · intro hx
    exact ⟨hx _ s.t_mem_T, hx _ d.v_mem_T⟩
  · rintro ⟨h1, h2⟩ y hy
    rcases (d.mem_T y).mp hy with rfl | rfl | rfl | rfl
    · rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
    · exact h1
    · exact h2
    · simp

theorem inf_centralizer_v :
    h.F ⊓ Subgroup.centralizer ({d.v} : Set G) = d.U ⊔ Subgroup.zpowers d.w :=
  d.torus.centralizer_eq d.v_mem_U d.orderOf_v

theorem card_U_mod_four
    (hp : h.p ≠ 2) : Nat.card d.U % 4 = 2 := by
  have h8 := h.mod_eight hp
  have hc := d.two_mul_card_U
  rw [JTHyp.eps] at hc
  rcases h8 with h8 | h8
  · rw [ite_eq_left (by omega)] at hc
    omega
  · rw [ite_eq_right (by omega)] at hc
    omega

theorem mem_F_part {x : G} (hx : x ∈ Subgroup.centralizer (s.T : Set G)) :
    (x ∈ h.F ∧ x ∈ d.U ⊔ Subgroup.zpowers d.w) ∨
      (h.t * x ∈ h.F ∧ h.t * x ∈ d.U ⊔ Subgroup.zpowers d.w) := by
  rw [d.centralizer_T] at hx
  rw [← d.inf_centralizer_v]
  have hvt : h.t ∈ Subgroup.centralizer ({d.v} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (h.commute_of_mem_F d.v_mem_F).symm
  rcases h.mem_centralizer_t.mp hx.1 with hxF | hxF
  · exact Or.inl ⟨hxF, hxF, hx.2⟩
  · exact Or.inr ⟨hxF, hxF, Subgroup.mul_mem _ hvt hx.2⟩

theorem Q_spec (hp : h.p ≠ 2) :
    s.Q ≤ d.U ∧ IsCyclic s.Q ∧ Nat.card d.U = 2 * Nat.card s.Q ∧ Odd (Nat.card s.Q) ∧
      ∀ x ∈ d.U, Odd (orderOf x) → x ∈ s.Q := by
  have hU4 := d.card_U_mod_four hp
  have hm : Odd (Nat.card d.U / 2) := Nat.odd_iff.mpr (by omega)
  obtain ⟨Q₀, hQ₀U, hQ₀c, hQ₀card, hQ₀all⟩ :=
    exists_oddPart_of_cyclic d.torus.cyclic hm (by omega)
  have hUC : d.U ≤ Subgroup.centralizer (s.T : Set G) := by
    rw [d.centralizer_T]
    intro x hx
    refine ⟨h.le_centralizer (d.torus.le hx), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have := d.torus.cyclic
    exact congrArg Subtype.val ((IsCyclic.commGroup (α := d.U)).mul_comm ⟨x, hx⟩ ⟨d.v, d.v_mem_U⟩)
  have hQ : s.Q = Q₀ := by
    refine oddCoreOf_eq_of (hQ₀U.trans hUC) ⟨fun x hx g => ?_⟩ (hQ₀card ▸ hm) ?_
    · rw [Subgroup.mem_subgroupOf] at hx ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have hxU := hQ₀U hx
      have key : ∀ y ∈ d.U ⊔ Subgroup.zpowers d.w, y * x * y⁻¹ ∈ Q₀ := by
        intro y hy
        rcases d.torus.conj_eq hy hxU with ⟨-, h1⟩ | ⟨-, h1⟩
        · rw [h1]; exact hx
        · rw [h1]; exact Q₀.inv_mem hx
      have htx : h.t * x = x * h.t := (h.commute_of_mem_F (d.torus.le hxU)).symm
      rcases d.mem_F_part g.2 with ⟨-, hg⟩ | ⟨-, hg⟩
      · exact key _ hg
      · have hy := key _ hg
        have hyF : h.t * g * x * (h.t * g)⁻¹ ∈ h.F := d.torus.le (hQ₀U hy)
        have hc := h.commute_of_mem_F hyF
        have : (g : G) * x * (g : G)⁻¹ = h.t * g * x * (h.t * g)⁻¹ := by
          calc (g : G) * x * (g : G)⁻¹
              = h.t⁻¹ * (h.t * g * x * (h.t * g)⁻¹) * h.t := by group
            _ = h.t * g * x * (h.t * g)⁻¹ := by
              rw [mul_assoc _ _ h.t, hc, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [this]
        exact hy
    · intro x hx hodd
      have hxt : x ∈ Subgroup.centralizer ({h.t} : Set G) := by
        rw [d.centralizer_T] at hx
        exact hx.1
      have hxF := h.mem_F_of_odd hxt hodd
      have hxv : x ∈ h.F ⊓ Subgroup.centralizer ({d.v} : Set G) := by
        rw [d.centralizer_T] at hx
        exact ⟨hxF, hx.2⟩
      rw [d.inf_centralizer_v, d.torus.mem_sup_iff] at hxv
      rcases hxv with hxU | hxU
      · exact hQ₀all x hxU hodd
      · have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by
          rw [pow_two]; exact d.torus.mul_self_of_mul_mem hxU)
        have h1 : orderOf x = 1 := by
          rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
          · exact h1
          · rw [h1] at hodd
            exact absurd hodd (by decide)
        rw [orderOf_eq_one_iff.mp h1]
        exact Q₀.one_mem
  rw [hQ]
  exact ⟨hQ₀U, hQ₀c, by omega, hQ₀card ▸ hm, hQ₀all⟩

theorem card_centralizer_T :
    Nat.card (Subgroup.centralizer (s.T : Set G)) = 4 * Nat.card d.U := by
  have hUw : Nat.card (d.U ⊔ Subgroup.zpowers d.w : Subgroup G) = 2 * Nat.card d.U := by
    refine card_eq_two_mul_of_xor le_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      fun b hb => ⟨fun hbw hbU => d.torus.w_not_mem ?_, fun hbU => ?_⟩
    · have : d.w = b⁻¹ * (b * d.w) := by group
      rw [this]
      exact d.U.mul_mem (d.U.inv_mem hbU) hbw
    · rcases d.torus.mem_sup_iff.mp hb with h1 | h1
      · exact absurd h1 hbU
      · exact h1
  have hvt : h.t ∈ Subgroup.centralizer ({d.v} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (h.commute_of_mem_F d.v_mem_F).symm
  have hle : h.F ⊓ Subgroup.centralizer ({d.v} : Set G) ≤ Subgroup.centralizer (s.T : Set G) := by
    rw [d.centralizer_T]
    exact inf_le_inf_right _ h.le_centralizer
  have htC : h.t ∈ Subgroup.centralizer (s.T : Set G) := by
    rw [d.centralizer_T]
    exact ⟨h.t_mem_centralizer, hvt⟩
  have hC := card_eq_two_mul_of_xor hle htC fun b hb => by
    have hb' := hb
    rw [d.centralizer_T] at hb'
    constructor
    · intro hbt hbF
      apply h.t_not_mem
      have : h.t = (b : G)⁻¹ * (b * h.t) := by group
      rw [this]
      exact h.F.mul_mem (h.F.inv_mem hbF.1) hbt.1
    · intro hbF
      have hbnF : b ∉ h.F := fun h1 => hbF ⟨h1, hb'.2⟩
      rcases h.mem_centralizer_t.mp hb'.1 with h1 | h1
      · exact absurd h1 hbnF
      · refine ⟨?_, Subgroup.mul_mem _ hb'.2 hvt⟩
        rw [h.commute_of_mem hb'.1]
        exact h1
  rw [hC, d.inf_centralizer_v, hUw]
  ring

end Data

variable (hp : h.p ≠ 2)
include hp

theorem Q_le_U :
    s.Q ≤ (s.data hp).U := ((s.data hp).Q_spec hp).1

theorem Q_le_F :
    s.Q ≤ h.F := (s.Q_le_U hp).trans (s.data hp).torus.le

theorem isCyclic_Q :
    IsCyclic s.Q := ((s.data hp).Q_spec hp).2.1

theorem card_U_eq :
    Nat.card (s.data hp).U = 2 * Nat.card s.Q := ((s.data hp).Q_spec hp).2.2.1

theorem odd_card_Q :
    Odd (Nat.card s.Q) := ((s.data hp).Q_spec hp).2.2.2.1

omit hp in
theorem Q_le_centralizer_T : s.Q ≤ Subgroup.centralizer (s.T : Set G) :=
  Subgroup.map_subtype_le _

theorem four_mul_card_Q :
    4 * (Nat.card s.Q : ℤ) = h.q + h.eps := by
  have h1 := (s.data hp).two_mul_card_U
  rw [s.card_U_eq hp] at h1
  push_cast at h1
  linarith

theorem card_Q_ne_one :
    Nat.card s.Q ≠ 1 := by
  intro h1
  have h4 := s.four_mul_card_Q hp
  have h5 := h.five_lt
  have h8 := h.mod_eight hp
  rw [h1, JTHyp.eps] at h4
  rw [JTHyp.q_eq] at h8 h4
  split_ifs at h4 with h3
  · omega
  · have : (h.p ^ h.f : ℤ) = 5 := by push_cast at h4 ⊢; linarith
    have : h.p ^ h.f = 5 := by exact_mod_cast this
    omega

theorem mem_Q_iff {x : G} :
    x ∈ s.Q ↔ x ∈ Subgroup.centralizer (s.T : Set G) ∧ Odd (orderOf x) := by
  set d := s.data hp
  constructor
  · intro hx
    exact ⟨s.Q_le_centralizer_T hx,
      Odd.of_dvd_nat (s.odd_card_Q hp) (Subgroup.orderOf_dvd_natCard _ hx)⟩
  · rintro ⟨hx, hodd⟩
    have hxt : x ∈ Subgroup.centralizer ({h.t} : Set G) := by
      rw [d.centralizer_T] at hx
      exact hx.1
    have hxF := h.mem_F_of_odd hxt hodd
    have hxv : x ∈ h.F ⊓ Subgroup.centralizer ({d.v} : Set G) := by
      rw [d.centralizer_T] at hx
      exact ⟨hxF, hx.2⟩
    rw [d.inf_centralizer_v, d.torus.mem_sup_iff] at hxv
    rcases hxv with hxU | hxU
    · exact (d.Q_spec hp).2.2.2.2 x hxU hodd
    · have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by
        rw [pow_two]; exact d.torus.mul_self_of_mul_mem hxU)
      have h1 : orderOf x = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
        · exact h1
        · rw [h1] at hodd
          exact absurd hodd (by decide)
      rw [orderOf_eq_one_iff.mp h1]
      exact s.Q.one_mem

omit hp in
theorem T_le_centralizer_Q : s.T ≤ Subgroup.centralizer (s.Q : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact ((Subgroup.mem_centralizer_iff.mp (s.Q_le_centralizer_T hy)) x hx).symm

theorem conj_eq_inv_of_mem_S
    {x : G} (hxS : x ∈ s.S) (hxT : x ∉ s.T) {y : G} (hy : y ∈ s.Q) :
    x * y * x⁻¹ = y⁻¹ := by
  set d := s.data hp
  have hab := h.abelian_sylow s.S
  have hyU := s.Q_le_U hp hy
  have hyF := s.Q_le_F hp hy
  obtain ⟨z, hzS, hzF, hzx⟩ : ∃ z ∈ s.S, z ∈ h.F ∧ (x = z ∨ x = h.t * z) := by
    rcases h.mem_centralizer_t.mp (h.sylow_le_centralizer s.S s.t_mem_S hxS) with h1 | h1
    · exact ⟨x, hxS, h1, Or.inl rfl⟩
    · refine ⟨h.t * x, (s.S : Subgroup G).mul_mem s.t_mem_S hxS, h1, Or.inr ?_⟩
      rw [← mul_assoc, h.t_mul_t, one_mul]
  have hzT : z ∉ s.T := by
    intro hzT
    rcases hzx with rfl | rfl
    · exact hxT hzT
    · exact hxT (s.T.mul_mem s.t_mem_T hzT)
  have hzv : z ∈ h.F ⊓ Subgroup.centralizer ({d.v} : Set G) :=
    ⟨hzF, Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (hab.is_comm.comm ⟨z, hzS⟩ ⟨d.v, s.le_S d.v_mem_T⟩))⟩
  rw [d.inf_centralizer_v] at hzv
  have hz1 : z ≠ 1 := fun h0 => hzT (h0 ▸ s.T.one_mem)
  have hzU : z ∉ d.U := by
    intro hzU
    have hz2 : orderOf z = 2 := orderOf_eq_prime
      (by rw [pow_two]; exact h.mul_self_of_mem_sylow hp s.S s.t_mem_S hzS) hz1
    have := eq_of_orderOf_eq_two_of_isCyclic d.torus.cyclic hzU d.v_mem_U hz2 d.orderOf_v
    exact hzT (this ▸ d.v_mem_T)
  have hzy : z * y * z⁻¹ = y⁻¹ := by
    rcases d.torus.conj_eq hzv hyU with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact absurd h1 hzU
    · exact h1
  rcases hzx with rfl | rfl
  · exact hzy
  · have hc := h.commute_of_mem_F (h.F.inv_mem hyF)
    rw [show h.t * z * y * (h.t * z)⁻¹ = h.t * (z * y * z⁻¹) * h.t⁻¹ by group, hzy, ← hc,
      mul_inv_cancel_right]

theorem card_centralizer_T :
    Nat.card (Subgroup.centralizer (s.T : Set G)) = 8 * Nat.card s.Q := by
  rw [(s.data hp).card_centralizer_T, s.card_U_eq hp]
  ring

omit hp in
theorem S_le_centralizer_T : (s.S : Subgroup G) ≤ Subgroup.centralizer (s.T : Set G) := by
  have hab := h.abelian_sylow s.S
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (hab.is_comm.comm ⟨y, s.le_S hy⟩ ⟨x, hx⟩)

theorem centralizer_T_eq :
    Subgroup.centralizer (s.T : Set G) = (s.S : Subgroup G) ⊔ s.Q := by
  symm
  apply Subgroup.eq_of_le_of_card_ge (sup_le s.S_le_centralizer_T s.Q_le_centralizer_T)
  rw [s.card_centralizer_T hp]
  have h8 : 8 ∣ Nat.card ((s.S : Subgroup G) ⊔ s.Q : Subgroup G) :=
    h.card_sylow hp s.S s.t_mem_S ▸ Subgroup.card_dvd_of_le le_sup_left
  have hQd : Nat.card s.Q ∣ Nat.card ((s.S : Subgroup G) ⊔ s.Q : Subgroup G) :=
    Subgroup.card_dvd_of_le le_sup_right
  have hcop : Nat.Coprime 8 (Nat.card s.Q) := by
    have := s.odd_card_Q hp
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr this)
  exact Nat.le_of_dvd Nat.card_pos (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h8 hQd)

theorem normalizer_T_le_normalizer_Q :
    Subgroup.normalizer (s.T : Set G) ≤ Subgroup.normalizer (s.Q : Set G) := by
  intro g hg
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨hxC, hodd⟩ := (s.mem_Q_iff hp).mp hx
  refine (s.mem_Q_iff hp).mpr ⟨?_, by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact hodd⟩
  rw [Subgroup.mem_centralizer_iff] at hxC ⊢
  intro y hy
  have hy' : g⁻¹ * y * g ∈ s.T := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp hy
    simpa using this
  have := hxC _ hy'
  calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
    _ = g * x * g⁻¹ * y := by group

theorem lemma_4_2_a :
    Subgroup.centralizer (s.T : Set G) = (s.S : Subgroup G) ⊔ s.Q ∧ IsCyclic s.Q ∧
      4 * (Nat.card s.Q : ℤ) = h.q + h.eps ∧ Nat.card s.Q ≠ 1 :=
  ⟨s.centralizer_T_eq hp, s.isCyclic_Q hp, s.four_mul_card_Q hp, s.card_Q_ne_one hp⟩

end Setup

end CFSG.Walter.JT
