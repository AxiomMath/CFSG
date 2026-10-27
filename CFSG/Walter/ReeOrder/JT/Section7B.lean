module

public import CFSG.Walter.ReeOrder.JT.Section7A
public import CFSG.Walter.ReeOrder.JT.PSL2Torus
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.Dihedral.OriginalSylowControl

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups

section General

variable {X : Type*} [Group X]

theorem eq_mul_of_mem_kleinFour [Finite X] {V : Subgroup X} (hV : IsKleinFour V) {x y z : X}
    (hx : x ∈ V) (hy : y ∈ V) (hz : z ∈ V) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y)
    (hz1 : z ≠ 1) (hzx : z ≠ x) (hzy : z ≠ y) : z = x * y :=
  congrArg Subtype.val (IsKleinFour.eq_mul_of_ne_all (G := V) (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)
    (z := ⟨z, hz⟩) (fun h0 => hx1 (congrArg Subtype.val h0))
    (fun h0 => hy1 (congrArg Subtype.val h0)) (fun h0 => hxy (congrArg Subtype.val h0))
    (fun h0 => hz1 (congrArg Subtype.val h0)) (fun h0 => hzx (congrArg Subtype.val h0))
    (fun h0 => hzy (congrArg Subtype.val h0)))

theorem exists_normal_odd_of_kleinFour_sylow [Finite X] (V : Sylow 2 X)
    (hV : IsKleinFour (V : Subgroup X)) {u w : X} (hu : u ∈ V) (hw : w ∈ V) (hu1 : u ≠ 1)
    (hw1 : w ≠ 1) (huw : ∀ g : X, g * u * g⁻¹ ≠ w) :
    ∃ M : Subgroup X, M.Normal ∧ Odd (Nat.card M) ∧ Nat.card X = 4 * Nat.card M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have huw' : u ≠ w := fun h0 => huw 1 (by rw [h0]; group)
  have hVN : ∀ n ∈ Subgroup.normalizer ((V : Subgroup X) : Set X), ∀ x ∈ (V : Subgroup X),
      n * x * n⁻¹ ∈ (V : Subgroup X) := fun n hn x hx =>
    (Subgroup.mem_normalizer_iff.mp hn x).mp hx
  have huwV : u * w ∈ (V : Subgroup X) := (V : Subgroup X).mul_mem hu hw
  obtain ⟨z, hzV, hz1, hz⟩ : ∃ z ∈ (V : Subgroup X), z ≠ 1 ∧
      ∀ n ∈ Subgroup.normalizer ((V : Subgroup X) : Set X), n * z = z * n := by
    by_contra hcon
    push Not at hcon
    obtain ⟨n₁, hn₁, hn₁u⟩ := hcon u hu hu1
    obtain ⟨n₂, hn₂, hn₂w⟩ := hcon w hw hw1
    have hc1 : ∀ {n x : X}, n * x ≠ x * n → n * x * n⁻¹ ≠ x := fun {n x} h0 h1 =>
      h0 (by calc n * x = n * x * n⁻¹ * n := by group
        _ = x * n := by rw [h1])
    have hne1 : ∀ {n x : X}, x ≠ 1 → n * x * n⁻¹ ≠ 1 := fun {n x} hx h0 =>
      hx (by have := congrArg (fun y => n⁻¹ * y * n) h0; simpa [mul_assoc] using this)
    have h1 : n₁ * u * n₁⁻¹ = u * w :=
      eq_mul_of_mem_kleinFour hV hu hw (hVN n₁ hn₁ u hu) hu1 hw1 huw' (hne1 hu1) (hc1 hn₁u)
        (huw n₁)
    have h2 : n₂ * w * n₂⁻¹ = u * w :=
      eq_mul_of_mem_kleinFour hV hu hw (hVN n₂ hn₂ w hw) hu1 hw1 huw' (hne1 hw1)
        (fun h0 => huw n₂⁻¹ (by rw [← h0]; group)) (hc1 hn₂w)
    apply huw (n₂⁻¹ * n₁)
    calc n₂⁻¹ * n₁ * u * (n₂⁻¹ * n₁)⁻¹ = n₂⁻¹ * (n₁ * u * n₁⁻¹) * n₂ := by group
      _ = n₂⁻¹ * (n₂ * w * n₂⁻¹) * n₂ := by rw [h1, h2]
      _ = w := by group
  obtain ⟨M₁, hM₁, hM₁i⟩ :=
    exists_normal_index_eq_of_commute_normalizer V hV.isMulCommutative hzV hz1 hz
  have hM₁card : Nat.card X = 2 * Nat.card M₁ := by
    rw [← Subgroup.card_mul_index M₁, hM₁i, mul_comm]
  have hfac : (Nat.card X).factorization 2 = 2 := by
    have h1 := Sylow.card_eq_multiplicity V
    rw [hV.card_four, show (4 : ℕ) = 2 ^ 2 by norm_num] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hfac₁ : (Nat.card M₁).factorization 2 = 1 := by
    rw [hM₁card, Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two] at hfac
    omega
  let S₁ : Sylow 2 M₁ := default
  have hS₁ : Nat.card (S₁ : Subgroup M₁) = 2 := by
    rw [Sylow.card_eq_multiplicity, hfac₁, pow_one]
  have hS₁c : IsCyclic (S₁ : Subgroup M₁) := isCyclic_of_prime_card hS₁
  obtain ⟨hKcard, -, -, ⟨-, hKodd, -, -⟩, hKchar⟩ :=
    cyclic_sylow_normal_odd_complement S₁ hS₁c
  refine ⟨(pPrimeCore 2 M₁).map M₁.subtype, ConjAct.normal_of_characteristic_of_normal, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective M₁.subtype_injective]
    exact hKodd
  · rw [Subgroup.card_map_of_injective M₁.subtype_injective, hKcard, hS₁, hM₁card]
    have h2 : 2 ∣ Nat.card M₁ := hS₁ ▸ Subgroup.card_subgroup_dvd_card (S₁ : Subgroup M₁)
    obtain ⟨k, hk⟩ := h2
    rw [hk]
    omega

end General

namespace Setup

variable {G : Type} [Group G] [Finite G] {h : JTHyp G} (s : Setup h) (hp : h.p ≠ 2)
include hp

theorem exists_conj_le_Q_of_eight_dvd
    {W : Subgroup G} (hWodd : Odd (Nat.card W))
    (h8 : 8 ∣ Nat.card (Subgroup.normalizer (W : Set G))) :
    ∃ g : G, W.map (MulAut.conj g).toMonoidHom ≤ s.Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime
    (G := Subgroup.normalizer (W : Set G)) 2 (n := 3) (by norm_num; exact h8)
  set H₁ := H.map (Subgroup.normalizer (W : Set G)).subtype
  have hH₁ : Nat.card H₁ = 8 := by
    rw [Subgroup.card_map_of_injective (Subgroup.normalizer (W : Set G)).subtype_injective, hH]
    norm_num
  have hfac : (Nat.card G).factorization 2 = 3 := by
    have h1 := h.card_sylow hp s.S s.t_mem_S
    rw [Sylow.card_eq_multiplicity, show (8 : ℕ) = 2 ^ 3 by norm_num] at h1
    exact Nat.pow_right_injective le_rfl h1
  let S' : Sylow 2 G := Sylow.ofCard H₁ (by rw [hH₁, hfac]; norm_num)
  exact s.lemma_4_2_b hp ⟨hWodd, S', Subgroup.map_subtype_le H⟩

end Setup

namespace JTHyp

variable {G : Type} [Group G] [Finite G] (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem exists_normal_odd_normalizer_of_mem_torus
    {C : Subgroup G} (hCF : C ≤ h.F)
    (hC : IsCyclic C) (hCcard : 2 * Nat.card C + 1 = h.q) {x : G} (hxC : x ∈ C) (hx1 : x ≠ 1) :
    ∃ M : Subgroup (Subgroup.normalizer (Subgroup.zpowers x : Set G)), M.Normal ∧
      Odd (Nat.card M) ∧
      Nat.card (Subgroup.normalizer (Subgroup.zpowers x : Set G)) = 4 * Nat.card M := by
  classical
  have hp := h.p_ne_two_of_eq_three hp3
  have hq8 := h.q_mod_eight_of_eq_three hp3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w, hU⟩ := exists_torusData_of_isCyclic h.F h.iso hp h.five_lt
    (by rw [← JTHyp.q_eq]; omega) hCF hC hCcard
  have hxF : x ∈ h.F := hCF hxC
  have hwF : w ∈ h.F := hU.w_mem
  have hwx : w * x * w⁻¹ = x⁻¹ := hU.inv x hxC
  have hxodd : Odd (orderOf x) := by
    refine Odd.of_dvd_nat (Nat.odd_iff.mpr ?_) (Subgroup.orderOf_dvd_natCard C hxC)
    omega
  set N₀ := Subgroup.normalizer (Subgroup.zpowers x : Set G) with hN₀def
  have htN : h.t ∈ N₀ := mem_normalizer_zpowers_of_commute (h.commute_of_mem_F hxF).symm
  have hwN : w ∈ N₀ := by
    refine (conj_smul_eq_iff (K := Subgroup.zpowers x)).mp ?_
    change (Subgroup.zpowers x).map (MulAut.conj w).toMonoidHom = Subgroup.zpowers x
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (w * x * w⁻¹) = Subgroup.zpowers x
    rw [hwx, Subgroup.zpowers_inv]
  have htw : Commute h.t w := (h.commute_of_mem_F hwF).symm
  have htne : h.t ≠ w := fun h0 => h.t_not_mem (h0 ▸ hwF)
  have hw1 : w ≠ 1 := fun h0 => hU.w_not_mem (h0 ▸ C.one_mem)
  set V := GorensteinWalter.kleinFourOfCommutingInvolutions h.t w h.t_mul_t hU.w_mul_self htw
    with hVdef
  have hV : IsKleinFour V := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    _ _ _ _ h.t_ne_one hw1 htne htw
  have hmemV : ∀ y, y ∈ V ↔ y = h.t * w ∨ y = h.t ∨ y = w ∨ y = 1 := fun y => Iff.rfl
  have htV : h.t ∈ V := (hmemV _).mpr (Or.inr (Or.inl rfl))
  have hwV : w ∈ V := (hmemV _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hVN : V ≤ N₀ := fun y hy => by
    rcases (hmemV y).mp hy with rfl | rfl | rfl | rfl
    · exact N₀.mul_mem htN hwN
    · exact htN
    · exact hwN
    · exact N₀.one_mem
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
  obtain ⟨S', hS'⟩ := hV2.exists_le_sylow
  let s : Setup h := ⟨S', hS' htV, V, hS', hV, htV⟩
  have h8 : ¬ 8 ∣ Nat.card N₀ := by
    intro h8
    obtain ⟨g, hg⟩ := s.exists_conj_le_Q_of_eight_dvd hp
      (by rw [Nat.card_zpowers]; exact hxodd) h8
    have h1 : orderOf x ∣ Nat.card s.Q := by
      have := Subgroup.card_dvd_of_le hg
      rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective, Nat.card_zpowers] at this
    have h4 := s.four_mul_card_Q hp
    rw [h.eps_eq_one_of_eq_three hp3] at h4
    have h4' : 4 * Nat.card s.Q = h.q + 1 := by exact_mod_cast h4
    have h2 : orderOf x ∣ Nat.card C := Subgroup.orderOf_dvd_natCard C hxC
    have h3 : orderOf x ∣ 2 * Nat.card s.Q := dvd_mul_of_dvd_right h1 2
    have h5 : 2 * Nat.card s.Q = Nat.card C + 1 := by omega
    rw [h5] at h3
    have := (Nat.dvd_add_right h2).mp h3
    exact hx1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp this))
  have hVcard : Nat.card (V.subgroupOf N₀) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv, hV.card_four]
  have hfacN : (Nat.card N₀).factorization 2 = 2 := by
    have h4 : 2 ^ 2 ∣ Nat.card N₀ := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hV.card_four]
      exact Subgroup.card_dvd_of_le hVN
    have h8' : ¬ 2 ^ 3 ∣ Nat.card N₀ := by norm_num; exact h8
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne'] at h4 h8'
    omega
  let VS : Sylow 2 N₀ := Sylow.ofCard (V.subgroupOf N₀) (by rw [hVcard, hfacN]; norm_num)
  have hVS : IsKleinFour (VS : Subgroup N₀) := by
    have e : (V.subgroupOf N₀) ≃* V := Subgroup.subgroupOfEquivOfLe hVN
    exact ⟨hVcard, by
      change Monoid.exponent (V.subgroupOf N₀) = 2
      rw [Monoid.exponent_eq_of_mulEquiv e, hV.exponent_two]⟩
  have hnc : ∀ g : N₀, g * ⟨h.t, htN⟩ * g⁻¹ ≠ ⟨w, hwN⟩ := by
    intro g hg
    have hg' : (g : G) * h.t * (g : G)⁻¹ = w := congrArg Subtype.val hg
    have hgx : (g : G) * x * (g : G)⁻¹ ∈ Subgroup.zpowers x :=
      (Subgroup.mem_normalizer_iff.mp g.2 x).mp (Subgroup.mem_zpowers x)
    have hz : Subgroup.zpowers ((g : G) * x * (g : G)⁻¹) = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hgx) (by
        rw [Nat.card_zpowers, Nat.card_zpowers, ← MulAut.conj_apply, MulEquiv.orderOf_eq])
    have hxz : x ∈ Subgroup.zpowers ((g : G) * x * (g : G)⁻¹) := hz ▸ Subgroup.mem_zpowers x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxz
    have htx : Commute h.t x := (h.commute_of_mem_F hxF).symm
    have hc : Commute w ((g : G) * x * (g : G)⁻¹) := by
      rw [← hg']
      change (g : G) * h.t * (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) =
        (g : G) * x * (g : G)⁻¹ * ((g : G) * h.t * (g : G)⁻¹)
      calc (g : G) * h.t * (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) =
          (g : G) * (h.t * x) * (g : G)⁻¹ := by group
        _ = (g : G) * (x * h.t) * (g : G)⁻¹ := by rw [htx.eq]
        _ = _ := by group
    have hwx' : w * x = x * w := by
      have := (hc.zpow_right k).eq
      rwa [hk] at this
    have hxx : x = x⁻¹ := by rw [← hwx, hwx', mul_inv_cancel_right]
    apply hx1
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [pow_two]; nth_rewrite 2 [hxx]; exact mul_inv_cancel x)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · rw [h1] at hxodd
      exact absurd hxodd (by decide)
  obtain ⟨M, hMn, hModd, hMcard⟩ := exists_normal_odd_of_kleinFour_sylow VS hVS
    (u := ⟨h.t, htN⟩) (w := ⟨w, hwN⟩) (by
      change (⟨h.t, htN⟩ : N₀) ∈ V.subgroupOf N₀
      rw [Subgroup.mem_subgroupOf]; exact htV)
    (by change (⟨w, hwN⟩ : N₀) ∈ V.subgroupOf N₀; rw [Subgroup.mem_subgroupOf]; exact hwV)
    (fun h0 => h.t_ne_one (congrArg Subtype.val h0)) (fun h0 => hw1 (congrArg Subtype.val h0))
    hnc
  exact ⟨M, hMn, hModd, hMcard⟩

theorem lemma_7_4
    {C : Subgroup G} (hCF : C ≤ h.F) (hC : IsCyclic C)
    (hCcard : 2 * Nat.card C + 1 = h.q) {x : G} (hxC : x ∈ C) (hx1 : x ≠ 1) :
    ¬ 3 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  classical
  have hp := h.p_ne_two_of_eq_three hp3
  have hq8 := h.q_mod_eight_of_eq_three hp3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w, hU⟩ := exists_torusData_of_isCyclic h.F h.iso hp h.five_lt
    (by rw [← JTHyp.q_eq]; omega) hCF hC hCcard
  have hxF : x ∈ h.F := hCF hxC
  have hwF : w ∈ h.F := hU.w_mem
  have hwx : w * x * w⁻¹ = x⁻¹ := hU.inv x hxC
  have hxodd : Odd (orderOf x) := by
    refine Odd.of_dvd_nat (Nat.odd_iff.mpr ?_) (Subgroup.orderOf_dvd_natCard C hxC)
    omega
  set N₀ := Subgroup.normalizer (Subgroup.zpowers x : Set G) with hN₀def
  have htN : h.t ∈ N₀ := mem_normalizer_zpowers_of_commute (h.commute_of_mem_F hxF).symm
  have hwN : w ∈ N₀ := by
    refine (conj_smul_eq_iff (K := Subgroup.zpowers x)).mp ?_
    change (Subgroup.zpowers x).map (MulAut.conj w).toMonoidHom = Subgroup.zpowers x
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (w * x * w⁻¹) = Subgroup.zpowers x
    rw [hwx, Subgroup.zpowers_inv]
  have htw : Commute h.t w := (h.commute_of_mem_F hwF).symm
  have htne : h.t ≠ w := fun h0 => h.t_not_mem (h0 ▸ hwF)
  have hw1 : w ≠ 1 := fun h0 => hU.w_not_mem (h0 ▸ C.one_mem)
  set V := GorensteinWalter.kleinFourOfCommutingInvolutions h.t w h.t_mul_t hU.w_mul_self htw
    with hVdef
  have hV : IsKleinFour V := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    _ _ _ _ h.t_ne_one hw1 htne htw
  have hmemV : ∀ y, y ∈ V ↔ y = h.t * w ∨ y = h.t ∨ y = w ∨ y = 1 := fun y => Iff.rfl
  have htV : h.t ∈ V := (hmemV _).mpr (Or.inr (Or.inl rfl))
  have hwV : w ∈ V := (hmemV _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hVN : V ≤ N₀ := fun y hy => by
    rcases (hmemV y).mp hy with rfl | rfl | rfl | rfl
    · exact N₀.mul_mem htN hwN
    · exact htN
    · exact hwN
    · exact N₀.one_mem
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
  obtain ⟨S', hS'⟩ := hV2.exists_le_sylow
  let s : Setup h := ⟨S', hS' htV, V, hS', hV, htV⟩
  have h8 : ¬ 8 ∣ Nat.card N₀ := by
    intro h8
    obtain ⟨g, hg⟩ := s.exists_conj_le_Q_of_eight_dvd hp
      (by rw [Nat.card_zpowers]; exact hxodd) h8
    have h1 : orderOf x ∣ Nat.card s.Q := by
      have := Subgroup.card_dvd_of_le hg
      rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective, Nat.card_zpowers] at this
    have h4 := s.four_mul_card_Q hp
    rw [h.eps_eq_one_of_eq_three hp3] at h4
    have h4' : 4 * Nat.card s.Q = h.q + 1 := by exact_mod_cast h4
    have h2 : orderOf x ∣ Nat.card C := Subgroup.orderOf_dvd_natCard C hxC
    have h3 : orderOf x ∣ 2 * Nat.card s.Q := dvd_mul_of_dvd_right h1 2
    have h5 : 2 * Nat.card s.Q = Nat.card C + 1 := by omega
    rw [h5] at h3
    have := (Nat.dvd_add_right h2).mp h3
    exact hx1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp this))
  have hVcard : Nat.card (V.subgroupOf N₀) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN).toEquiv, hV.card_four]
  have hfacN : (Nat.card N₀).factorization 2 = 2 := by
    have h4 : 2 ^ 2 ∣ Nat.card N₀ := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hV.card_four]
      exact Subgroup.card_dvd_of_le hVN
    have h8' : ¬ 2 ^ 3 ∣ Nat.card N₀ := by norm_num; exact h8
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne'] at h4 h8'
    omega
  let VS : Sylow 2 N₀ := Sylow.ofCard (V.subgroupOf N₀) (by rw [hVcard, hfacN]; norm_num)
  have hVS : IsKleinFour (VS : Subgroup N₀) := by
    have e : (V.subgroupOf N₀) ≃* V := Subgroup.subgroupOfEquivOfLe hVN
    exact ⟨hVcard, by
      change Monoid.exponent (V.subgroupOf N₀) = 2
      rw [Monoid.exponent_eq_of_mulEquiv e, hV.exponent_two]⟩
  have hnc : ∀ g : N₀, g * ⟨h.t, htN⟩ * g⁻¹ ≠ ⟨w, hwN⟩ := by
    intro g hg
    have hg' : (g : G) * h.t * (g : G)⁻¹ = w := congrArg Subtype.val hg
    have hgx : (g : G) * x * (g : G)⁻¹ ∈ Subgroup.zpowers x :=
      (Subgroup.mem_normalizer_iff.mp g.2 x).mp (Subgroup.mem_zpowers x)
    have hz : Subgroup.zpowers ((g : G) * x * (g : G)⁻¹) = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hgx) (by
        rw [Nat.card_zpowers, Nat.card_zpowers, ← MulAut.conj_apply, MulEquiv.orderOf_eq])
    have hxz : x ∈ Subgroup.zpowers ((g : G) * x * (g : G)⁻¹) := hz ▸ Subgroup.mem_zpowers x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxz
    have htx : Commute h.t x := (h.commute_of_mem_F hxF).symm
    have hc : Commute w ((g : G) * x * (g : G)⁻¹) := by
      rw [← hg']
      change (g : G) * h.t * (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) =
        (g : G) * x * (g : G)⁻¹ * ((g : G) * h.t * (g : G)⁻¹)
      calc (g : G) * h.t * (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) =
          (g : G) * (h.t * x) * (g : G)⁻¹ := by group
        _ = (g : G) * (x * h.t) * (g : G)⁻¹ := by rw [htx.eq]
        _ = _ := by group
    have hwx' : w * x = x * w := by
      have := (hc.zpow_right k).eq
      rwa [hk] at this
    have hxx : x = x⁻¹ := by rw [← hwx, hwx', mul_inv_cancel_right]
    apply hx1
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [pow_two]; nth_rewrite 2 [hxx]; exact mul_inv_cancel x)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · rw [h1] at hxodd
      exact absurd hxodd (by decide)
  obtain ⟨M, hMn, hModd, hMcard⟩ := exists_normal_odd_of_kleinFour_sylow VS hVS
    (u := ⟨h.t, htN⟩) (w := ⟨w, hwN⟩) (by
      change (⟨h.t, htN⟩ : N₀) ∈ V.subgroupOf N₀
      rw [Subgroup.mem_subgroupOf]; exact htV)
    (by change (⟨w, hwN⟩ : N₀) ∈ V.subgroupOf N₀; rw [Subgroup.mem_subgroupOf]; exact hwV)
    (fun h0 => h.t_ne_one (congrArg Subtype.val h0)) (fun h0 => hw1 (congrArg Subtype.val h0))
    hnc
  set M' := M.map N₀.subtype with hM'def
  have hM'card : Nat.card M' = Nat.card M := Subgroup.card_map_of_injective N₀.subtype_injective
  have hVM' : V ≤ Subgroup.normalizer (M' : Set G) := by
    intro v hv
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    obtain ⟨m, hm, rfl⟩ := hy
    exact ⟨⟨v, hVN hv⟩ * m * ⟨v, hVN hv⟩⁻¹, hMn.conj_mem m hm _, rfl⟩
  obtain ⟨P₀, ⟨hP₀M, hP₀3, hP₀max⟩, hP₀V⟩ := CFSG.DihedralBlueprint.normalized_exists_sylow 2 3
    Nat.prime_two Nat.prime_three V M' hV2 hVM'
    ((Nat.coprime_two_left).mpr (hM'card ▸ hModd))
  change V ≤ Subgroup.normalizer (P₀ : Set G) at hP₀V
  have hdisj : Disjoint V P₀ := by
    rw [Subgroup.disjoint_def]
    intro y hyV hyP
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP₀3
    have h1 : orderOf y ∣ 4 := hV.card_four ▸ Subgroup.orderOf_dvd_natCard V hyV
    have h2 : orderOf y ∣ 3 ^ k := hk ▸ Subgroup.orderOf_dvd_natCard P₀ hyP
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right _ (by norm_num))
      h1 h2)
  set H := V ⊔ P₀ with hHdef
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP₀3
  have hHcard : Nat.card H = 4 * 3 ^ k := by
    rw [hHdef, card_sup_eq_mul_of_disjoint hP₀V hdisj, hV.card_four, hk]
  have hHprimes : ∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 2 ∨ r = 3 := by
    intro r hr hrH
    rw [hHcard, show (4 : ℕ) = 2 ^ 2 by norm_num] at hrH
    rcases (Nat.Prime.dvd_mul hr).mp hrH with h1 | h1
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h1))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h1))
  obtain ⟨⟨P₂, hP₂⟩, -⟩ := h.lemma_7_2 hp3 hHprimes (by rw [hHcard]; exact dvd_mul_right 4 _)
  have hVH : V ≤ H := le_sup_left
  have hfacH : (Nat.card H).factorization 2 = 2 := by
    rw [hHcard, Nat.factorization_mul (by norm_num) (by positivity), Finsupp.add_apply,
      show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd (by
        intro h2
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Nat.prime_three).mp
          (Nat.prime_two.dvd_of_dvd_pow h2)
        omega)]
  let VH : Sylow 2 H := Sylow.ofCard (V.subgroupOf H) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv, hV.card_four, hfacH]
    norm_num)
  have hVHn : (V.subgroupOf H).Normal := by
    have : Unique (Sylow 2 H) := Sylow.unique_of_normal P₂ hP₂
    have hVP : VH = P₂ := Subsingleton.elim _ _
    have : (VH : Subgroup H) = V.subgroupOf H := rfl
    rw [← this, hVP]
    exact hP₂
  have hP₀C : P₀ ≤ Subgroup.centralizer (V : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 : y * v * y⁻¹ ∈ V := by
      have := hVHn.conj_mem ⟨v, hVH hv⟩ (by rw [Subgroup.mem_subgroupOf]; exact hv)
        ⟨y, Subgroup.mem_sup_right hy⟩
      rw [Subgroup.mem_subgroupOf] at this
      exact this
    have h2 : v * y⁻¹ * v⁻¹ ∈ P₀ :=
      (Subgroup.mem_normalizer_iff.mp (hP₀V hv) y⁻¹).mp (P₀.inv_mem hy)
    have h3 : y * v * y⁻¹ * v⁻¹ = 1 := (Subgroup.disjoint_def.mp hdisj)
      (V.mul_mem h1 (V.inv_mem hv))
      (by rw [show y * v * y⁻¹ * v⁻¹ = y * (v * y⁻¹ * v⁻¹) by group]; exact P₀.mul_mem hy h2)
    calc v * y = (y * v * y⁻¹ * v⁻¹)⁻¹ * y * v := by group
      _ = y * v := by rw [h3, inv_one, one_mul]
  have hk0 : k = 0 := by
    by_contra hk0
    apply h.three_not_dvd_card_centralizer hp3 hV
    exact (dvd_pow_self 3 hk0).trans (hk ▸ Subgroup.card_dvd_of_le hP₀C)
  have hP₀bot : P₀ = ⊥ := by
    rw [← Subgroup.card_eq_one, hk, hk0, pow_zero]
  have hM3 : ¬ 3 ∣ Nat.card M' := by
    intro h3
    obtain ⟨⟨z, hz⟩, hzo⟩ := exists_prime_orderOf_dvd_card' (G := M') 3 h3
    have hz3 : IsPGroup 3 (Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ← hzo, Subgroup.orderOf_mk, pow_one])
    have := hP₀max (Subgroup.zpowers z) ((Subgroup.zpowers_le).mpr hz) hz3
      (hP₀bot ▸ bot_le)
    rw [hP₀bot, Subgroup.zpowers_eq_bot] at this
    rw [Subgroup.orderOf_mk, this, orderOf_one] at hzo
    omega
  have hN₀3 : ¬ 3 ∣ Nat.card N₀ := by
    rw [hMcard, ← hM'card]
    intro h3
    exact hM3 ((Nat.Coprime.dvd_mul_left (by norm_num : Nat.Coprime 3 4)).mp h3)
  intro h3
  apply hN₀3
  refine h3.trans (Subgroup.card_dvd_of_le fun y hy => ?_)
  exact mem_normalizer_zpowers_of_commute (Subgroup.mem_centralizer_singleton_iff.mp hy)

end JTHyp

end CFSG.Walter.JT
