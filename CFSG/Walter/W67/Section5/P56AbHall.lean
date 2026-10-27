module

public import CFSG.Walter.W67.Section5.P56AbGLv

public section

namespace CFSG.Walter.W67

open P56Ab

namespace P56AbData

variable {G : Type} [Group G] [Finite G] (d : P56AbData G)

theorem exists_sylow_two_Nbar : ∃ S : Sylow 2 d.Nbar, IsCyclic S ∧ Nat.card S ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 d.Nbar))
  have hS : Nat.card S ≤ 2 := by
    have h := d.card_le_two_of_le_Nbar (Subgroup.map_subtype_le (S : Subgroup d.Nbar))
      (S.isPGroup'.map _)
    rwa [Subgroup.card_map_of_injective d.Nbar.subtype_injective] at h
  refine ⟨S, ?_, hS⟩
  rcases Nat.lt_or_ge (Nat.card S) 2 with h | h
  · have h1 : Nat.card S = 1 := by have := Nat.card_pos (α := S); omega
    have : Subsingleton S := (Nat.card_eq_one_iff_unique.mp h1).1
    exact isCyclic_of_subsingleton
  · have h2 : Nat.card S = 2 := le_antisymm hS h
    exact isCyclic_of_prime_card h2

noncomputable abbrev Kbar : Subgroup (MulAut d.V) := (pPrimeCore 2 d.Nbar).map d.Nbar.subtype

theorem Kbar_le_Nbar : d.Kbar ≤ d.Nbar := Subgroup.map_subtype_le _

theorem Nbar_le_normalizer_Kbar : d.Nbar ≤ Subgroup.normalizer (d.Kbar : Set (MulAut d.V)) := by
  intro α hα
  apply Sec53.mem_normalizer_of_conj_le
  rintro _ ⟨β, hβ, rfl⟩
  have : (pPrimeCore 2 d.Nbar).Normal := Subgroup.sSup_normal _ fun _ hK => hK.1
  exact ⟨_, this.conj_mem β hβ ⟨α, hα⟩, rfl⟩

theorem odd_card_Kbar : Odd (Nat.card d.Kbar) := by
  obtain ⟨S, hS, -⟩ := d.exists_sylow_two_Nbar
  rw [Subgroup.card_map_of_injective d.Nbar.subtype_injective]
  exact (cyclic_sylow_normal_odd_complement S hS).2.2.2.1.2.1

theorem card_Nbar_eq : ∃ s ≤ 2, 0 < s ∧ Nat.card d.Nbar = Nat.card d.Kbar * s := by
  obtain ⟨S, hS, hS2⟩ := d.exists_sylow_two_Nbar
  have h := cyclic_sylow_normal_odd_complement S hS
  refine ⟨Nat.card S, hS2, Nat.card_pos, ?_⟩
  rw [Subgroup.card_map_of_injective d.Nbar.subtype_injective]
  have hidx := h.2.2.2.1.2.2.1
  rw [← hidx, Subgroup.card_mul_index]

theorem factorization_three_Kbar :
    (Nat.card d.Kbar).factorization 3 = (Nat.card d.Nbar).factorization 3 := by
  obtain ⟨s, hs2, hs0, h⟩ := d.card_Nbar_eq
  rw [h, Nat.factorization_mul Nat.card_pos.ne' hs0.ne', Finsupp.add_apply]
  have : s.factorization 3 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h3
    have := Nat.le_of_dvd hs0 h3
    omega
  rw [this, add_zero]

theorem mem_Kbar_of_odd {α : MulAut d.V} (hα : α ∈ d.Nbar) (hodd : Odd (orderOf α)) :
    α ∈ d.Kbar := by
  obtain ⟨S, hS, hS2⟩ := d.exists_sylow_two_Nbar
  have h := cyclic_sylow_normal_odd_complement S hS
  set K := pPrimeCore 2 d.Nbar
  have hKn : K.Normal := h.2.2.2.1.1
  have hidx : K.index = Nat.card S := h.2.2.2.1.2.2.1
  set x : d.Nbar := ⟨α, hα⟩
  have hx : (x : d.Nbar ⧸ K) = 1 := by
    have h1 : orderOf (x : d.Nbar ⧸ K) ∣ orderOf x := orderOf_map_dvd (QuotientGroup.mk' K) x
    have h2 : orderOf (x : d.Nbar ⧸ K) ∣ Nat.card (d.Nbar ⧸ K) := orderOf_dvd_natCard _
    rw [← Subgroup.index, hidx] at h2
    have h3 : orderOf (x : d.Nbar ⧸ K) ≤ 2 := (Nat.le_of_dvd Nat.card_pos h2).trans hS2
    have hox : Odd (orderOf x) := by rwa [Subgroup.orderOf_mk]
    have h4 : Odd (orderOf (x : d.Nbar ⧸ K)) := Odd.of_dvd_nat hox h1
    have h5 : orderOf (x : d.Nbar ⧸ K) ≠ 0 := (orderOf_pos _).ne'
    have : orderOf (x : d.Nbar ⧸ K) = 1 := by
      obtain ⟨k, hk⟩ := h4
      omega
    exact orderOf_eq_one_iff.mp this
  rw [QuotientGroup.eq_one_iff] at hx
  exact ⟨x, hx, rfl⟩

theorem Jbar_not_mem_Kbar : d.Jbar ∉ d.Kbar := by
  intro h
  have h1 : orderOf d.Jbar ∣ Nat.card d.Kbar := by
    rw [← Subgroup.orderOf_mk d.Jbar h]
    exact orderOf_dvd_natCard _
  rw [d.orderOf_Jbar] at h1
  exact (Nat.not_even_iff_odd.mpr d.odd_card_Kbar) (even_iff_two_dvd.mpr h1)

@[expose] noncomputable def conjOf {A : Type*} [Group A] {Y : Subgroup A} {g : A}
    (hg : g ∈ Subgroup.normalizer (Y : Set A)) : MulAut Y :=
  conjAut (Subgroup.zpowers g) Y (Subgroup.zpowers_le.mpr hg) ⟨g, Subgroup.mem_zpowers g⟩

omit [Finite G] in
theorem conjOf_apply_coe {A : Type*} [Group A] {Y : Subgroup A} {g : A}
    (hg : g ∈ Subgroup.normalizer (Y : Set A)) (y : Y) :
    ((conjOf hg y : Y) : A) = g * y * g⁻¹ := rfl

theorem mem_normalizer_map_of_characteristic {A : Type} [Group A] [Finite A] {Y : Subgroup A}
    {C : Subgroup Y} (hC : C.Characteristic) {g : A} (hg : g ∈ Subgroup.normalizer (Y : Set A)) :
    g ∈ Subgroup.normalizer ((C.map Y.subtype : Subgroup A) : Set A) := by
  apply Sec53.mem_normalizer_of_conj_le
  rintro _ ⟨c, hc, rfl⟩
  have := Subgroup.characteristic_iff_map_le.mp hC (conjOf hg) ⟨c, hc, rfl⟩
  exact ⟨_, this, rfl⟩

theorem le_normalizer_map_of_normal {A : Type} [Group A] [Finite A] {Y : Subgroup A}
    {C : Subgroup Y} (hC : C.Normal) :
    Y ≤ Subgroup.normalizer ((C.map Y.subtype : Subgroup A) : Set A) := by
  intro y hy
  apply Sec53.mem_normalizer_of_conj_le
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨_, hC.conj_mem c hc ⟨y, hy⟩, rfl⟩

section hall

variable {v : ℕ} [hv : Fact v.Prime]

abbrev π3v (v : ℕ) [hv : Fact v.Prime] : Set Nat.Primes := {⟨3, Nat.prime_three⟩, ⟨v, hv.out⟩}

theorem odd_orderOf_of_mem_bar_U {α : MulAut d.V} (hα : α ∈ d.bar (d.U v))
    (hvn : orderOf (3 : ZMod v) = d.n) : Odd (orderOf α) := by
  have hUp : IsPGroup v (d.bar (d.U v)) :=
    (show IsPGroup v ((d.U v).subgroupOf d.NV) from
      d.U_isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe d.U_le_NV).symm).map d.φ
  obtain ⟨k, hk⟩ := hUp ⟨α, hα⟩
  have h1 : orderOf α ∣ v ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hv.out).mp h1
  rw [hj]
  exact Odd.pow (hv.out.odd_of_ne_two (d.v_ne_two hvn))

theorem bar_U_le_Kbar (hvn : orderOf (3 : ZMod v) = d.n) : d.bar (d.U v) ≤ d.Kbar :=
  fun _ hα => d.mem_Kbar_of_odd (d.bar_le_Nbar _ hα) (d.odd_orderOf_of_mem_bar_U hα hvn)

theorem bar_P₀_isPGroup : IsPGroup 3 (d.bar d.P₀) :=
  (d.P₀_isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe d.P₀_le_NV).symm).map d.φ

theorem bar_P₀_le_Kbar : d.bar d.P₀ ≤ d.Kbar := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro α hα
  apply d.mem_Kbar_of_odd (d.bar_le_Nbar _ hα)
  obtain ⟨k, hk⟩ := d.bar_P₀_isPGroup ⟨α, hα⟩
  have h1 : orderOf α ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
  rw [hj]
  exact Odd.pow (by decide)

theorem comm_Jbar_of_mem_bar {X : Subgroup G} (hXJ : X ≤ Subgroup.centralizer ({d.J} : Set G))
    {α : MulAut d.V} (hα : α ∈ d.bar X) : α * d.Jbar = d.Jbar * α := by
  obtain ⟨x, hx, rfl⟩ := d.mem_bar.mp hα
  exact d.phi_comm_Jbar_of_comm x.2 (Subgroup.mem_centralizer_singleton_iff.mp (hXJ hx))

theorem mem_normalizer_of_comm {A : Type} [Group A] [Finite A] {X : Subgroup A} {g : A}
    (hg : ∀ x ∈ X, x * g = g * x) : g ∈ Subgroup.normalizer (X : Set A) := by
  apply Sec53.mem_normalizer_of_conj_le
  intro x hx
  rw [← hg x hx, mul_inv_cancel_right]
  exact hx

noncomputable abbrev Lbar (v : ℕ) : Subgroup (MulAut d.V) := d.bar (d.U v) ⊔ d.bar d.P₀

theorem Lbar_le_Kbar (hvn : orderOf (3 : ZMod v) = d.n) : d.Lbar v ≤ d.Kbar :=
  sup_le (d.bar_U_le_Kbar hvn) d.bar_P₀_le_Kbar

omit hv in
theorem Jbar_mem_normalizer_Lbar :
    d.Jbar ∈ Subgroup.normalizer (d.Lbar v : Set (MulAut d.V)) :=
  mem_normalizer_sup' (mem_normalizer_of_comm fun _ hx =>
      d.comm_Jbar_of_mem_bar d.U_le_centralizer_J hx)
    (mem_normalizer_of_comm fun _ hx =>
      d.comm_Jbar_of_mem_bar (d.P₀_le.trans d.E_le) hx)

end hall

section hall2

variable {v : ℕ} [hv : Fact v.Prime]

omit hv in
theorem bar_U_isPGroup : IsPGroup v (d.bar (d.U v)) :=
  (show IsPGroup v ((d.U v).subgroupOf d.NV) from
    d.U_isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe d.U_le_NV).symm).map d.φ

theorem isPiSubgroup_Lbar : IsPiSubgroup (π3v v) (d.Lbar v) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPU : d.bar d.P₀ ≤ Subgroup.normalizer (d.bar (d.U v) : Set (MulAut d.V)) :=
    (d.bar_mono d.P₀_le_H).trans (d.bar_le_normalizer d.H_le_normalizer_U)
  have h := Sec52.card_sup_mul_card_inf hPU
  rw [sup_comm] at h
  intro p hp
  have hp' : p.val ∣ Nat.card (d.bar (d.U v)) * Nat.card (d.bar d.P₀) :=
    hp.trans (Dvd.intro _ h)
  rcases (Nat.Prime.dvd_mul p.2).mp hp' with h1 | h1
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (d.bar_U_isPGroup (v := v))
    rw [hk] at h1
    have := (Nat.prime_dvd_prime_iff_eq p.2 hv.out).mp (p.2.dvd_of_dvd_pow h1)
    right
    exact Subtype.ext this
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp d.bar_P₀_isPGroup
    rw [hk] at h1
    have := (Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_three).mp (p.2.dvd_of_dvd_pow h1)
    left
    exact Subtype.ext this

theorem coprime_zpowers_Jbar {K : Subgroup (MulAut d.V)} (hK : Odd (Nat.card K)) :
    Nat.Coprime (Nat.card (Subgroup.zpowers d.Jbar)) (Nat.card K) := by
  rw [Nat.card_zpowers, d.orderOf_Jbar]
  exact Nat.coprime_two_left.mpr hK

theorem zpowers_Jbar_le_normalizer_Kbar :
    Subgroup.zpowers d.Jbar ≤ Subgroup.normalizer (d.Kbar : Set (MulAut d.V)) :=
  Subgroup.zpowers_le.mpr (d.Nbar_le_normalizer_Kbar d.Jbar_mem_Nbar)

theorem exists_Y (hvn : orderOf (3 : ZMod v) = d.n) :
    ∃ Y : Subgroup (MulAut d.V), Y ≤ d.Kbar ∧ IsHallSubgroup (π3v v) (Y.subgroupOf d.Kbar) ∧
      Subgroup.zpowers d.Jbar ≤ Subgroup.normalizer (Y : Set (MulAut d.V)) ∧ d.Lbar v ≤ Y :=
  exists_hall_invariant d.zpowers_Jbar_le_normalizer_Kbar (isSolvable_of_odd d.odd_card_Kbar)
    (d.coprime_zpowers_Jbar d.odd_card_Kbar) (d.Lbar_le_Kbar hvn) d.isPiSubgroup_Lbar
    (Subgroup.zpowers_le.mpr d.Jbar_mem_normalizer_Lbar)

theorem odd_card_of_le_Kbar {Y : Subgroup (MulAut d.V)} (hYK : Y ≤ d.Kbar) : Odd (Nat.card Y) :=
  Odd.of_dvd_nat d.odd_card_Kbar (Subgroup.card_dvd_of_le hYK)

theorem pCore_three_Y_eq_bot
    (hvn : orderOf (3 : ZMod v) = d.n) {Y : Subgroup (MulAut d.V)}
    (hYK : Y ≤ d.Kbar) (hJY : Subgroup.zpowers d.Jbar ≤ Subgroup.normalizer (Y : Set (MulAut d.V)))
    (hLY : d.Lbar v ≤ Y) : pCore 3 Y = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX := d.eq_bot_of_normalized hvn (X := (pCore 3 Y).map Y.subtype)
    ((Subgroup.map_subtype_le _).trans (hYK.trans d.Kbar_le_Nbar))
    ((pCore_isPGroup (p := 3) (G := Y)).map Y.subtype)
    (mem_normalizer_map_of_characteristic (pCore_characteristic (p := 3) (G := Y))
      (hJY (Subgroup.mem_zpowers _)))
    ((le_sup_left.trans hLY).trans (le_normalizer_map_of_normal (pCore_normal (p := 3) (G := Y))))
  exact (Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).mp hX

theorem pPrimeCore_v_Y_eq_bot {Y : Subgroup (MulAut d.V)}
    (hYHall : IsHallSubgroup (π3v v) (Y.subgroupOf d.Kbar)) (hYK : Y ≤ d.Kbar)
    (hO3 : pCore 3 Y = ⊥) : pPrimeCore v Y = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply sSup_eq_bot.mpr
  rintro K ⟨hKn, hKv⟩
  have hK3 : IsPGroup 3 K := by
    have hKcard : Nat.card K = 3 ^ (Nat.card K).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' (fun {q} hq hqK => by
        have hqY : q ∣ Nat.card (Y.subgroupOf d.Kbar) := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYK).toEquiv]
          exact hqK.trans (Subgroup.card_subgroup_dvd_card K)
        have hmem := hYHall.p_in_pi_of_p_dvd_card ⟨q, hq⟩ hqY
        rcases hmem with h | h
        · exact congrArg Subtype.val h
        · exfalso
          have hqv : q = v := congrArg Subtype.val h
          rw [hqv] at hqK
          exact (Nat.Prime.coprime_iff_not_dvd hv.out).mp hKv hqK)
    exact IsPGroup.of_card hKcard
  have : K ≤ pCore 3 Y := le_sSup ⟨hKn, hK3⟩
  rw [hO3] at this
  exact le_bot_iff.mp this

end hall2

section qbar

variable {v : ℕ} [hv : Fact v.Prime]

theorem three_dvd_v_sub_one (hvn : orderOf (3 : ZMod v) = d.n) : 3 ∣ v - 1 := by
  have h3 : (3 : ZMod v) ≠ 0 := three_ne_zero_zmod (by
    rintro rfl
    have h0 : (3 : ZMod 3) = 0 := rfl
    rw [h0, orderOf_eq_zero_iff.mpr] at hvn
    · have := d.three_le_n
      omega
    · rw [isOfFinOrder_iff_pow_eq_one]
      rintro ⟨k, hk, hk1⟩
      rw [zero_pow hk.ne'] at hk1
      exact zero_ne_one hk1)
  have := ZMod.orderOf_dvd_card_sub_one h3
  rw [hvn] at this
  exact d.three_dvd_n.trans this

theorem eq_one_of_mem_of_isPGroup {A : Type*} [Group A] {X Y : Subgroup A} {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) (hX : IsPGroup p X) (hY : IsPGroup q Y)
    {x : A} (hxX : x ∈ X) (hxY : x ∈ Y) : x = 1 := by
  obtain ⟨a, ha⟩ := hX ⟨x, hxX⟩
  obtain ⟨b, hb⟩ := hY ⟨x, hxY⟩
  have h1 : orderOf x ∣ p ^ a := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val ha)
  have h2 : orderOf x ∣ q ^ b := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hb)
  have hcop : Nat.Coprime (p ^ a) (q ^ b) :=
    Nat.Coprime.pow a b ((Nat.coprime_primes Fact.out Fact.out).mpr hpq)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem exists_Qbar
    (hvn : orderOf (3 : ZMod v) = d.n) :
    ∃ Q : Subgroup (MulAut d.V), Q ≤ d.Kbar ∧ IsPGroup 3 Q ∧
      (Nat.card Q).factorization 3 = (Nat.card d.Nbar).factorization 3 ∧
      Subgroup.zpowers d.Jbar ≤ Subgroup.normalizer (Q : Set (MulAut d.V)) ∧ d.bar d.P₀ ≤ Q ∧
      (∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) ∧
      ∀ E : Subgroup (MulAut d.V), E ≤ Q → (∀ x ∈ E, x ^ 3 = 1) → Nat.card E ≤ 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hv3 : v ≠ 3 := by
    intro h
    have := d.three_dvd_v_sub_one hvn
    rw [h] at this
    norm_num at this
  obtain ⟨Y, hYK, hYHall, hJY, hLY⟩ := d.exists_Y hvn
  have hYodd := d.odd_card_of_le_Kbar hYK
  have hYsolv : Group.IsSolvable Y := isSolvable_of_odd hYodd
  have hO3 := d.pCore_three_Y_eq_bot hvn hYK hJY hLY
  have hOv' := d.pPrimeCore_v_Y_eq_bot hYHall hYK hO3
  have hF : fittingSubgroup Y = pCore v Y := Fitting_eq_pcore Y v hOv'
  have hCF := centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hYsolv
  rw [hF] at hCF
  set V₀ : Subgroup (MulAut d.V) := (pCore v Y).map Y.subtype with hV₀
  have hV₀p : IsPGroup v V₀ := (pCore_isPGroup (p := v) (G := Y)).map Y.subtype
  obtain ⟨hV₀comm, hV₀small⟩ := d.vsubgroup_mulAut hvn hV₀p
  have hPY : d.bar d.P₀ ≤ Y := le_sup_right.trans hLY
  obtain ⟨Q, hQY, hQHall, hJQ, hPQ⟩ := exists_hall_invariant hJY hYsolv
    (d.coprime_zpowers_Jbar hYodd) hPY (isPiSubgroup_iff_isPGroup.mpr d.bar_P₀_isPGroup)
    (Subgroup.zpowers_le.mpr (mem_normalizer_of_comm fun _ hx =>
      d.comm_Jbar_of_mem_bar (d.P₀_le.trans d.E_le) hx))
  have hQp : IsPGroup 3 Q := (isPiSubgroup_iff_isPGroup.mp hQHall.p_in_pi_of_p_dvd_card).of_equiv
    (Subgroup.subgroupOfEquivOfLe hQY)
  have hQV₀ : Q ≤ Subgroup.normalizer (V₀ : Set (MulAut d.V)) :=
    hQY.trans (le_normalizer_map_of_normal (pCore_normal (p := v) (G := Y)))
  have hfaith : ∀ q ∈ Q, (∀ w ∈ V₀, q * w = w * q) → q = 1 := by
    intro q hq hqw
    have hqC : (⟨q, hQY hq⟩ : Y) ∈ Subgroup.centralizer ((pCore v Y : Subgroup Y) : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact Subtype.ext (hqw _ ⟨w, hw, rfl⟩).symm
    have hqV : q ∈ V₀ := ⟨_, hCF hqC, rfl⟩
    exact eq_one_of_mem_of_isPGroup hv3.symm hQp hV₀p hq hqV
  let W : Subgroup (MulAut d.V) :=
    { carrier := {w | w ∈ V₀ ∧ w ^ v = 1}
      one_mem' := ⟨V₀.one_mem, one_pow _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        exact ⟨V₀.mul_mem ha hb, by
          rw [(Commute.mul_pow (hV₀comm a ha b hb) v), ha', hb', one_mul]⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨V₀.inv_mem ha, by rw [inv_pow, ha', inv_one]⟩ }
  have hWV₀ : W ≤ V₀ := fun _ hw => hw.1
  have hQW : Q ≤ Subgroup.normalizer (W : Set (MulAut d.V)) := by
    intro q hq
    apply Sec53.mem_normalizer_of_conj_le
    rintro w ⟨hw, hw'⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hQV₀ hq) w).mp hw, by rw [conj_pow, hw', mul_one,
      mul_inv_cancel]⟩
  set ψ := conjAut Q W hQW
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro q hq
    rw [MonoidHom.mem_ker, conjAut_eq_one_iff] at hq
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply hfaith q q.2
    set α := conjOf (hQV₀ q.2) with hαdef
    have hαord : Nat.Coprime (orderOf α) v := by
      obtain ⟨k, hk⟩ := hQp q
      have h1 : orderOf (q : MulAut d.V) ∣ 3 ^ k :=
        orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
      have h2 : orderOf α ∣ orderOf (q : MulAut d.V) := by
        have := orderOf_map_dvd (conjAut (Subgroup.zpowers (q : MulAut d.V)) V₀
          (Subgroup.zpowers_le.mpr (hQV₀ q.2))) ⟨(q : MulAut d.V), Subgroup.mem_zpowers _⟩
        rwa [Subgroup.orderOf_mk] at this
      exact Nat.Coprime.coprime_dvd_left (h2.trans h1)
        (Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_three hv.out).mpr hv3.symm))
    have hα : α = 1 := eq_one_of_forall_pow_eq_one hV₀p
      (fun a b => Subtype.ext (hV₀comm a a.2 b b.2)) α hαord (by
        intro x hx
        apply Subtype.ext
        rw [conjOf_apply_coe]
        have hxW : (x : MulAut d.V) ∈ W := ⟨x.2, by simpa using congrArg Subtype.val hx⟩
        rw [hq _ hxW, mul_inv_cancel_right])
    intro w hw
    have h1 := congrArg (fun β : MulAut V₀ => ((β ⟨w, hw⟩ : V₀) : MulAut d.V)) hα
    have h2 : (q : MulAut d.V) * w * (q : MulAut d.V)⁻¹ = w := h1
    calc (q : MulAut d.V) * w = (q : MulAut d.V) * w * (q : MulAut d.V)⁻¹ * q := by group
      _ = w * q := by rw [h2]
  have hWcomm : ∀ a b : W, a * b = b * a := fun a b =>
    Subtype.ext (hV₀comm a (hWV₀ a.2) b (hWV₀ b.2))
  have hWpow : ∀ w : W, w ^ v = 1 := fun w => Subtype.ext (by simpa using w.2.2)
  have hWp : IsPGroup v W := hV₀p.to_le hWV₀
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hWp
  have hr2 : r ≤ 2 := by
    have := hV₀small W hWV₀ (fun x hx => hx.2)
    rw [hr] at this
    exact (Nat.pow_le_pow_iff_right hv.out.one_lt).mp this
  obtain ⟨hRcomm, hRsmall⟩ := isMulCommutative_and_card_le_of_mulAut hWcomm hWpow hr2 hr
    (d.three_dvd_v_sub_one hvn) ψ.range (hQp.of_surjective ψ.rangeRestrict
      ψ.rangeRestrict_surjective)
  have hfac : (Nat.card Q).factorization 3 = (Nat.card d.Nbar).factorization 3 := by
    have h1 := Subgroup.card_mul_index (Q.subgroupOf Y)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQY).toEquiv] at h1
    have h2 := Subgroup.card_mul_index (Y.subgroupOf d.Kbar)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYK).toEquiv] at h2
    have hi1 : ¬ 3 ∣ (Q.subgroupOf Y).index := fun h3 =>
      hQHall.p_in_pi_of_p_dvd_index ⟨3, Nat.prime_three⟩ h3 rfl
    have hi2 : ¬ 3 ∣ (Y.subgroupOf d.Kbar).index := fun h3 =>
      hYHall.p_in_pi_of_p_dvd_index ⟨3, Nat.prime_three⟩ h3 (Or.inl rfl)
    have hne1 : (Q.subgroupOf Y).index ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at h1; exact Nat.card_pos.ne' h1.symm
    have hne2 : (Y.subgroupOf d.Kbar).index ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at h2; exact Nat.card_pos.ne' h2.symm
    rw [← d.factorization_three_Kbar, ← h2, ← h1, Nat.factorization_mul (Nat.mul_ne_zero
      Nat.card_pos.ne' hne1) hne2, Nat.factorization_mul Nat.card_pos.ne' hne1,
      Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hi1,
      Nat.factorization_eq_zero_of_not_dvd hi2, add_zero, add_zero]
  refine ⟨Q, hQY.trans hYK, hQp, hfac, hJQ, hPQ, ?_, ?_⟩
  · intro a ha b hb
    have h := hψ.eq_iff (a := ⟨a, ha⟩ * ⟨b, hb⟩) (b := ⟨b, hb⟩ * ⟨a, ha⟩)
    have : ψ (⟨a, ha⟩ * ⟨b, hb⟩) = ψ (⟨b, hb⟩ * ⟨a, ha⟩) := by
      rw [map_mul, map_mul]
      exact hRcomm _ ⟨_, rfl⟩ _ ⟨_, rfl⟩
    exact congrArg Subtype.val (h.mp this)
  · intro E hEQ hE
    have hEcard : Nat.card E = Nat.card ((E.subgroupOf Q).map ψ) := by
      rw [Subgroup.card_map_of_injective hψ,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEQ).toEquiv]
    rw [hEcard]
    refine hRsmall _ (Subgroup.map_le_range _ _) ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (by simpa using hE _ hx)
    rw [this, map_one]

end qbar


end P56AbData

end CFSG.Walter.W67
