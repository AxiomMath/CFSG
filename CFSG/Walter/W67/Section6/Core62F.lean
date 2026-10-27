module

public import CFSG.Walter.W67.Section6.Core62E
public import CFSG.LocalAnalysis.PreuniquenessRankFour.NormalRankTwo
public import CFSG.Walter.W67.Section6.Core62D

public section

namespace CFSG.Walter.W67.Sec6

variable {G : Type} [Group G] [Finite G]

theorem exists_orderOf_eq_of_ne_bot {r : ℕ} [Fact r.Prime] {H : Subgroup G} (hH : IsPGroup r H)
    (hne : H ≠ ⊥) : ∃ x ∈ H, orderOf x = r := by
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hk
    exact hne hk
  have hdvd : r ∣ Nat.card H := by rw [hk]; exact dvd_pow_self r hk0
  obtain ⟨⟨x, hx⟩, hxo⟩ := exists_prime_orderOf_dvd_card' (G := H) r hdvd
  exact ⟨x, hx, by rwa [Subgroup.orderOf_mk] at hxo⟩

namespace Hyp62

variable {r : ℕ} [Fact r.Prime] {J d x₀ y₀ : G} {P₀ P₁ M M₁ H₃ : Subgroup G}
  (h : Hyp62 r J d x₀ y₀ P₀ P₁ M M₁ H₃)
include h

variable {S : Subgroup G}

omit [Finite G] in
theorem J_y₀ : J * y₀ * J⁻¹ = y₀⁻¹ := h.P₁_inv y₀ h.y₀_mem

omit [Finite G] in
theorem y₀_pow : y₀ ^ r = 1 := by rw [← h.orderOf_y₀, pow_orderOf_eq_one]

theorem x₀_not_mem_centralizer (hS : IsPGroup r S) (hPS : P₀ ⊔ P₁ ≤ S)
    (hSP : ¬ S ≤ P₀ ⊔ P₁) : x₀ ∉ Subgroup.centralizer (S : Set G) := by
  intro hx
  apply hSP
  intro s hs
  rw [← h.inf_centralizer_eq hS hPS]
  refine ⟨hs, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  exact Subgroup.mem_centralizer_iff.mp hx s hs

theorem mem_Y_of_center (hS : IsPGroup r S) (hPS : P₀ ⊔ P₁ ≤ S)
    (hJS : J ∈ Subgroup.normalizer (S : Set G)) (hSP : ¬ S ≤ P₀ ⊔ P₁) {z : G} (hzS : z ∈ S)
    (hzC : z ∈ Subgroup.centralizer (S : Set G)) (hzr : z ^ r = 1) :
    z ∈ Subgroup.zpowers y₀ := by
  have hzP : z ∈ P₀ ⊔ P₁ := by
    rw [← h.inf_centralizer_eq hS hPS]
    refine ⟨hzS, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hzC x₀ (hPS h.x₀_mem_P)).symm
  have hzCP : z ∈ Subgroup.centralizer ((P₀ ⊔ P₁ : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hPS) hzC
  obtain ⟨a, ha, b, hb, rfl⟩ := h.mem_V_iff.mp (h.mem_V_of hzP hzCP hzr)
  have haJ : J * a * J⁻¹ = a := by
    have haP₀ : a ∈ P₀ := (Subgroup.zpowers_le.mpr h.x₀_mem) ha
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (h.P₀_le haP₀), mul_inv_cancel_right]
  have hbJ : J * b * J⁻¹ = b⁻¹ := h.P₁_inv b ((Subgroup.zpowers_le.mpr h.y₀_mem) hb)
  have hJz : J * (a * b) * J⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : J⁻¹ * s * J ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hJS) s).mp hs
      simpa using this
    have := Subgroup.mem_centralizer_iff.mp hzC _ hs'
    calc s * (J * (a * b) * J⁻¹) = J * ((J⁻¹ * s * J) * (a * b)) * J⁻¹ := by group
      _ = J * ((a * b) * (J⁻¹ * s * J)) * J⁻¹ := by rw [this]
      _ = J * (a * b) * J⁻¹ * s := by group
  have hab : a * b = b * a :=
    h.V_comm a (Subgroup.mem_sup_left ha) b (Subgroup.mem_sup_right hb)
  have ha2 : a ^ 2 ∈ Subgroup.centralizer (S : Set G) := by
    have e : a ^ 2 = (a * b) * (J * (a * b) * J⁻¹) := by
      have e1 : J * (a * b) * J⁻¹ = (J * a * J⁻¹) * (J * b * J⁻¹) := by group
      rw [e1, haJ, hbJ, pow_two]
      calc a * a = a * (b * b⁻¹) * a := by group
        _ = (a * b) * (b⁻¹ * a) := by group
        _ = (a * b) * (a * b⁻¹) := by
            rw [show b⁻¹ * a = a * b⁻¹ from by
              calc b⁻¹ * a = b⁻¹ * (a * b) * b⁻¹ := by group
                _ = b⁻¹ * (b * a) * b⁻¹ := by rw [hab]
                _ = a * b⁻¹ := by group]
    rw [e]
    exact Subgroup.mul_mem _ hzC hJz
  by_cases ha1 : a = 1
  · rw [ha1, one_mul]
    exact hb
  exfalso
  have haP₀ : a ∈ P₀ := (Subgroup.zpowers_le.mpr h.x₀_mem) ha
  have ha21 : a ^ 2 ≠ 1 := fun h2 => ha1 (h.eq_one_of_sq h.P₀_r haP₀ (by rwa [pow_two] at h2))
  have har : a ^ r = 1 := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← h.orderOf_x₀,
      pow_orderOf_eq_one, one_zpow]
  have ho : orderOf (a ^ 2) = r := by
    refine orderOf_eq_prime ?_ ha21
    rw [← pow_mul, mul_comm, pow_mul, har, one_pow]
  have hz := zpowers_eq_of_cyclic h.P₀_cyc (P₀.pow_mem haP₀ 2) h.x₀_mem (by rw [ho, h.orderOf_x₀])
  have hx : x₀ ∈ Subgroup.centralizer (S : Set G) := by
    have : x₀ ∈ Subgroup.zpowers (a ^ 2) := hz ▸ Subgroup.mem_zpowers x₀
    exact (Subgroup.zpowers_le.mpr ha2) this
  exact h.x₀_not_mem_centralizer hS hPS hSP hx

theorem y₀_mem_centralizer (hS : IsPGroup r S) (hPS : P₀ ⊔ P₁ ≤ S)
    (hJS : J ∈ Subgroup.normalizer (S : Set G)) (hSP : ¬ S ≤ P₀ ⊔ P₁) :
    y₀ ∈ Subgroup.centralizer (S : Set G) := by
  have : Nontrivial S := by
    refine ⟨⟨⟨x₀, hPS h.x₀_mem_P⟩, 1, fun h1 => h.x₀_ne_one ?_⟩⟩
    exact congrArg Subtype.val h1
  have hSr : IsPGroup r S := hS
  have hcen := hSr.center_nontrivial
  set Z := (Subgroup.center S).map S.subtype with hZ
  have hZS : Z ≤ S := Subgroup.map_subtype_le _
  have hZne : Z ≠ ⊥ := by
    intro h1
    obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center S)
    have : (z : G) ∈ Z := ⟨z, hz, rfl⟩
    rw [h1, Subgroup.mem_bot] at this
    exact hz1 (Subtype.ext (Subtype.ext this))
  have hZC : ∀ z ∈ Z, z ∈ Subgroup.centralizer (S : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have := Subgroup.mem_center_iff.mp hz ⟨s, hs⟩
    exact congrArg Subtype.val this
  obtain ⟨z, hzZ, hzo⟩ := exists_orderOf_eq_of_ne_bot (hS.to_le hZS) hZne
  have hzr : z ^ r = 1 := by rw [← hzo, pow_orderOf_eq_one]
  have hzY := h.mem_Y_of_center hS hPS hJS hSP (hZS hzZ) (hZC z hzZ) hzr
  have hzP₁ : z ∈ P₁ := (Subgroup.zpowers_le.mpr h.y₀_mem) hzY
  have heq := zpowers_eq_of_cyclic h.P₁_cyc hzP₁ h.y₀_mem (by rw [hzo, h.orderOf_y₀])
  have : y₀ ∈ Subgroup.zpowers z := heq ▸ Subgroup.mem_zpowers y₀
  exact (Subgroup.zpowers_le.mpr (hZC z hzZ)) this

theorem exists_U (hS : IsPGroup r S) (hPS : P₀ ⊔ P₁ ≤ S)
    (hJS : J ∈ Subgroup.normalizer (S : Set G)) (hSP : ¬ S ≤ P₀ ⊔ P₁) :
    ∃ U : Subgroup G, U ≤ S ∧ S ≤ Subgroup.normalizer (U : Set G) ∧ Huppert.Plane r U ∧
      y₀ ∈ U := by
  have hnc : ¬ IsCyclic S := by
    intro hc
    have := eq_of_le_cyclic hc ((Subgroup.zpowers_le.mpr h.x₀_mem_P).trans hPS)
      ((Subgroup.zpowers_le.mpr h.y₀_mem_P).trans hPS)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, h.orderOf_x₀, h.orderOf_y₀])
    have hx : x₀ ∈ Subgroup.zpowers x₀ ⊓ Subgroup.zpowers y₀ :=
      ⟨Subgroup.mem_zpowers x₀, this ▸ Subgroup.mem_zpowers x₀⟩
    rw [h.X_inf_Y, Subgroup.mem_bot] at hx
    exact h.x₀_ne_one hx
  obtain ⟨U', hU'n, hU'e, hU'c⟩ :=
    PreuniquenessRankFour.Helpers.odd_pGroup_noncyclic_has_normal_elementary_rank_two r
      h.r_ne_two _ rfl hS hnc
  set U := U'.map S.subtype with hU
  have hUS : U ≤ S := Subgroup.map_subtype_le _
  have hUc : Nat.card U = r ^ 2 := by
    rw [hU, Subgroup.card_map_of_injective S.subtype_injective, hU'c]
  have hSU : S ≤ Subgroup.normalizer (U : Set G) := by
    intro s hs
    apply JT.mem_normalizer_of_conj_mem
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨⟨s, hs⟩ * u * ⟨s, hs⟩⁻¹, hU'n.conj_mem u hu ⟨s, hs⟩, rfl⟩
  have hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := hU'e.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg (fun x : U' => ((x : S) : G)) this
  have hpow : ∀ a ∈ U, a ^ r = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have := congrArg Subtype.val (hU'e.2 a ha)
    simpa using this
  have hplane : Huppert.Plane r U :=
    ⟨fun a b => Subtype.ext (hcomm a a.2 b b.2),
      fun v => Subtype.ext (by rw [Subgroup.coe_pow, hpow v v.2]; rfl), hUc⟩
  refine ⟨U, hUS, hSU, hplane, ?_⟩
  have : Group.IsNilpotent S := hS.isNilpotent
  have hU'ne : U' ≠ ⊥ := by
    intro h1
    rw [h1, Subgroup.card_bot] at hU'c
    have := Nat.one_lt_pow (by norm_num : (2 : ℕ) ≠ 0) (Fact.out : r.Prime).one_lt
    omega
  obtain ⟨z, hz, hz1⟩ := (Subgroup.bot_or_exists_ne_one (U' ⊓ Subgroup.center S)).resolve_left
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hU'ne)
  obtain ⟨hzU', hzZ⟩ := Subgroup.mem_inf.mp hz
  have hzU : (z : G) ∈ U := ⟨z, hzU', rfl⟩
  have hzC : (z : G) ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzZ ⟨s, hs⟩)
  have hzr := hpow _ hzU
  have hzY := h.mem_Y_of_center hS hPS hJS hSP z.2 hzC hzr
  have hz1' : (z : G) ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  have hzo : orderOf (z : G) = r := orderOf_eq_prime hzr hz1'
  have heq := zpowers_eq_of_cyclic h.P₁_cyc ((Subgroup.zpowers_le.mpr h.y₀_mem) hzY) h.y₀_mem
    (by rw [hzo, h.orderOf_y₀])
  have : y₀ ∈ Subgroup.zpowers (z : G) := heq ▸ Subgroup.mem_zpowers y₀
  exact (Subgroup.zpowers_le.mpr hzU) this

theorem isT_of_mem_U (hS : IsPGroup r S) {U : Subgroup G} (hUS : U ≤ S)
    (hSU : S ≤ Subgroup.normalizer (U : Set G)) (hpl : Huppert.Plane r U) (hy₀U : y₀ ∈ U)
    (hyC : y₀ ∈ Subgroup.centralizer (S : Set G)) {u : G} (hu : u ∈ U) : IsT S y₀ r u := by
  refine ⟨hUS hu, ?_, fun s hs => ?_⟩
  · have := congrArg Subtype.val (hpl.pow ⟨u, hu⟩)
    simpa using this
  set σ := conjAut (hSU hs) with hσ
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS) ⟨s, hs⟩
  rw [Subgroup.orderOf_mk] at hk
  have hsk : s ^ r ^ k = 1 := by rw [← hk, pow_orderOf_eq_one]
  have hσk : σ ^ r ^ k = 1 := by
    refine MulEquiv.ext fun v => Subtype.ext ?_
    rw [conjAut_pow_apply, hsk, one_mul, inv_one, mul_one]
    rfl
  have hsy : s * y₀ * s⁻¹ = y₀ := by
    rw [Subgroup.mem_centralizer_iff.mp hyC s hs, mul_inv_cancel_right]
  by_cases hσ1 : σ = 1
  · have := congrArg Subtype.val (DFunLike.congr_fun hσ1 ⟨u, hu⟩)
    change s * u * s⁻¹ = u at this
    rw [this, mul_inv_cancel]
    exact Subgroup.one_mem _
  obtain ⟨e, -, hσe, hax⟩ := hpl.exists_axis hσk hσ1
  have hy1 : (⟨y₀, hy₀U⟩ : U) ≠ 1 := fun h1 => h.y₀_ne_one (congrArg Subtype.val h1)
  have heY : e ∈ Subgroup.zpowers (⟨y₀, hy₀U⟩ : U) := by
    by_contra hne
    apply hσ1
    refine hpl.mulAut_ext hy1 hne ?_ ?_
    · exact Subtype.ext (by rw [MulAut.one_apply]; exact hsy)
    · rw [MulAut.one_apply]
      exact hσe
  obtain ⟨n, hn⟩ := hax ⟨u, hu⟩
  have he' : (e : G) ∈ Subgroup.zpowers y₀ := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp heY
    rw [← hj, Subgroup.coe_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers y₀) j
  have hc : u⁻¹ * (s * u * s⁻¹) = (e : G) ^ n := by
    have := congrArg Subtype.val hn
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] at this
    exact this
  have hcY : u⁻¹ * (s * u * s⁻¹) ∈ Subgroup.zpowers y₀ := hc ▸ Subgroup.pow_mem _ he' n
  have e3 : s * u * s⁻¹ * u⁻¹ = u * (u⁻¹ * (s * u * s⁻¹)) * u⁻¹ := by group
  rw [e3, ← IsT.comm_of_mem_zpowers hyC hcY (hUS hu), mul_inv_cancel_right]
  exact hcY

omit [Finite G] in
theorem isT_y₀ (hPS : P₀ ⊔ P₁ ≤ S) (hyC : y₀ ∈ Subgroup.centralizer (S : Set G)) :
    IsT S y₀ r y₀ := by
  refine ⟨hPS h.y₀_mem_P, h.y₀_pow, fun s hs => ?_⟩
  rw [Subgroup.mem_centralizer_iff.mp hyC s hs, mul_inv_cancel_right, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem exists_w (hS : IsPGroup r S) (hPS : P₀ ⊔ P₁ ≤ S)
    (hJS : J ∈ Subgroup.normalizer (S : Set G)) (hSP : ¬ S ≤ P₀ ⊔ P₁) :
    ∃ w : G, IsT S y₀ r w ∧ w ∉ Subgroup.zpowers y₀ ∧
      (J * w * J⁻¹ = w⁻¹ ∨ w⁻¹ * (J * w * J⁻¹) ∈ Subgroup.zpowers y₀) := by
  have hyC := h.y₀_mem_centralizer hS hPS hJS hSP
  have hyr := h.y₀_pow
  have hr := h.r_odd
  obtain ⟨U, hUS, hSU, hpl, hy₀U⟩ := h.exists_U hS hPS hJS hSP
  obtain ⟨u, hu, huY⟩ : ∃ u ∈ U, u ∉ Subgroup.zpowers y₀ := by
    by_contra hcon
    push Not at hcon
    have hle : Nat.card U ≤ Nat.card (Subgroup.zpowers y₀) := Subgroup.card_le_of_le hcon
    rw [hpl.card, Nat.card_zpowers, h.orderOf_y₀] at hle
    have := (Fact.out : r.Prime).one_lt
    nlinarith
  have hut := h.isT_of_mem_U hS hUS hSU hpl hy₀U hyC hu
  have hu't := hut.conj hJS h.J_y₀
  set u' := J * u * J⁻¹ with hu'
  have hJu' : J * u' * J⁻¹ = u := by
    rw [hu']
    calc J * (J * u * J⁻¹) * J⁻¹ = (J * J) * u * (J * J)⁻¹ := by group
      _ = u := by rw [h.J_mul_J, one_mul, inv_one, mul_one]
  by_cases h2 : u * u'⁻¹ ∈ Subgroup.zpowers y₀
  · by_cases h1 : u * u' ∈ Subgroup.zpowers y₀
    · exfalso
      apply huY
      set c := u' * u * u'⁻¹ * u⁻¹ with hc
      have hcY : c ∈ Subgroup.zpowers y₀ := hut.2.2 u' hu't.1
      have hprod : (u * u') * (u * u'⁻¹) = c * (u * u) := by
        have e1 : (u * u') * (u * u'⁻¹) = u * c * u := by rw [hc]; group
        rw [e1, ← IsT.comm_of_mem_zpowers hyC hcY (hUS hu), mul_assoc]
      have hu2 : u * u ∈ Subgroup.zpowers y₀ := by
        have e2 : u * u = c⁻¹ * ((u * u') * (u * u'⁻¹)) := by rw [hprod]; group
        rw [e2]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcY) (Subgroup.mul_mem _ h1 h2)
      obtain ⟨m, hm⟩ := hr
      have e3 : u = (u * u) ^ (m + 1) := by
        rw [← pow_two, ← pow_mul, show 2 * (m + 1) = r + 1 by omega, pow_succ, hut.2.1,
          one_mul]
      rw [e3]
      exact Subgroup.pow_mem _ hu2 _
    · refine ⟨u * u', hut.mul hyC hyr hr hu't, h1, Or.inr ?_⟩
      have e : (u * u')⁻¹ * (J * (u * u') * J⁻¹) = u'⁻¹ * u⁻¹ * u'⁻¹⁻¹ * u⁻¹⁻¹ := by
        have : J * (u * u') * J⁻¹ = (J * u * J⁻¹) * (J * u' * J⁻¹) := by group
        rw [this, ← hu', hJu']
        group
      rw [e]
      exact (hut.inv hyC).2.2 _ (S.inv_mem hu't.1)
  · refine ⟨u * u'⁻¹, hut.mul hyC hyr hr (hu't.inv hyC), h2, Or.inl ?_⟩
    have : J * (u * u'⁻¹) * J⁻¹ = (J * u * J⁻¹) * (J * u' * J⁻¹)⁻¹ := by group
    rw [this, ← hu', hJu']
    group

theorem isT_x₀ (hS : IsPGroup r S) (hPS : P₀ ⊔ P₁ ≤ S)
    (hJS : J ∈ Subgroup.normalizer (S : Set G)) (hSP : ¬ S ≤ P₀ ⊔ P₁) {w : G}
    (hw : IsT S y₀ r w) (hwY : w ∉ Subgroup.zpowers y₀)
    (hwJ : w⁻¹ * (J * w * J⁻¹) ∈ Subgroup.zpowers y₀) : IsT S y₀ r x₀ := by
  have hyC := h.y₀_mem_centralizer hS hPS hJS hSP
  have hyr := h.y₀_pow
  have hr := h.r_odd
  obtain ⟨n, hn⟩ := (isOfFinOrder_of_finite y₀).mem_powers_iff_mem_zpowers.mpr hwJ
  obtain ⟨m, hm⟩ := hr
  set k := n * (m + 1) with hk
  set w' := w * y₀ ^ k with hw'
  have hJw : J * w * J⁻¹ = w * y₀ ^ n := by
    have : y₀ ^ n = w⁻¹ * (J * w * J⁻¹) := hn
    rw [this]
    group
  have hJy : J * y₀ ^ k * J⁻¹ = (y₀ ^ k)⁻¹ := by rw [← conj_pow, h.J_y₀, inv_pow]
  have hkk : y₀ ^ k * y₀ ^ k = y₀ ^ n := by
    rw [← pow_add, show k + k = r * n + n by rw [hk, hm]; ring, pow_add, pow_mul, hyr, one_pow,
      one_mul]
  have hw'J : J * w' * J⁻¹ = w' := by
    calc J * w' * J⁻¹ = (J * w * J⁻¹) * (J * y₀ ^ k * J⁻¹) := by rw [hw']; group
      _ = w * (y₀ ^ k * y₀ ^ k) * (y₀ ^ k)⁻¹ := by rw [hJw, hJy, hkk]
      _ = w' := by rw [hw']; group
  have hw't : IsT S y₀ r w' := hw.mul hyC hyr ⟨m, hm⟩ ((h.isT_y₀ hPS hyC).pow hyC hyr ⟨m, hm⟩ k)
  have hw'P₀ : w' ∈ P₀ := by
    rw [← h.inf_centralizer_J hS hPS]
    refine ⟨hw't.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc w' * J = J * w' * J⁻¹ * J := by rw [hw'J]
      _ = J * w' := by group
  have hw'X := h.mem_X_of_pow hw'P₀ hw't.2.1
  have hw'1 : w' ≠ 1 := by
    intro h1
    apply hwY
    have : w = (y₀ ^ k)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← hw']; exact h1)
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers y₀) k)
  have ho : orderOf w' = r := orderOf_eq_prime hw't.2.1 hw'1
  have heq := zpowers_eq_of_cyclic h.P₀_cyc hw'P₀ h.x₀_mem (by rw [ho, h.orderOf_x₀])
  have hx : x₀ ∈ Subgroup.zpowers w' := heq ▸ Subgroup.mem_zpowers x₀
  obtain ⟨j, hj⟩ := (isOfFinOrder_of_finite w').mem_powers_iff_mem_zpowers.mpr hx
  rw [← hj]
  exact hw't.pow hyC hyr ⟨m, hm⟩ j

end Hyp62

end CFSG.Walter.W67.Sec6
