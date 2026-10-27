module

public import CFSG.Quasithin.Recognition.HSType129a

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

theorem perm_five_three_inverted : ∀ σ : Equiv.Perm (Fin 5), σ * σ * σ = 1 → σ ≠ 1 →
    ∃ τ : Equiv.Perm (Fin 5), τ * σ * τ⁻¹ = σ⁻¹ := by
  decide +kernel

namespace HSSetting

variable {z : G} {V : Subgroup G}

theorem exists_mul_conj_eq_zpow_three [Finite G] (h : HSSetting z V) {x y : G}
    (hxH : x ∈ hsH z) (hx3 : orderOf x = 3) {k : ℤ} (hyx : y * x * y⁻¹ * (x ^ k)⁻¹ ∈ hsQ z) :
    ∃ q ∈ hsQ z, q * y * x * (q * y)⁻¹ = x ^ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxN : x ∈ Subgroup.normalizer (hsQ z : Set G) :=
    le_normalizer_quasithinGenFitting (hsH z) hxH
  set W := Subgroup.zpowers x ⊔ hsQ z with hW
  have hcardW : Nat.card W = 192 := by
    have hXN : Subgroup.zpowers x ≤ Subgroup.normalizer (hsQ z : Set G) :=
      (Subgroup.zpowers_le).mpr hxN
    have := card_sup_mul_card_inf_of_le_normalizer hXN
    rw [h.zpowers_inf_Q hx3, Subgroup.card_bot, mul_one, Nat.card_zpowers, hx3, h.card_Q] at this
    exact this
  have hxW : x ∈ W := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hx'W : y * x * y⁻¹ ∈ W := by
    have e : y * x * y⁻¹ = (y * x * y⁻¹ * (x ^ k)⁻¹) * x ^ k := by group
    rw [e]
    exact W.mul_mem (Subgroup.mem_sup_right hyx) (W.zpow_mem hxW k)
  have hx'3 : orderOf (y * x * y⁻¹) = 3 := by
    rw [show y * x * y⁻¹ = MulAut.conj y x from rfl, MulEquiv.orderOf_eq, hx3]
  have hap : IsPGroup 3 ↥(Subgroup.zpowers (⟨x, hxW⟩ : ↥W)) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx3, pow_one])
  have hbp : IsPGroup 3 ↥(Subgroup.zpowers (⟨y * x * y⁻¹, hx'W⟩ : ↥W)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx'3, pow_one])
  have hidx : ∀ c : ↥W, orderOf (c : G) = 3 → ¬ 3 ∣ (Subgroup.zpowers c).index := by
    intro c hc
    have h1 := (Subgroup.zpowers c).card_mul_index
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, hc, hcardW] at h1
    have : (Subgroup.zpowers c).index = 64 := by omega
    rw [this]
    decide
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥W (hbp.toSylow (hidx _ hx'3))
    (hap.toSylow (hidx _ hx3))
  have hgb : g * ⟨y * x * y⁻¹, hx'W⟩ * g⁻¹ ∈ Subgroup.zpowers (⟨x, hxW⟩ : ↥W) := by
    have h1 : g * ⟨y * x * y⁻¹, hx'W⟩ * g⁻¹ ∈
        (g • hbp.toSylow (hidx _ hx'3) : Sylow 3 ↥W) := by
      rw [mem_smul_sylow', show g⁻¹ * (g * ⟨y * x * y⁻¹, hx'W⟩ * g⁻¹) * g =
        ⟨y * x * y⁻¹, hx'W⟩ by group]
      exact Subgroup.mem_zpowers _
    rw [hg] at h1
    exact h1
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hgb
  have hj' : (g : G) * (y * x * y⁻¹) * (g : G)⁻¹ = x ^ j := by
    have := congrArg Subtype.val hj
    simp only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv] at this
    exact this.symm
  obtain ⟨m, q₁, hq₁, hgm⟩ := mem_sup_zpowers hxN g.2
  have hq₁' : q₁ * (y * x * y⁻¹) * q₁⁻¹ = x ^ j := by
    have e : q₁ = x ^ (-m) * (g : G) := by rw [hgm, zpow_neg]; group
    rw [e, show x ^ (-m) * (g : G) * (y * x * y⁻¹) * (x ^ (-m) * (g : G))⁻¹ =
      x ^ (-m) * ((g : G) * (y * x * y⁻¹) * (g : G)⁻¹) * (x ^ (-m))⁻¹ by group, hj',
      ← zpow_neg, ← zpow_add, ← zpow_add]
    congr 1
    ring
  refine ⟨q₁, hq₁, ?_⟩
  have hmod : x ^ j * (x ^ k)⁻¹ ∈ hsQ z := by
    have e : x ^ j * (x ^ k)⁻¹ =
        q₁ * (y * x * y⁻¹ * (x ^ k)⁻¹) * (x ^ k * q₁⁻¹ * (x ^ k)⁻¹) := by
      rw [← hq₁']
      group
    rw [e]
    exact (hsQ z).mul_mem ((hsQ z).mul_mem hq₁ hyx)
      ((Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).zpow_mem hxN k) _).mp
        ((hsQ z).inv_mem hq₁))
  have hmodX : x ^ j * (x ^ k)⁻¹ ∈ Subgroup.zpowers x :=
    (Subgroup.zpowers x).mul_mem (Subgroup.zpow_mem_zpowers x j)
      ((Subgroup.zpowers x).inv_mem (Subgroup.zpow_mem_zpowers x k))
  have h1 : x ^ j * (x ^ k)⁻¹ ∈ Subgroup.zpowers x ⊓ hsQ z := ⟨hmodX, hmod⟩
  rw [h.zpowers_inf_Q hx3, Subgroup.mem_bot] at h1
  have hxj : x ^ j = x ^ k := by
    calc x ^ j = x ^ j * (x ^ k)⁻¹ * x ^ k := by group
      _ = x ^ k := by rw [h1, one_mul]
  rw [show q₁ * y * x * (q₁ * y)⁻¹ = q₁ * (y * x * y⁻¹) * q₁⁻¹ by group, hq₁', hxj]

theorem exists_inverts_three [Finite G] (h : HSSetting z V) {x : G} (hxH : x ∈ hsH z)
    (hx3 : orderOf x = 3) : ∃ i ∈ hsH z, i * x * i⁻¹ = x⁻¹ := by
  obtain ⟨φ, hφ, hker⟩ := h.one.quot
  have hkerQ : ∀ g : ↥(hsH z), φ g = 1 ↔ (g : G) ∈ hsQ z := fun g => by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  set x' : ↥(hsH z) := ⟨x, hxH⟩
  have hxxx : x * x * x = 1 := by rw [← pow_three', ← hx3, pow_orderOf_eq_one]
  have hσ3 : φ x' * φ x' * φ x' = 1 := by
    rw [← map_mul, ← map_mul]
    have : x' * x' * x' = 1 := Subtype.ext hxxx
    rw [this, map_one]
  have hσ1 : φ x' ≠ 1 := by
    intro h1
    have hxQ : x ∈ hsQ z := (hkerQ x').mp h1
    have : x ∈ Subgroup.zpowers x ⊓ hsQ z := ⟨Subgroup.mem_zpowers x, hxQ⟩
    rw [h.zpowers_inf_Q hx3, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hx3
    exact absurd hx3 (by decide)
  obtain ⟨τ, hτ⟩ := perm_five_three_inverted _ hσ3 hσ1
  obtain ⟨y, rfl⟩ := hφ τ
  have hyx : (y : G) * x * (y : G)⁻¹ * (x ^ (-1 : ℤ))⁻¹ ∈ hsQ z := by
    have e : φ (y * x' * y⁻¹ * x') = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, hτ, inv_mul_cancel]
    have := (hkerQ _).mp e
    rw [zpow_neg, zpow_one, inv_inv]
    exact this
  obtain ⟨q, hq, hqy⟩ := h.exists_mul_conj_eq_zpow_three hxH hx3 hyx
  refine ⟨q * y, (hsH z).mul_mem (h.Q_le_H hq) y.2, ?_⟩
  rw [hqy, zpow_neg, zpow_one]

theorem exists_conj_three [Finite G] (h : HSSetting z V) {x x' : G} (hxH : x ∈ hsH z)
    (hx3 : orderOf x = 3) (hx'H : x' ∈ hsH z) (hx'3 : orderOf x' = 3) :
    ∃ g ∈ hsH z, g * x' * g⁻¹ = x ∨ g * x' * g⁻¹ = x⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set a : ↥(hsH z) := ⟨x, hxH⟩
  set b : ↥(hsH z) := ⟨x', hx'H⟩
  have hap : IsPGroup 3 ↥(Subgroup.zpowers a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx3, pow_one])
  have hbp : IsPGroup 3 ↥(Subgroup.zpowers b) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx'3, pow_one])
  have hidx : ∀ c : ↥(hsH z), orderOf (c : G) = 3 → ¬ 3 ∣ (Subgroup.zpowers c).index := by
    intro c hc
    have h1 := (Subgroup.zpowers c).card_mul_index
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, hc, h.card_H] at h1
    have : (Subgroup.zpowers c).index = 2560 := by omega
    rw [this]
    decide
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(hsH z) (hbp.toSylow (hidx _ hx'3))
    (hap.toSylow (hidx _ hx3))
  have hgb : g * b * g⁻¹ ∈ Subgroup.zpowers a := by
    have h1 : g * b * g⁻¹ ∈ (g • hbp.toSylow (hidx _ hx'3) : Sylow 3 ↥(hsH z)) := by
      rw [mem_smul_sylow', show g⁻¹ * (g * b * g⁻¹) * g = b by group]
      exact Subgroup.mem_zpowers _
    rw [hg] at h1
    exact h1
  have hgb' : (g : G) * x' * (g : G)⁻¹ ∈ Subgroup.zpowers x := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hgb
    have := congrArg Subtype.val hj
    simp only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [← this]
    exact Subgroup.zpow_mem_zpowers x j
  have hne : (g : G) * x' * (g : G)⁻¹ ≠ 1 := by
    intro h1
    have : x' = 1 := by
      calc x' = (g : G)⁻¹ * ((g : G) * x' * (g : G)⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at hx'3
    exact absurd hx'3 (by decide)
  refine ⟨g, g.2, ?_⟩
  have hxxx : x * x * x = 1 := by rw [← pow_three', ← hx3, pow_orderOf_eq_one]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hgb'
  rw [← hj] at hne ⊢
  have hx3' : x ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_three', hxxx]
  have hj3 : x ^ j = x ^ (j % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv j 3, zpow_add, zpow_mul, hx3', one_zpow, mul_one]
  have hr : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  rw [hj3] at hne ⊢
  rcases hr with hr | hr | hr
  · rw [hr, zpow_zero] at hne
    exact absurd rfl hne
  · left
    rw [hr, zpow_one]
  · right
    rw [hr, show (2 : ℤ) = 3 + (-1) by norm_num, zpow_add, hx3', one_mul, zpow_neg, zpow_one]

theorem exists_centralizer_conj [Finite G] (h : HSSetting z V) {x : G} (hxH : x ∈ hsH z)
    (hx3 : orderOf x = 3) {e g : G} (hex : e * x = x * e) (hge : g * z * g⁻¹ = e) :
    ∃ c : G, c * x = x * c ∧ c * z * c⁻¹ = e := by
  have hx''H : g⁻¹ * x * g ∈ hsH z := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [← hge] at hex
    calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [hex]
      _ = z * (g⁻¹ * x * g) := by group
  have hx''3 : orderOf (g⁻¹ * x * g) = 3 := by
    rw [show g⁻¹ * x * g = MulAut.conj g⁻¹ x by simp, MulEquiv.orderOf_eq, hx3]
  obtain ⟨k, hkH, hk⟩ := h.exists_conj_three hxH hx3 hx''H hx''3
  have hkz : k * z * k⁻¹ = z := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hkH, mul_inv_cancel_right]
  have hnz : g * k⁻¹ * z * (g * k⁻¹)⁻¹ = e := by
    have e' : k⁻¹ * z * k = z := by
      calc k⁻¹ * z * k = k⁻¹ * (k * z * k⁻¹) * k := by rw [hkz]
        _ = z := by group
    calc g * k⁻¹ * z * (g * k⁻¹)⁻¹ = g * (k⁻¹ * z * k) * g⁻¹ := by group
      _ = e := by rw [e', hge]
  have hnx : (g * k⁻¹)⁻¹ * x * (g * k⁻¹) = k * (g⁻¹ * x * g) * k⁻¹ := by group
  rcases hk with hk | hk
  · refine ⟨g * k⁻¹, ?_, hnz⟩
    rw [hk] at hnx
    calc g * k⁻¹ * x = g * k⁻¹ * ((g * k⁻¹)⁻¹ * x * (g * k⁻¹)) := by rw [hnx]
      _ = x * (g * k⁻¹) := by group
  · obtain ⟨i, hiH, hi⟩ := h.exists_inverts_three hxH hx3
    have hiz : i * z * i⁻¹ = z := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hiH, mul_inv_cancel_right]
    refine ⟨g * k⁻¹ * i, ?_, ?_⟩
    · rw [hk] at hnx
      have hi' : i⁻¹ * x⁻¹ * i = x := by
        calc i⁻¹ * x⁻¹ * i = i⁻¹ * (i * x * i⁻¹) * i := by rw [hi]
          _ = x := by group
      calc g * k⁻¹ * i * x = g * k⁻¹ * i * (i⁻¹ * x⁻¹ * i) := by rw [hi']
        _ = g * k⁻¹ * x⁻¹ * i := by group
        _ = g * k⁻¹ * ((g * k⁻¹)⁻¹ * x * (g * k⁻¹)) * i := by rw [hnx]
        _ = x * (g * k⁻¹ * i) := by group
    · calc g * k⁻¹ * i * z * (g * k⁻¹ * i)⁻¹ = g * k⁻¹ * (i * z * i⁻¹) * (g * k⁻¹)⁻¹ := by
            group
        _ = e := by rw [hiz, hnz]

end HSSetting

end CFSG.Quasithin.HSType
