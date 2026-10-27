module

public import CFSG.Quasithin.Recognition.HSTypeL12j
public import CFSG.Quasithin.Recognition.HSTypeL12b

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

theorem card_centralizer_perm_five_three : ∀ τ : Equiv.Perm (Fin 5), τ * τ * τ = 1 → τ ≠ 1 →
    (Finset.univ.filter fun σ : Equiv.Perm (Fin 5) => σ * τ = τ * σ).card = 6 := by
  decide +kernel

theorem mem_sup_zpowers {Q : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (Q : Set G))
    {g : G} (hg : g ∈ Subgroup.zpowers x ⊔ Q) : ∃ k : ℤ, ∃ q ∈ Q, g = x ^ k * q := by
  have hconj : ∀ (k : ℤ) (q : G), q ∈ Q → x ^ k * q * (x ^ k)⁻¹ ∈ Q := fun k q hq =>
    (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).zpow_mem hx k) q).mp hq
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with ⟨k, rfl⟩ | hy
    · exact ⟨k, 1, Q.one_mem, (mul_one _).symm⟩
    · exact ⟨0, y, hy, by rw [zpow_zero, one_mul]⟩
  | one => exact ⟨0, 1, Q.one_mem, by rw [zpow_zero, one_mul]⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨i, q, hq, rfl⟩ := iha
    obtain ⟨j, q', hq', rfl⟩ := ihb
    refine ⟨i + j, x ^ (-j) * q * (x ^ (-j))⁻¹ * q', Q.mul_mem (hconj _ q hq) hq', ?_⟩
    rw [zpow_add, zpow_neg, inv_inv]
    group
  | inv a _ iha =>
    obtain ⟨i, q, hq, rfl⟩ := iha
    refine ⟨-i, x ^ i * q⁻¹ * (x ^ i)⁻¹, hconj i _ (Q.inv_mem hq), ?_⟩
    rw [zpow_neg]
    group

namespace HSSetting

variable {z : G} {V : Subgroup G}

theorem zpowers_inf_Q [Finite G] (h : HSSetting z V) {x : G} (hx3 : orderOf x = 3) :
    Subgroup.zpowers x ⊓ hsQ z = ⊥ := by
  refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [Nat.card_zpowers, hx3, h.card_Q]
  norm_num

theorem exists_mul_mem_centralizer_three [Finite G] (h : HSSetting z V) {x y : G}
    (hxH : x ∈ hsH z) (hx3 : orderOf x = 3) (hyx : y * x * y⁻¹ * x⁻¹ ∈ hsQ z) :
    ∃ q ∈ hsQ z, q * y * x * (q * y)⁻¹ = x := by
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
    have e : y * x * y⁻¹ = (y * x * y⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact W.mul_mem (Subgroup.mem_sup_right hyx) hxW
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
  obtain ⟨k, q₁, hq₁, hgk⟩ := mem_sup_zpowers hxN g.2
  have hq₁' : q₁ * (y * x * y⁻¹) * q₁⁻¹ = x ^ j := by
    have e : q₁ = x ^ (-k) * (g : G) := by rw [hgk, zpow_neg]; group
    rw [e, show x ^ (-k) * (g : G) * (y * x * y⁻¹) * (x ^ (-k) * (g : G))⁻¹ =
      x ^ (-k) * ((g : G) * (y * x * y⁻¹) * (g : G)⁻¹) * (x ^ (-k))⁻¹ by group, hj',
      ← zpow_neg, ← zpow_add, ← zpow_add]
    congr 1
    ring
  refine ⟨q₁, hq₁, ?_⟩
  have hmod : x ^ j * x⁻¹ ∈ hsQ z := by
    have e : x ^ j * x⁻¹ = q₁ * (y * x * y⁻¹ * x⁻¹) * (x * q₁⁻¹ * x⁻¹) := by
      rw [← hq₁']
      group
    rw [e]
    exact (hsQ z).mul_mem ((hsQ z).mul_mem hq₁ hyx)
      ((Subgroup.mem_normalizer_iff.mp hxN _).mp ((hsQ z).inv_mem hq₁))
  have hmodX : x ^ j * x⁻¹ ∈ Subgroup.zpowers x :=
    (Subgroup.zpowers x).mul_mem (Subgroup.zpow_mem_zpowers x j)
      ((Subgroup.zpowers x).inv_mem (Subgroup.mem_zpowers x))
  have h1 : x ^ j * x⁻¹ ∈ Subgroup.zpowers x ⊓ hsQ z := ⟨hmodX, hmod⟩
  rw [h.zpowers_inf_Q hx3, Subgroup.mem_bot] at h1
  have hxj : x ^ j = x := by
    calc x ^ j = x ^ j * x⁻¹ * x := by group
      _ = x := by rw [h1, one_mul]
  rw [show q₁ * y * x * (q₁ * y)⁻¹ = q₁ * (y * x * y⁻¹) * q₁⁻¹ by group, hq₁', hxj]

theorem card_centralizer_H_three [Finite G] (h : HSSetting z V) {x : G} (hxH : x ∈ hsH z)
    (hx3 : orderOf x = 3) :
    Nat.card ↥(hsH z ⊓ Subgroup.centralizer ({x} : Set G)) = 24 := by
  classical
  obtain ⟨φ, hφ, hker⟩ := h.one.quot
  have hkerQ : ∀ g : ↥(hsH z), φ g = 1 ↔ (g : G) ∈ hsQ z := fun g => by
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  set CH := hsH z ⊓ Subgroup.centralizer ({x} : Set G) with hCH
  set ψ : ↥CH →* Equiv.Perm (Fin 5) := φ.comp (Subgroup.inclusion inf_le_left) with hψ
  have hψc : ∀ c : ↥CH, ψ c = φ ⟨c, c.2.1⟩ := fun c => rfl
  set x' : ↥(hsH z) := ⟨x, hxH⟩
  have hZ : hsZQ z ≤ CH := by
    rw [← h.centralizer_Q_eq_ZQ_of_orderOf_three hxH hx3]
    exact le_inf (inf_le_left.trans h.Q_le_H) inf_le_right
  have hkerψ : ψ.ker = (hsZQ z).subgroupOf CH := by
    ext c
    rw [MonoidHom.mem_ker, hψc, hkerQ, Subgroup.mem_subgroupOf,
      ← h.centralizer_Q_eq_ZQ_of_orderOf_three hxH hx3]
    exact ⟨fun hc => ⟨hc, c.2.2⟩, fun hc => hc.1⟩
  have hcardker : Nat.card ψ.ker = 4 := by
    rw [hkerψ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ).toEquiv, h.card_ZQ]
  have hrange : ψ.range = Subgroup.centralizer ({φ x'} : Set (Equiv.Perm (Fin 5))) := by
    ext σ
    rw [MonoidHom.mem_range, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, rfl⟩
      rw [hψc, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2.2)
    · intro hσ
      obtain ⟨y, rfl⟩ := hφ σ
      have hyx : (y : G) * x * (y : G)⁻¹ * x⁻¹ ∈ hsQ z := by
        have : φ (y * x' * y⁻¹ * x'⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, hσ]
          group
        exact (hkerQ _).mp this
      obtain ⟨q, hq, hqy⟩ := h.exists_mul_mem_centralizer_three hxH hx3 hyx
      have hmem : q * y ∈ CH := ⟨(hsH z).mul_mem (h.Q_le_H hq) y.2,
        Subgroup.mem_centralizer_singleton_iff.mpr (by
          calc q * y * x = q * y * x * (q * y)⁻¹ * (q * y) := by group
            _ = x * (q * y) := by rw [hqy])⟩
      refine ⟨⟨_, hmem⟩, ?_⟩
      show φ (⟨q, h.Q_le_H hq⟩ * y) = φ y
      rw [map_mul, (hkerQ ⟨q, h.Q_le_H hq⟩).mpr hq, one_mul]
  have hφx3 : φ x' * φ x' * φ x' = 1 := by
    rw [← map_mul, ← map_mul]
    have : x' * x' * x' = 1 := Subtype.ext (by
      show x * x * x = 1
      rw [← pow_three', ← hx3, pow_orderOf_eq_one])
    rw [this, map_one]
  have hφx1 : φ x' ≠ 1 := by
    intro h1
    have hxQ := (hkerQ x').mp h1
    have h2 : x ∈ Subgroup.zpowers x ⊓ hsQ z := ⟨Subgroup.mem_zpowers x, hxQ⟩
    rw [h.zpowers_inf_Q hx3, Subgroup.mem_bot] at h2
    rw [h2, orderOf_one] at hx3
    exact absurd hx3 (by norm_num)
  have hcardrange : Nat.card ψ.range = 6 := by
    rw [hrange, ← card_centralizer_perm_five_three (φ x') hφx3 hφx1, Nat.card_eq_fintype_card,
      ← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun π =>
      Subgroup.mem_centralizer_singleton_iff)
  have := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hcardrange,
    hcardker] at this
  exact this

end HSSetting

end CFSG.Quasithin.HSType
