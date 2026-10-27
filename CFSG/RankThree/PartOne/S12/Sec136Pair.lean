module

public import CFSG.RankThree.PartOne.S12.InvolAbelian
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne.Invol

open CFSG.RankThree.PartOne.Torsion37

variable {M : Type*} [CommGroup M]

theorem apply_mul_zpow (σ : MulAut M) (b c : M) (i : ℤ) : σ (b * c ^ i) = σ b * (σ c) ^ i := by
  rw [map_mul, map_zpow]

structure UData (p : ℕ) (c : M) (u : MulAut M) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  pow : ∀ x : M, x ^ p = 1
  card : Nat.card M = p ^ 4
  order_c : orderOf c = p
  u_sq : u * u = 1
  fix_u : fixS u = Subgroup.zpowers c

namespace UData

variable {p : ℕ} {c : M} {u : MulAut M} (Z : UData p c u)

include Z

theorem sq_eq_one {x : M} (h : x * x = 1) : x = 1 := by
  have h2 : x ^ 2 = 1 := by rw [pow_two]; exact h
  have h4 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have h5 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (Z.pow x)
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two Z.prime).2 (Ne.symm Z.ne_two)
  have h6 : orderOf x ∣ 1 := hcop ▸ Nat.dvd_gcd h4 h5
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h6)

theorem u_c : u c = c := by
  have : c ∈ fixS u := by rw [Z.fix_u]; exact Subgroup.mem_zpowers c
  exact this

theorem card_fixS_u : Nat.card (fixS u) = p := by
  rw [Z.fix_u, Nat.card_zpowers, Z.order_c]

theorem card_invS_u [Finite M] : Nat.card (invS u) = p ^ 3 := by
  have h := card_eq_mul Z.prime Z.ne_two Z.pow Z.u_sq
  rw [Z.card, Z.card_fixS_u] at h
  have hp : 0 < p := Z.prime.pos
  have h' : p * p ^ 3 = p * Nat.card (invS u) := by rw [← h]; ring
  exact (Nat.eq_of_mul_eq_mul_left hp h').symm

theorem zpowers_inf_invS : Subgroup.zpowers c ⊓ invS u = ⊥ := by
  rw [← Z.fix_u]
  exact fixS_inf_invS Z.prime Z.ne_two Z.pow

theorem zpow_eq_one_of_mem {n : ℤ} (h : c ^ n ∈ invS u) : c ^ n = 1 := by
  have h1 : c ^ n ∈ Subgroup.zpowers c ⊓ invS u := ⟨Subgroup.zpow_mem_zpowers c n, h⟩
  rw [Z.zpowers_inf_invS] at h1
  exact h1

theorem exists_mul_zpow (x : M) : ∃ b ∈ invS u, ∃ i : ℤ, x = b * c ^ i := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_involution Z.prime Z.ne_two Z.pow Z.u_sq x
  rw [Z.fix_u] at ha
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  exact ⟨b, hb, i, mul_comm _ _⟩

theorem eq_of_mul_zpow_eq {b₁ b₂ : M} (h₁ : b₁ ∈ invS u) (h₂ : b₂ ∈ invS u) {i j : ℤ}
    (h : b₁ * c ^ i = b₂ * c ^ j) : b₁ = b₂ ∧ c ^ i = c ^ j := by
  have h1 : c ^ (i - j) = b₁⁻¹ * b₂ := by
    rw [zpow_sub]
    calc c ^ i * (c ^ j)⁻¹ = (b₁ * c ^ i) * (b₁⁻¹ * (c ^ j)⁻¹) := by
          rw [mul_mul_mul_comm, mul_inv_cancel, one_mul]
      _ = b₂ * c ^ j * (b₁⁻¹ * (c ^ j)⁻¹) := by rw [h]
      _ = b₁⁻¹ * b₂ := by
          rw [mul_mul_mul_comm, mul_inv_cancel, mul_one, mul_comm]
  have h2 : c ^ (i - j) ∈ invS u := by rw [h1]; exact (invS u).mul_mem ((invS u).inv_mem h₁) h₂
  have h3 := Z.zpow_eq_one_of_mem h2
  rw [h3] at h1
  have hb : b₁ = b₂ := by
    have : b₁⁻¹ * b₂ = 1 := h1.symm
    rwa [inv_mul_eq_one] at this
  refine ⟨hb, ?_⟩
  rw [hb] at h
  exact mul_left_cancel h

theorem zpow_eq_one_of_eq_neg {i : ℤ} (h : c ^ i = c ^ (-i)) : c ^ i = 1 := by
  apply Z.sq_eq_one
  have : c ^ i * c ^ i = c ^ (-i) * c ^ i := by rw [← h]
  rw [this, ← zpow_add, neg_add_cancel, zpow_zero]

theorem eq_one_of_eq_inv {x : M} (h : x = x⁻¹) : x = 1 :=
  Z.sq_eq_one (mul_eq_one_iff_eq_inv.2 h)

theorem comm_of_fixes {z g : MulAut M} (hzc : z c = c⁻¹) (hzb : ∀ b ∈ invS u, z b = b)
    (hgc : g c = c) (hgu : u * g = g * u) : z * g = g * z := by
  ext x
  obtain ⟨b, hb, i, rfl⟩ := Z.exists_mul_zpow x
  have hgb : g b ∈ invS u := apply_mem_invS_of_commute hgu hb
  have hL : z (g (b * c ^ i)) = g b * (c⁻¹) ^ i := by
    rw [apply_mul_zpow g, hgc, apply_mul_zpow z, hzb _ hgb, hzc]
  have hR : g (z (b * c ^ i)) = g b * (c⁻¹) ^ i := by
    rw [apply_mul_zpow z, hzb b hb, hzc, apply_mul_zpow g, map_inv, hgc]
  show z (g (b * c ^ i)) = g (z (b * c ^ i))
  rw [hL, hR]

end UData

abbrev vOf (u ŵ : MulAut M) : MulAut M := ŵ * u * ŵ⁻¹

abbrev yOf (u ŵ : MulAut M) : MulAut M := vOf u ŵ * u

structure ZPair (p : ℕ) (c : M) (u ŵ : MulAut M) : Prop extends UData p c u where
  comm : (ŵ * u * ŵ⁻¹) * u = u * (ŵ * u * ŵ⁻¹)
  moves : ŵ c ∉ Subgroup.zpowers c

namespace ZPair

variable [Finite M] {p : ℕ} {c : M} {u ŵ : MulAut M} (Z : ZPair p c u ŵ)

include Z

omit [Finite M] in
theorem v_sq : vOf u ŵ * vOf u ŵ = 1 := by
  calc ŵ * u * ŵ⁻¹ * (ŵ * u * ŵ⁻¹) = ŵ * (u * u) * ŵ⁻¹ := by group
    _ = 1 := by rw [Z.u_sq]; group

omit [Finite M] in
theorem v_comm : u * vOf u ŵ = vOf u ŵ * u := Z.comm.symm

omit [Finite M] in
theorem fixS_v : fixS (vOf u ŵ) = (Subgroup.zpowers c).map ŵ.toMonoidHom := by
  rw [fixS_conj, Z.fix_u]

omit [Finite M] in
theorem card_fixS_v : Nat.card (fixS (vOf u ŵ)) = p := by
  rw [Z.fixS_v, Subgroup.card_map_of_injective ŵ.injective, Nat.card_zpowers, Z.order_c]

theorem v_c : vOf u ŵ c = c⁻¹ := by
  have hfixc : c ∈ fixS u := by rw [Z.fix_u]; exact Subgroup.mem_zpowers c
  have h1 : vOf u ŵ c ∈ fixS u := apply_mem_fixS_of_commute Z.v_comm hfixc
  rw [Z.fix_u] at h1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
  have hvv := apply_apply_of_mul_self Z.v_sq c
  rw [← hk, map_zpow, ← hk, ← zpow_mul] at hvv
  have h2 : c ^ ((k - 1) * (k + 1)) = 1 := by
    have : (k - 1) * (k + 1) = k * k - 1 := by ring
    rw [this, zpow_sub_one, hvv, mul_inv_cancel]
  have h3 : (p : ℤ) ∣ (k - 1) * (k + 1) := by
    rw [← Z.order_c]
    exact orderOf_dvd_iff_zpow_eq_one.2 h2
  rcases Int.Prime.dvd_mul' Z.prime h3 with h4 | h4
  · exfalso
    have h5 : c ^ (k - 1) = 1 := by
      rw [← Z.order_c] at h4
      exact orderOf_dvd_iff_zpow_eq_one.1 h4
    have h6 : vOf u ŵ c = c := by
      rw [← hk]
      have : c ^ k = c ^ (k - 1) * c := by rw [← zpow_add_one]; congr 1; ring
      rw [this, h5, one_mul]
    have h7 : c ∈ fixS (vOf u ŵ) := h6
    rw [Z.fixS_v] at h7
    obtain ⟨x, hx, hxc⟩ := Subgroup.mem_map.1 h7
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h8 : c ∈ Subgroup.zpowers (ŵ c) := ⟨j, by
      show (ŵ c) ^ j = c
      rw [← map_zpow]
      exact hxc⟩
    have hc1 : c ≠ 1 := by
      intro h
      have := Z.order_c
      rw [h, orderOf_one] at this
      exact Z.prime.one_lt.ne this
    have hord : orderOf (ŵ c) = p := by rw [MulEquiv.orderOf_eq]; exact Z.order_c
    have h9 := zpowers_eq_of_mem_of_ne_one Z.prime hord h8 hc1
    apply Z.moves
    rw [h9]
    exact Subgroup.mem_zpowers (ŵ c)
  · have h5 : c ^ (k + 1) = 1 := by
      rw [← Z.order_c] at h4
      exact orderOf_dvd_iff_zpow_eq_one.1 h4
    rw [← hk]
    have : c ^ k = c ^ (k + 1) * c⁻¹ := by rw [zpow_add_one, mul_inv_cancel_right]
    rw [this, h5, one_mul]

omit [Finite M] in
theorem v_mem_invS {b : M} (hb : b ∈ invS u) : vOf u ŵ b ∈ invS u :=
  apply_mem_invS_of_commute Z.v_comm hb

theorem fixS_v_le : fixS (vOf u ŵ) ≤ invS u := by
  intro x hx
  obtain ⟨b, hb, i, rfl⟩ := Z.exists_mul_zpow x
  have h1 : vOf u ŵ (b * c ^ i) = b * c ^ i := hx
  rw [apply_mul_zpow, Z.v_c, inv_zpow'] at h1
  have h2 := Z.eq_of_mul_zpow_eq (Z.v_mem_invS hb) hb h1
  have h3 := Z.zpow_eq_one_of_eq_neg h2.2.symm
  rw [h3, mul_one]
  exact hb

omit [Finite M] in
theorem y_sq : yOf u ŵ * yOf u ŵ = 1 := by
  calc vOf u ŵ * u * (vOf u ŵ * u) = vOf u ŵ * (u * vOf u ŵ) * u := by group
    _ = vOf u ŵ * (vOf u ŵ * u) * u := by rw [Z.v_comm]
    _ = (vOf u ŵ * vOf u ŵ) * (u * u) := by group
    _ = 1 := by rw [Z.v_sq, Z.u_sq, one_mul]

theorem y_c : yOf u ŵ c = c⁻¹ := by
  show vOf u ŵ (u c) = c⁻¹
  rw [Z.u_c, Z.v_c]

omit [Finite M] Z in
theorem y_apply_invS {b : M} (hb : b ∈ invS u) : yOf u ŵ b = (vOf u ŵ b)⁻¹ := by
  show vOf u ŵ (u b) = _
  rw [(hb : u b = b⁻¹), map_inv]

theorem fixS_y : fixS (yOf u ŵ) = invS u ⊓ invS (vOf u ŵ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨b, hb, i, rfl⟩ := Z.exists_mul_zpow x
    have h1 : yOf u ŵ (b * c ^ i) = b * c ^ i := hx
    rw [apply_mul_zpow, Z.y_c, y_apply_invS hb, inv_zpow'] at h1
    have h2 := Z.eq_of_mul_zpow_eq ((invS u).inv_mem (Z.v_mem_invS hb)) hb h1
    have h3 := Z.zpow_eq_one_of_eq_neg h2.2.symm
    rw [h3, mul_one]
    refine ⟨hb, ?_⟩
    show vOf u ŵ b = b⁻¹
    calc vOf u ŵ b = ((vOf u ŵ b)⁻¹)⁻¹ := (inv_inv _).symm
      _ = b⁻¹ := by rw [h2.1]
  · rintro ⟨hx1, hx2⟩
    show yOf u ŵ x = x
    rw [y_apply_invS hx1, (hx2 : vOf u ŵ x = x⁻¹), inv_inv]

theorem fixS_y_le : fixS (yOf u ŵ) ≤ invS u := by
  rw [Z.fixS_y]
  exact inf_le_left

theorem invS_v_eq : invS (vOf u ŵ) = (invS u ⊓ invS (vOf u ŵ)) ⊔ Subgroup.zpowers c := by
  apply le_antisymm
  · intro x hx
    obtain ⟨b, hb, i, rfl⟩ := Z.exists_mul_zpow x
    have h1 : vOf u ŵ (b * c ^ i) = (b * c ^ i)⁻¹ := hx
    rw [apply_mul_zpow, Z.v_c, inv_zpow', mul_inv, ← zpow_neg] at h1
    have h2 := Z.eq_of_mul_zpow_eq (Z.v_mem_invS hb) ((invS u).inv_mem hb) h1
    exact Subgroup.mul_mem_sup ⟨hb, h2.1⟩ (Subgroup.zpow_mem_zpowers c i)
  · refine sup_le inf_le_right ?_
    rw [Subgroup.zpowers_le]
    show vOf u ŵ c = c⁻¹
    exact Z.v_c

theorem card_fixS_y : Nat.card (fixS (yOf u ŵ)) = p ^ 2 := by
  have hv := card_eq_mul Z.prime Z.ne_two Z.pow Z.v_sq
  rw [Z.card, Z.card_fixS_v] at hv
  have hP : 0 < p := Z.prime.pos
  have hinvv : Nat.card (invS (vOf u ŵ)) = p ^ 3 := by
    have h' : p * p ^ 3 = p * Nat.card (invS (vOf u ŵ)) := by rw [← hv]; ring
    exact (Nat.eq_of_mul_eq_mul_left hP h').symm
  have hdisj : Disjoint (invS u ⊓ invS (vOf u ŵ)) (Subgroup.zpowers c) := by
    refine Disjoint.mono_left inf_le_left ?_
    rw [disjoint_iff, inf_comm]
    exact Z.zpowers_inf_invS
  have hcard := card_sup_of_commute_disjoint (fun k _ l _ => mul_comm k l) hdisj
  rw [← Z.invS_v_eq, hinvv, Nat.card_zpowers, Z.order_c] at hcard
  rw [Z.fixS_y]
  have h' : p * p ^ 2 = p * Nat.card ↥(invS u ⊓ invS (vOf u ŵ)) := by
    rw [← pow_succ', hcard]
    ring
  exact (Nat.eq_of_mul_eq_mul_left hP h').symm

theorem conj_eq {t z : MulAut M} (ht : t * t = 1) (htc : t c = c)
    (hty : ∀ b ∈ invS u, t b = yOf u ŵ b) (hz : z = yOf u ŵ * t) :
    z c = c⁻¹ ∧ (∀ b ∈ invS u, z b = b) ∧ z * z = 1 ∧ ŵ * z * ŵ⁻¹ = t ∧
      invS z = Subgroup.zpowers c := by
  have hzapp : ∀ x, z x = yOf u ŵ (t x) := fun x => by rw [hz]; rfl
  have hzc : z c = c⁻¹ := by
    rw [hzapp, htc, Z.y_c]
  have hzb : ∀ b ∈ invS u, z b = b := by
    intro b hb
    rw [hzapp, hty b hb]
    exact apply_apply_of_mul_self Z.y_sq b
  have hzx : ∀ b ∈ invS u, ∀ i : ℤ, z (b * c ^ i) = b * c ^ (-i) := by
    intro b hb i
    rw [apply_mul_zpow, hzb b hb, hzc, inv_zpow']
  have hzsq : z * z = 1 := by
    ext x
    obtain ⟨b, hb, i, rfl⟩ := Z.exists_mul_zpow x
    show z (z (b * c ^ i)) = b * c ^ i
    rw [hzx b hb i, hzx b hb (-i), neg_neg]
  have hfixz : fixS z = invS u := by
    apply le_antisymm
    · intro x hx
      obtain ⟨b, hb, i, rfl⟩ := Z.exists_mul_zpow x
      have h1 : z (b * c ^ i) = b * c ^ i := hx
      rw [hzx b hb i] at h1
      have h2 := Z.eq_of_mul_zpow_eq hb hb h1
      have h3 := Z.zpow_eq_one_of_eq_neg h2.2.symm
      rw [h3, mul_one]
      exact hb
    · intro b hb
      exact hzb b hb
  have hinvz : invS z = Subgroup.zpowers c := by
    apply le_antisymm
    · intro x hx
      obtain ⟨b, hb, i, rfl⟩ := Z.exists_mul_zpow x
      have h1 : z (b * c ^ i) = (b * c ^ i)⁻¹ := hx
      rw [hzx b hb i, mul_inv, ← zpow_neg] at h1
      have h2 := Z.eq_of_mul_zpow_eq hb ((invS u).inv_mem hb) h1
      have h3 : b = 1 := Z.eq_one_of_eq_inv h2.1
      rw [h3, one_mul]
      exact Subgroup.zpow_mem_zpowers c i
    · rw [Subgroup.zpowers_le]
      show z c = c⁻¹
      exact hzc
  have hinvt : invS t = fixS (vOf u ŵ) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨b, hb, i, rfl⟩ := Z.exists_mul_zpow x
      have h1 : t (b * c ^ i) = (b * c ^ i)⁻¹ := hx
      rw [apply_mul_zpow, htc, hty b hb, y_apply_invS hb, mul_inv, ← zpow_neg] at h1
      have h2 := Z.eq_of_mul_zpow_eq ((invS u).inv_mem (Z.v_mem_invS hb))
        ((invS u).inv_mem hb) h1
      have h3 := Z.zpow_eq_one_of_eq_neg h2.2
      have h4 : vOf u ŵ b = b := inv_injective h2.1
      rw [h3, mul_one]
      exact h4
    · intro x hx
      have hxF : x ∈ invS u := Z.fixS_v_le hx
      show t x = x⁻¹
      rw [hty x hxF, y_apply_invS hxF, (hx : vOf u ŵ x = x)]
  have hkey : ∀ x : M, vOf u ŵ x = x⁻¹ → t x = x := by
    intro x hvx
    obtain ⟨b', hb', i, hx'⟩ := Z.exists_mul_zpow x
    have h1 : vOf u ŵ (b' * c ^ i) = (b' * c ^ i)⁻¹ := by rw [← hx']; exact hvx
    rw [apply_mul_zpow, Z.v_c, inv_zpow', mul_inv, ← zpow_neg] at h1
    have h2 := Z.eq_of_mul_zpow_eq (Z.v_mem_invS hb') ((invS u).inv_mem hb') h1
    rw [hx', apply_mul_zpow, htc, hty b' hb', y_apply_invS hb', h2.1, inv_inv]
  have hcardt : Nat.card (fixS t) = p ^ 3 := by
    have h := card_eq_mul Z.prime Z.ne_two Z.pow ht
    rw [Z.card, hinvt, Z.card_fixS_v] at h
    have hP : 0 < p := Z.prime.pos
    have h' : Nat.card (fixS t) * p = p ^ 3 * p := by rw [← h]; ring
    exact Nat.eq_of_mul_eq_mul_right hP h'
  have hfixt : fixS t = (invS u).map ŵ.toMonoidHom := by
    have hle : (invS u).map ŵ.toMonoidHom ≤ fixS t := by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hx
      have hwb : ŵ⁻¹ (ŵ b) = b := by simp
      have hvx : vOf u ŵ (ŵ b) = (ŵ b)⁻¹ := by
        show ŵ (u (ŵ⁻¹ (ŵ b))) = (ŵ b)⁻¹
        rw [hwb, (hb : u b = b⁻¹), map_inv]
      exact hkey _ hvx
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hcardt, Subgroup.card_map_of_injective ŵ.injective, Z.card_invS_u]
  refine ⟨hzc, hzb, hzsq, ?_, hinvz⟩
  apply eq_of_fixS_eq Z.prime Z.ne_two Z.pow
  · calc ŵ * z * ŵ⁻¹ * (ŵ * z * ŵ⁻¹) = ŵ * (z * z) * ŵ⁻¹ := by group
      _ = 1 := by rw [hzsq]; group
  · rw [fixS_conj, hfixz, hfixt]
  · rw [invS_conj, hinvz, hinvt, Z.fixS_v]

end ZPair

end CFSG.RankThree.PartOne.Invol
