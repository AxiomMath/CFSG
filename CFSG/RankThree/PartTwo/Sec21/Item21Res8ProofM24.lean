module

public import CFSG.RankThree.Native.MathieuRealThree
import CFSG.Sporadic.Mathieu.M24
import CFSG.RankThree.Asc83Table.Reduction
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Res8Proof

open CFSG.Blueprint CFSG.RankThree.Native Subgroup
open scoped commutatorElement

theorem mem_zpowers_commutator_of_commute {P : Type*} [Group P] {x y g : P} (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) (hz1 : ⁅x, y⁆ ≠ 1)
    (hg : g ∈ closure ({x, y} : Set P)) (hgx : g * x = x * g) (hgy : g * y = y * g) :
    g ∈ zpowers ⁅x, y⁆ := by
  obtain ⟨i, j, k, hi, hj, -, rfl⟩ :=
    CFSG.SectionRank.LocalWitness.mem_closure_normalForm (by norm_num) hx hy hzx hzy hg
  have hz3 : ⁅x, y⁆ ^ 3 = 1 := Asc83Table.commutator_pow_three hx hzx
  have hord : orderOf ⁅x, y⁆ = 3 := orderOf_eq_prime hz3 hz1
  have h3 : ∀ m : ℕ, m < 3 → ⁅x, y⁆ ^ (2 * m) = 1 → m = 0 := by
    intro m hm h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hord] at this
    omega
  have hzkx : ⁅x, y⁆ ^ k * x = x * ⁅x, y⁆ ^ k := (hzx.pow_left k).eq
  have hzky : ⁅x, y⁆ ^ k * y = y * ⁅x, y⁆ ^ k := (hzy.pow_left k).eq
  have hj0 : j = 0 := by
    apply h3 j hj
    have h1 : y ^ j * x = x * y ^ j * ⁅x, y⁆ ^ (2 * j) := by
      have := Asc83Table.y_pow_mul_x_pow hx hzx hzy 1 j
      rwa [pow_one, mul_one] at this
    have hxx : x * x ^ i = x ^ i * x := (Commute.self_pow x i).eq
    have key : x ^ i * x * y ^ j * ⁅x, y⁆ ^ (2 * j) * ⁅x, y⁆ ^ k =
        x ^ i * x * y ^ j * 1 * ⁅x, y⁆ ^ k := by
      calc x ^ i * x * y ^ j * ⁅x, y⁆ ^ (2 * j) * ⁅x, y⁆ ^ k
          = x ^ i * (x * y ^ j * ⁅x, y⁆ ^ (2 * j)) * ⁅x, y⁆ ^ k := by simp only [mul_assoc]
        _ = x ^ i * (y ^ j * x) * ⁅x, y⁆ ^ k := by rw [h1]
        _ = x ^ i * y ^ j * (x * ⁅x, y⁆ ^ k) := by simp only [mul_assoc]
        _ = x ^ i * y ^ j * ⁅x, y⁆ ^ k * x := by rw [← hzkx]; simp only [mul_assoc]
        _ = x * (x ^ i * y ^ j * ⁅x, y⁆ ^ k) := hgx
        _ = x * x ^ i * y ^ j * ⁅x, y⁆ ^ k := by simp only [mul_assoc]
        _ = x ^ i * x * y ^ j * 1 * ⁅x, y⁆ ^ k := by rw [hxx, mul_one]
    exact mul_left_cancel (mul_right_cancel key)
  subst hj0
  have hi0 : i = 0 := by
    apply h3 i hi
    have h1 : y * x ^ i = x ^ i * y * ⁅x, y⁆ ^ (2 * i) := by
      have := Asc83Table.y_pow_mul_x_pow hx hzx hzy i 1
      rwa [pow_one, mul_one] at this
    have key : x ^ i * y * ⁅x, y⁆ ^ (2 * i) * ⁅x, y⁆ ^ k = x ^ i * y * 1 * ⁅x, y⁆ ^ k := by
      calc x ^ i * y * ⁅x, y⁆ ^ (2 * i) * ⁅x, y⁆ ^ k
          = y * x ^ i * ⁅x, y⁆ ^ k := by rw [h1]
        _ = y * (x ^ i * y ^ 0 * ⁅x, y⁆ ^ k) := by rw [pow_zero, mul_one, mul_assoc]
        _ = x ^ i * y ^ 0 * ⁅x, y⁆ ^ k * y := hgy.symm
        _ = x ^ i * (⁅x, y⁆ ^ k * y) := by rw [pow_zero, mul_one, mul_assoc]
        _ = x ^ i * y * 1 * ⁅x, y⁆ ^ k := by rw [hzky, mul_one, mul_assoc]
    exact mul_left_cancel (mul_right_cancel key)
  subst hi0
  rw [pow_zero, pow_zero, one_mul, one_mul]
  exact pow_mem (mem_zpowers _) k

def m24K₁ : NativeSporadic.M24 :=
  m24T * m24B * m24T * m24B⁻¹ * m24T * m24B * m24T * m24B⁻¹ * m24T * m24B⁻¹ * m24T * m24B⁻¹ *
    m24T * m24B * m24T * m24B * m24T * m24B * m24T * m24B⁻¹ * m24T

def m24K₂ : NativeSporadic.M24 :=
  m24T * m24B * m24T * m24B * m24T * m24B * m24T * m24B⁻¹ * m24T * m24B * m24T * m24B⁻¹ *
    m24T * m24B⁻¹ * m24T * m24B * m24T * m24B⁻¹ * m24T * m24B * m24T * m24B * m24T

def m24X : NativeSporadic.M24 := m24K₁ * m24B * m24K₁⁻¹

def m24Y : NativeSporadic.M24 := m24K₂ * m24B * m24K₂⁻¹

theorem m24B_pow_three : m24B ^ 3 = 1 := by decide +kernel

theorem m24B_ne_one : m24B ≠ 1 := by decide +kernel

theorem m24X_mul_B : m24X * m24B = m24B * m24X := by decide +kernel

theorem m24Y_mul_B : m24Y * m24B = m24B * m24Y := by decide +kernel

def m24XPerm : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 12, 18] * List.formPerm [2, 14, 8] * List.formPerm [3, 16, 23] *
    List.formPerm [4, 17, 9] * List.formPerm [5, 15, 22] * List.formPerm [10, 11, 21]

def m24YPerm : Equiv.Perm (Fin 24) :=
  List.formPerm [1, 9, 14] * List.formPerm [2, 20, 4] * List.formPerm [6, 19, 7] *
    List.formPerm [8, 13, 17] * List.formPerm [12, 15, 16] * List.formPerm [18, 23, 22]

theorem coe_m24X : (m24X : Equiv.Perm (Fin 24)) = m24XPerm := by decide +kernel

theorem coe_m24Y : (m24Y : Equiv.Perm (Fin 24)) = m24YPerm := by decide +kernel

theorem m24_commutator : ⁅m24X, m24Y⁆ = m24B := by
  apply Subtype.ext
  show (m24X : Equiv.Perm (Fin 24)) * m24Y * (m24X : Equiv.Perm (Fin 24))⁻¹ *
    (m24Y : Equiv.Perm (Fin 24))⁻¹ = m24B
  rw [coe_m24X, coe_m24Y]
  decide +kernel

theorem m24X_pow_three : m24X ^ 3 = 1 := by
  rw [m24X, conj_pow, m24B_pow_three, mul_one, mul_inv_cancel]

theorem m24Y_pow_three : m24Y ^ 3 = 1 := by
  rw [m24Y, conj_pow, m24B_pow_three, mul_one, mul_inv_cancel]

theorem conj_inv_conj_conj {G : Type*} [Group G] (h k b : G) :
    h * k⁻¹ * h⁻¹ * (h * (k * b * k⁻¹) * h⁻¹) * (h * k⁻¹ * h⁻¹)⁻¹ = h * b * h⁻¹ := by
  group

theorem m24_exists_fusion {Q : Subgroup NativeSporadic.M24}
    (hQ : Nat.card Q = 27) {x : NativeSporadic.M24} (hxQ : x ∈ Q) (hx1 : x ≠ 1)
    (hxc : ∀ q ∈ Q, q * x = x * q) :
    ∃ w ∈ Q, w ^ 3 = 1 ∧ w ∉ zpowers x ∧ ∃ k : NativeSporadic.M24,
      (zpowers w).map (MulAut.conj k).toMonoidHom = zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX3 := m24X_pow_three
  have hY3 := m24Y_pow_three
  have hzx : Commute ⁅m24X, m24Y⁆ m24X := by
    rw [m24_commutator]
    exact m24X_mul_B.symm
  have hzy : Commute ⁅m24X, m24Y⁆ m24Y := by
    rw [m24_commutator]
    exact m24Y_mul_B.symm
  have hz1 : ⁅m24X, m24Y⁆ ≠ 1 := by
    rw [m24_commutator]
    exact m24B_ne_one
  have hL : (Nat.card NativeSporadic.M24).factorization 3 = 3 := by
    rw [CFSG.Sporadic.Mathieu.card_M24, show (244823040 : ℕ) = 3 ^ 3 * 9067520 by norm_num,
      Sec4.Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
  set P₀ := closure ({m24X, m24Y} : Set NativeSporadic.M24) with hP₀
  have hP₀card : Nat.card P₀ = 27 := Asc83Table.ex27_card hX3 hY3 hzx hzy hz1
  have hP₀syl : Nat.card P₀ = 3 ^ (Nat.card NativeSporadic.M24).factorization 3 :=
    Asc83Table.ex27_card_sylow hX3 hY3 hzx hzy hz1 hL
  have hQp : IsPGroup 3 Q := IsPGroup.of_card (n := 3) (by rw [hQ]; norm_num)
  obtain ⟨h, hle⟩ := Sec4.Item434AltPerm.exists_le_map_conj_of_card hP₀syl hQp
  have hQeq : Q = P₀.map (MulAut.conj h).toMonoidHom :=
    eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective (MulAut.conj h).injective, hP₀card, hQ])
  have hxP : x ∈ P₀.map (MulAut.conj h).toMonoidHom := hQeq ▸ hxQ
  obtain ⟨p, hpP, hpx⟩ := mem_map.mp hxP
  have hpx' : h * p * h⁻¹ = x := hpx
  have hcomm : ∀ q ∈ P₀, p * q = q * p := by
    intro q hq
    have hqQ : h * q * h⁻¹ ∈ Q := by
      rw [hQeq]
      exact ⟨q, hq, rfl⟩
    have e1 := hxc _ hqQ
    rw [← hpx'] at e1
    have e2 : h * (q * p) * h⁻¹ = h * (p * q) * h⁻¹ := by
      calc h * (q * p) * h⁻¹ = h * q * h⁻¹ * (h * p * h⁻¹) := by group
        _ = h * p * h⁻¹ * (h * q * h⁻¹) := e1
        _ = h * (p * q) * h⁻¹ := by group
    exact (mul_left_cancel (mul_right_cancel e2)).symm
  have hpZ : p ∈ zpowers m24B := by
    have := mem_zpowers_commutator_of_commute hX3 hY3 hzx hzy hz1 hpP
      (hcomm _ (subset_closure (by simp))) (hcomm _ (subset_closure (by simp)))
    rwa [m24_commutator] at this
  have hp1 : p ≠ 1 := by
    rintro rfl
    apply hx1
    rw [← hpx']
    group
  have hp3 : p ^ 3 = 1 := by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hpZ
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, m24B_pow_three, one_zpow]
  have hzp : zpowers p = zpowers m24B := by
    refine eq_of_le_of_card_ge (zpowers_le.mpr hpZ) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime m24B_pow_three m24B_ne_one,
      orderOf_eq_prime hp3 hp1]
  have hzx' : zpowers x = (zpowers m24B).map (MulAut.conj h).toMonoidHom := by
    rw [← hzp, MonoidHom.map_zpowers]
    exact congrArg zpowers hpx'.symm
  refine ⟨h * m24X * h⁻¹, ?_, ?_, ?_, h * m24K₁⁻¹ * h⁻¹, ?_⟩
  · rw [hQeq]
    exact ⟨m24X, subset_closure (by simp), rfl⟩
  · rw [conj_pow, hX3, mul_one, mul_inv_cancel]
  · intro hw
    rw [hzx'] at hw
    obtain ⟨b', hb', hb'e⟩ := mem_map.mp hw
    have hb'e' : h * b' * h⁻¹ = h * m24X * h⁻¹ := hb'e
    have hb'X : b' = m24X := mul_left_cancel (mul_right_cancel hb'e')
    rw [hb'X, ← m24_commutator] at hb'
    have hmem : m24X ^ 1 * m24Y ^ 0 ∈ zpowers ⁅m24X, m24Y⁆ := by
      rw [pow_one, pow_zero, mul_one]
      exact hb'
    have := Asc83Table.eq_zero_of_mem_zpowers hX3 hY3 hzx hzy hP₀card (by norm_num)
      (by norm_num) hmem
    exact absurd this.1 one_ne_zero
  · rw [MonoidHom.map_zpowers, hzx', MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [m24X, conj_inv_conj_conj]

end CFSG.RankThree.PartTwo.Sec21.Item21Res8Proof
