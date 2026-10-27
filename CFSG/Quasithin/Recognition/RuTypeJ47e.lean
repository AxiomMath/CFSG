module

public import CFSG.Quasithin.Recognition.RuTypeJ47d

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin

theorem exists_pow_of_mem_zpowers {G : Type*} [Group G] [Finite G] {x y : G}
    (h : y ∈ Subgroup.zpowers x) : ∃ n : ℕ, x ^ n = y := by
  rw [← mem_powers_iff_mem_zpowers] at h
  exact h

theorem zpowers_eq_of_card_five {G : Type*} [Group G] {K : Subgroup G} (hK : Nat.card K = 5)
    {x : G} (hxK : x ∈ K) (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1) : Subgroup.zpowers x = K := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hle : Subgroup.zpowers x ≤ K := (Subgroup.zpowers_le).mpr hxK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hK, Nat.card_zpowers, orderOf_eq_prime hx5 hx1]

theorem exists_gen_of_card_five {G : Type*} [Group G] {K : Subgroup G} (hK : Nat.card K = 5) :
    ∃ x ∈ K, x ^ 5 = 1 ∧ x ≠ 1 ∧ ∀ y ∈ K, ∃ n : ℕ, x ^ n = y := by
  have hp : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hcyc : IsCyclic K := isCyclic_of_prime_card hK
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hg5 : g ^ 5 = 1 := by
    have h := pow_card_eq_one' (G := K) (x := g)
    rwa [hK] at h
  refine ⟨g, g.2, ?_, ?_, ?_⟩
  · have h := congrArg Subtype.val hg5
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
  · intro h1
    have hg1 : g = 1 := Subtype.ext (by rw [Subgroup.coe_one]; exact h1)
    have hall : ∀ y : K, y = 1 := fun y => by
      have hy := hg y
      rw [hg1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hy
      exact hy
    have hc : Nat.card K = 1 := Nat.card_eq_one_iff_unique.mpr
      ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, ⟨1⟩⟩
    rw [hK] at hc
    norm_num at hc
  · intro y hy
    obtain ⟨n, hn⟩ := exists_pow_of_mem_zpowers (hg ⟨y, hy⟩)
    refine ⟨n, ?_⟩
    have h := congrArg Subtype.val hn
    rwa [Subgroup.coe_pow] at h

namespace RuDataM

variable {G : Type} [Group G]

theorem z_inv47 (M : RuDataM G) : M.z⁻¹ = M.z := inv_eq_of_mul_eq_one_right M.z_mul_self

structure Conf47 (M : RuDataM G) where
  F1 : Subgroup G
  b : G
  u : G
  j : G
  y : G
  iEl : ℕ → G
  F1_le_H : F1 ≤ ruH M.T
  card_F1 : Nat.card F1 = 2 ^ 12 * 5
  card_F1_inf_Q : Nat.card (F1 ⊓ ruQ M.T : Subgroup G) = 2 ^ 10
  b_mem : b ∈ F1
  orderOf_b : orderOf b = 5
  u_mem : u ∈ F1
  u_mul_self : u * u = 1
  u_inv_b : u * b * u⁻¹ = b⁻¹
  j_mul_self : j * j = 1
  j_conj_z : j * M.z * j⁻¹ = u
  conj_mem_F1 : ∀ c ∈ F1, c * u = u * c → j * c * j⁻¹ ∈ F1
  iEl_inj : ∀ p < 16, ∀ q < 16, iEl p = iEl q → p = q
  iEl_mem : ∀ p, iEl p ∈ F1
  iEl_comm : ∀ p, iEl p * u = u * iEl p
  iEl_norm : ∀ p, ∃ k : ℕ, iEl p * b * (iEl p)⁻¹ = b ^ k
  iEl_inv : ∀ p < 16, iEl p * iEl p = 1 →
    iEl p = 1 ∨ iEl p = M.z ∨ iEl p = u ∨ iEl p = u * M.z
  conj_u_ne : ∀ g ∈ F1, g * u * g⁻¹ ≠ u * M.z
  y_pow_three : y ^ 3 = 1
  y_ne_one : y ≠ 1
  y_comm_t : y * (u * M.z) = (u * M.z) * y
  y_conj_z : y * M.z * y⁻¹ = j
  F1_norm : ∀ f ∈ F1, ∃ k : ℕ, M.phiG (f * b * f⁻¹) = M.phiG b ^ k

namespace Conf47

variable {M : RuDataM G} (C : Conf47 M) [Finite G]

omit [Finite G] in
theorem b_mem_H : C.b ∈ ruH M.T := C.F1_le_H C.b_mem

omit [Finite G] in
theorem u_mem_H : C.u ∈ ruH M.T := C.F1_le_H C.u_mem

theorem u_comm_z : C.u * M.z = M.z * C.u := (M.Z_comm_H M.z_mem_Z C.u_mem_H).symm

theorem b_comm_z : C.b * M.z = M.z * C.b := (M.Z_comm_H M.z_mem_Z C.b_mem_H).symm

omit [Finite G] in
theorem u_inv : C.u⁻¹ = C.u := inv_eq_of_mul_eq_one_right C.u_mul_self

omit [Finite G] in
theorem j_inv : C.j⁻¹ = C.j := inv_eq_of_mul_eq_one_right C.j_mul_self

omit [Finite G] in
theorem isConj_u : IsConj M.z C.u := isConj_iff.mpr ⟨C.j, C.j_conj_z⟩

omit [Finite G] in
theorem j_conj_u : C.j * C.u * C.j⁻¹ = M.z := by
  rw [← C.j_conj_z]
  calc C.j * (C.j * M.z * C.j⁻¹) * C.j⁻¹ = (C.j * C.j) * M.z * (C.j⁻¹ * C.j⁻¹) := by group
    _ = M.z := by rw [C.j_inv, C.j_mul_self]; group

omit [Finite G] in
theorem b_pow_five : C.b ^ 5 = 1 := by rw [← C.orderOf_b]; exact pow_orderOf_eq_one _

omit [Finite G] in
theorem b_ne_inv : C.b ≠ C.b⁻¹ := by
  intro h
  have h2 : C.b ^ 2 = 1 := by
    rw [pow_two]
    calc C.b * C.b = C.b * C.b⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel _
  have := orderOf_dvd_of_pow_eq_one h2
  rw [C.orderOf_b] at this
  norm_num at this

theorem u_ne_z : C.u ≠ M.z := by
  intro h
  apply C.b_ne_inv
  rw [← C.u_inv_b, h, ← C.b_comm_z]
  group

omit [Finite G] in
noncomputable abbrev t : G := C.u * M.z

theorem t_mul_self : C.t * C.t = 1 := by
  calc C.t * C.t = C.u * (M.z * C.u) * M.z := by group
    _ = C.u * (C.u * M.z) * M.z := by rw [C.u_comm_z]
    _ = (C.u * C.u) * (M.z * M.z) := by group
    _ = 1 := by rw [C.u_mul_self, M.z_mul_self, one_mul]

theorem t_inv_b : C.t * C.b * C.t⁻¹ = C.b⁻¹ := by
  calc C.t * C.b * C.t⁻¹ = C.u * (M.z * C.b) * M.z⁻¹ * C.u⁻¹ := by group
    _ = C.u * (C.b * M.z) * M.z⁻¹ * C.u⁻¹ := by rw [C.b_comm_z]
    _ = C.u * C.b * C.u⁻¹ := by group
    _ = C.b⁻¹ := C.u_inv_b

theorem phiG_u_ne_one : M.phiG C.u ≠ 1 := by
  intro h
  have h1 := M.phiG_conj C.u_mem_H C.b_mem_H
  rw [C.u_inv_b, M.phiG_inv C.b_mem_H, h, one_mul, inv_one, mul_one] at h1
  have hsq : (M.phiG C.b) ^ 2 = 1 := by
    rw [pow_two]
    calc M.phiG C.b * M.phiG C.b = (M.phiG C.b)⁻¹ * M.phiG C.b := by rw [h1]
      _ = 1 := inv_mul_cancel _
  have h5 : (M.phiG C.b) ^ 5 = 1 := by
    rw [← M.phiG_pow C.b_mem_H, C.b_pow_five, M.phiG_of_mem (one_mem _)]
    exact map_one _
  have hb1 : M.phiG C.b = 1 := by
    have := (pow_gcd_eq_one (a := M.phiG C.b)).mpr ⟨hsq, h5⟩
    rwa [show Nat.gcd 2 5 = 1 by norm_num, pow_one] at this
  have hbQ := (M.phiG_eq_one_iff C.b_mem_H).mp hb1
  have h2 := M.pow_eq_one_of_mem_Q hbQ
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [C.orderOf_b] at h3
  norm_num at h3

end Conf47

end RuDataM

end CFSG.Quasithin.RuType
