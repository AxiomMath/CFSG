module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Subgroup.Ker

public section

namespace CFSG.RankThree.PartOne.KFU

variable {G H : Type*} [Group G] [Group H]

structure CentralThree (π : G →* H) : Prop where
  central : ∀ z, π z = 1 → ∀ g, g * z = z * g
  exp_three : ∀ z, π z = 1 → z ^ 3 = 1

theorem comm_mem_ker {π : G →* H} {x y : G} (hxy : π x * π y = π y * π x) :
    π (x * y * x⁻¹ * y⁻¹) = 1 := by
  simp only [map_mul, map_inv]
  rw [hxy]
  group

theorem eq_one_of_pow_two_three {c : G} (h2 : c ^ 2 = 1) (h3 : c ^ 3 = 1) : c = 1 := by
  have h : c * c ^ 2 = c ^ 3 := (pow_succ' c 2).symm
  rwa [h2, h3, mul_one] at h

theorem sq_eq_one_of_eq_inv {c : G} (h : c = c⁻¹) : c ^ 2 = 1 := by
  rw [pow_two]
  nth_rewrite 2 [h]
  exact mul_inv_cancel c

variable {π : G →* H}

theorem CentralThree.exists_involution_lift_of_mem_range (hC : CentralThree π)
    {t : H} (htπ : t ∈ π.range) (ht : t ^ 2 = 1) :
    ∃ g : G, π g = t ∧ g ^ 2 = 1 := by
  obtain ⟨g₀, hg₀⟩ := htπ
  refine ⟨g₀ ^ 3, ?_, ?_⟩
  · rw [map_pow, hg₀, pow_succ, ht, one_mul]
  · have h1 : π (g₀ ^ 2) = 1 := by rw [map_pow, hg₀, ht]
    calc (g₀ ^ 3) ^ 2 = (g₀ ^ 2) ^ 3 := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = 1 := hC.exp_three _ h1

theorem CentralThree.commute_of_sq (h : CentralThree π) {x y : G}
    (hxy : π x * π y = π y * π x) (hy : y ^ 2 = 1) : x * y = y * x := by
  obtain ⟨c, hc⟩ : ∃ c, c = x * y * x⁻¹ * y⁻¹ := ⟨_, rfl⟩
  have hcz : π c = 1 := by rw [hc]; exact comm_mem_ker hxy
  have hcc : ∀ g, g * c = c * g := h.central c hcz
  have hc3 : c ^ 3 = 1 := h.exp_three c hcz
  have hxy' : x * y = c * (y * x) := by rw [hc]; group
  have e1 : y * x = c⁻¹ * (x * y) := by rw [hc]; group
  have e2 : y * x * y = c * x := by
    calc y * x * y = y * (x * y) := by rw [mul_assoc]
      _ = y * (c * (y * x)) := by rw [hxy']
      _ = (y * c) * (y * x) := by rw [mul_assoc]
      _ = (c * y) * (y * x) := by rw [hcc y]
      _ = c * (y * y * x) := by simp only [mul_assoc]
      _ = c * x := by rw [← pow_two, hy, one_mul]
  have e3 : y * x * y = c⁻¹ * x := by
    calc y * x * y = (c⁻¹ * (x * y)) * y := by rw [e1]
      _ = c⁻¹ * x * (y * y) := by simp only [mul_assoc]
      _ = c⁻¹ * x := by rw [← pow_two, hy, mul_one]
  have e4 : c = c⁻¹ := mul_right_cancel (e2.symm.trans e3)
  have hc1 : c = 1 := eq_one_of_pow_two_three (sq_eq_one_of_eq_inv e4) hc3
  rw [hxy', hc1, one_mul]

theorem CentralThree.pow_three_eq_one (h : CentralThree π) {x s : G} (hx : π x ^ 3 = 1)
    (hs : π s * π x * (π s)⁻¹ = (π x)⁻¹) : x ^ 3 = 1 := by
  obtain ⟨c, hc⟩ : ∃ c, c = x ^ 3 := ⟨_, rfl⟩
  have hcz : π c = 1 := by rw [hc, map_pow, hx]
  have hcc : ∀ g, g * c = c * g := h.central c hcz
  have hc3 : c ^ 3 = 1 := h.exp_three c hcz
  obtain ⟨z, hz⟩ : ∃ z, z = s * x * s⁻¹ * x := ⟨_, rfl⟩
  have hzz : π z = 1 := by
    rw [hz]
    simp only [map_mul, map_inv]
    rw [hs]
    group
  have hzc : ∀ g, g * z = z * g := h.central z hzz
  have hz3 : z ^ 3 = 1 := h.exp_three z hzz
  have e1 : s * x * s⁻¹ = z * x⁻¹ := by rw [hz]; group
  have e2 : (s * x * s⁻¹) ^ 3 = c := by
    rw [conj_pow, ← hc, hcc s, mul_inv_cancel_right]
  have e3 : (s * x * s⁻¹) ^ 3 = c⁻¹ := by
    have hcomm : Commute z x⁻¹ := (hzc x⁻¹).symm
    rw [e1, hcomm.mul_pow, hz3, one_mul, inv_pow, ← hc]
  have hc1 : c = 1 := eq_one_of_pow_two_three (sq_eq_one_of_eq_inv (e2.symm.trans e3)) hc3
  rw [← hc]
  exact hc1

theorem CentralThree.commute_of_inv (h : CentralThree π) {x y s : G}
    (hxy : π x * π y = π y * π x) (hs1 : π s * π x * (π s)⁻¹ = (π x)⁻¹)
    (hs2 : s * y = y * s) : x * y = y * x := by
  obtain ⟨c, hc⟩ : ∃ c, c = x * y * x⁻¹ * y⁻¹ := ⟨_, rfl⟩
  have hcz : π c = 1 := by rw [hc]; exact comm_mem_ker hxy
  have hcc : ∀ g, g * c = c * g := h.central c hcz
  have hc3 : c ^ 3 = 1 := h.exp_three c hcz
  obtain ⟨z, hz⟩ : ∃ z, z = s * x * s⁻¹ * x := ⟨_, rfl⟩
  have hzz : π z = 1 := by
    rw [hz]
    simp only [map_mul, map_inv]
    rw [hs1]
    group
  have hzc : ∀ g, g * z = z * g := h.central z hzz
  have e1 : s * x * s⁻¹ = z * x⁻¹ := by rw [hz]; group
  have e2 : s * y * s⁻¹ = y := by rw [hs2, mul_inv_cancel_right]
  have hxy' : x * y = c * (y * x) := by rw [hc]; group
  have e3 : x⁻¹ * y = c⁻¹ * (y * x⁻¹) := by
    have h1 : y * x⁻¹ = c * (x⁻¹ * y) := by
      calc y * x⁻¹ = x⁻¹ * (x * y) * x⁻¹ := by group
        _ = x⁻¹ * (c * (y * x)) * x⁻¹ := by rw [hxy']
        _ = (x⁻¹ * c) * (y * x * x⁻¹) := by group
        _ = c * (x⁻¹ * y) := by rw [hcc x⁻¹]; group
    rw [h1]
    group
  have e4 : (s * x * s⁻¹) * (s * y * s⁻¹) = (s * c * s⁻¹) * ((s * y * s⁻¹) * (s * x * s⁻¹)) := by
    calc (s * x * s⁻¹) * (s * y * s⁻¹) = s * (x * y) * s⁻¹ := by group
      _ = s * (c * (y * x)) * s⁻¹ := by rw [hxy']
      _ = (s * c * s⁻¹) * ((s * y * s⁻¹) * (s * x * s⁻¹)) := by group
  have e5 : s * c * s⁻¹ = c := by rw [hcc s, mul_inv_cancel_right]
  rw [e1, e2, e5] at e4
  have e6 : x⁻¹ * y = c * (y * x⁻¹) := by
    have e7 : z * (x⁻¹ * y) = z * (c * (y * x⁻¹)) := by
      calc z * (x⁻¹ * y) = (z * x⁻¹) * y := by rw [mul_assoc]
        _ = c * (y * (z * x⁻¹)) := e4
        _ = c * ((y * z) * x⁻¹) := by rw [mul_assoc]
        _ = c * ((z * y) * x⁻¹) := by rw [hzc y]
        _ = (c * z) * (y * x⁻¹) := by simp only [mul_assoc]
        _ = (z * c) * (y * x⁻¹) := by rw [hcc z]
        _ = z * (c * (y * x⁻¹)) := by rw [mul_assoc]
    exact mul_left_cancel e7
  have e8 : c = c⁻¹ := (mul_right_cancel (e3.symm.trans e6)).symm
  have hc1 : c = 1 := eq_one_of_pow_two_three (sq_eq_one_of_eq_inv e8) hc3
  rw [hxy', hc1, one_mul]

end CFSG.RankThree.PartOne.KFU
