module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.H13.L32A.T53

open scoped commutatorElement

variable {M : Type*} [Group M]

theorem inv_eq_mul_self_of_cube {a : M} (ha : a ^ 3 = 1) : a⁻¹ = a * a :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact ha)

theorem b23_inv_comm {a b : M} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab' : (a * b⁻¹) ^ 3 = 1) :
    ⁅a⁻¹, b⁻¹⁆ = ⁅a, b⁆ := by
  rw [pow_three] at ha hb hab'
  have ha' : a⁻¹ * a⁻¹ = a := by
    calc a⁻¹ * a⁻¹ = a⁻¹ * a⁻¹ * (a * (a * a)) := by rw [ha, mul_one]
      _ = a := by group
  have h1 : b⁻¹ * a * b⁻¹ = a⁻¹ * b * a⁻¹ := by
    calc b⁻¹ * a * b⁻¹ = a⁻¹ * (a * b⁻¹ * (a * b⁻¹ * (a * b⁻¹))) * b * a⁻¹ := by group
      _ = a⁻¹ * b * a⁻¹ := by rw [hab']; group
  have h2 : (b * a * b⁻¹ * a⁻¹) * (a⁻¹ * b⁻¹ * a * b) = 1 := by
    calc (b * a * b⁻¹ * a⁻¹) * (a⁻¹ * b⁻¹ * a * b)
        = b * a * b⁻¹ * (a⁻¹ * a⁻¹) * b⁻¹ * a * b := by group
      _ = b * a * (b⁻¹ * a * b⁻¹) * a * b := by rw [ha']; group
      _ = b * a * (a⁻¹ * b * a⁻¹) * a * b := by rw [h1]
      _ = b * (b * b) := by group
      _ = 1 := hb
  rw [commutatorElement_def, commutatorElement_def, inv_inv, inv_inv]
  have h3 := eq_inv_of_mul_eq_one_right h2
  rw [h3]
  group

theorem b23_comm_left {a b : M} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : (a * b) ^ 3 = 1)
    (hab' : (a * b⁻¹) ^ 3 = 1) : a * ⁅a, b⁆ = ⁅a, b⁆ * a := by
  have hinv := b23_inv_comm ha hb hab'
  have hb' := inv_eq_mul_self_of_cube hb
  have ha' := inv_eq_mul_self_of_cube ha
  rw [pow_three] at hab
  have h2 : b * a * b = a⁻¹ * b⁻¹ * a⁻¹ := by
    calc b * a * b = a⁻¹ * (a * b * (a * b * (a * b))) * b⁻¹ * a⁻¹ := by group
      _ = a⁻¹ * b⁻¹ * a⁻¹ := by rw [hab]; group
  have key : a * ⁅a, b⁆ * a⁻¹ = ⁅a⁻¹, b⁻¹⁆ := by
    calc a * ⁅a, b⁆ * a⁻¹ = (a * a) * b * a⁻¹ * b⁻¹ * a⁻¹ := by
          rw [commutatorElement_def]; group
      _ = a⁻¹ * b * (a⁻¹ * b⁻¹ * a⁻¹) := by rw [← ha']; group
      _ = a⁻¹ * b * (b * a * b) := by rw [h2]
      _ = a⁻¹ * (b * b) * a * b := by group
      _ = ⁅a⁻¹, b⁻¹⁆ := by rw [← hb', commutatorElement_def, inv_inv, inv_inv]
  rw [hinv] at key
  calc a * ⁅a, b⁆ = a * ⁅a, b⁆ * a⁻¹ * a := by group
    _ = ⁅a, b⁆ * a := by rw [key]

theorem b23_comm_right {a b : M} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : (a * b) ^ 3 = 1)
    (hab' : (a * b⁻¹) ^ 3 = 1) : b * ⁅a, b⁆ = ⁅a, b⁆ * b := by
  have hba : (b * a) ^ 3 = 1 := by
    have : (b * a) ^ 3 = b * (a * b) ^ 3 * b⁻¹ := by
      rw [pow_three, pow_three]; group
    rw [this, hab]; group
  have hba' : (b * a⁻¹) ^ 3 = 1 := by
    have : (b * a⁻¹) ^ 3 = ((a * b⁻¹) ^ 3)⁻¹ := by
      rw [pow_three, pow_three]; group
    rw [this, hab', inv_one]
  have h := b23_comm_left hb ha hba hba'
  have e : ⁅b, a⁆ = ⁅a, b⁆⁻¹ := (commutatorElement_inv a b).symm
  rw [e] at h
  calc b * ⁅a, b⁆ = ⁅a, b⁆ * (⁅a, b⁆⁻¹ * b) * ⁅a, b⁆ := by group
    _ = ⁅a, b⁆ * (b * ⁅a, b⁆⁻¹) * ⁅a, b⁆ := by rw [h]
    _ = ⁅a, b⁆ * b := by group

theorem b23_cube {a b : M} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : (a * b) ^ 3 = 1)
    (hab' : (a * b⁻¹) ^ 3 = 1) : ⁅a, b⁆ ^ 3 = 1 := by
  have hc := b23_comm_right ha hb hab hab'
  set c := ⁅a, b⁆ with hcdef
  have h1 : a * b * a⁻¹ = c * b := by rw [hcdef, commutatorElement_def]; group
  have hcomm : Commute c b := hc.symm
  have h2 : (c * b) ^ 3 = c ^ 3 * b ^ 3 := hcomm.mul_pow 3
  have h3 : (a * b * a⁻¹) ^ 3 = a * b ^ 3 * a⁻¹ := conj_pow
  rw [h1, h2, hb, mul_one] at h3
  rw [h3, mul_one, mul_inv_cancel]

theorem odd_orderOf_mul_of_involutions [Finite M] {S : Subgroup M}
    (hT : ∀ u ∈ S, ∀ w ∈ S, u ^ 2 = 1 → w ^ 2 = 1 → u ≠ 1 → w ≠ 1 → u * w = w * u → u = w)
    {d₁ d₂ : M} (hS₁ : d₁ ∈ S) (hS₂ : d₂ ∈ S) (h₁ : d₁ ^ 2 = 1) (h₂ : d₂ ^ 2 = 1)
    (h₁1 : d₁ ≠ 1) (h₂1 : d₂ ≠ 1) : Odd (orderOf (d₁ * d₂)) := by
  set g := d₁ * d₂ with hg
  have hd₁ : d₁⁻¹ = d₁ := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h₁)
  have hd₂ : d₂⁻¹ = d₂ := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h₂)
  have hinv : d₁ * g * d₁⁻¹ = g⁻¹ := by
    rw [hg, mul_inv_rev, hd₁, hd₂]
    calc d₁ * (d₁ * d₂) * d₁ = (d₁ * d₁) * d₂ * d₁ := by group
      _ = d₂ * d₁ := by rw [← sq, h₁, one_mul]
  have hinvk : ∀ k : ℕ, d₁ * g ^ k * d₁⁻¹ = (g ^ k)⁻¹ := fun k => by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hinv, inv_pow]
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨m, hm⟩ := hodd
  have hn0 : 0 < orderOf g := orderOf_pos g
  have hm0 : 0 < m := by omega
  set z := g ^ m with hz
  have hz2 : z ^ 2 = 1 := by
    rw [hz, ← pow_mul, mul_comm, show 2 * m = orderOf g by omega, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    intro h
    have := orderOf_le_of_pow_eq_one hm0 h
    omega
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hz2)
  have hdz : d₁ * z = z * d₁ := by
    have := hinvk m
    rw [← hz, hzinv] at this
    calc d₁ * z = d₁ * z * d₁⁻¹ * d₁ := by group
      _ = z * d₁ := by rw [this]
  have hd₁z := hT d₁ hS₁ z (S.pow_mem (S.mul_mem hS₁ hS₂) m) h₁ hz2 h₁1 hz1 hdz
  have hgc : d₁ * g = g * d₁ := by
    rw [hd₁z, hz]
    exact (Commute.self_pow g m).symm.eq
  have hg2 : g * g = 1 := by
    have h5 : d₁ * g * d₁⁻¹ = g := by rw [hgc]; group
    rw [h5] at hinv
    calc g * g = g * g⁻¹ := by rw [← hinv]
      _ = 1 := mul_inv_cancel g
  have hord : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hg2)
  have hm1 : m = 1 := by
    have := Nat.le_of_dvd (by norm_num) hord
    omega
  apply h₂1
  have h6 : d₁ = g := by rw [hd₁z, hz, hm1, pow_one]
  calc d₂ = d₁⁻¹ * g := by rw [hg]; group
    _ = 1 := by rw [← h6, inv_mul_cancel]

end CFSG.Quasithin.H13.L32A.T53

end
