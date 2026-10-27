module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.GF2n.Tim79a

open scoped commutatorElement

theorem c8_comm_cent {K : Type*} [Group K] {r : K}
    (h : ∀ x : K, x * r * x⁻¹ = r ∨ x * r * x⁻¹ = r⁻¹) (x y : K) :
    ⁅x, y⁆ * r * ⁅x, y⁆⁻¹ = r := by
  have hA : ∀ g : K, g⁻¹ * r * g = g * r * g⁻¹ := by
    intro g
    have h1 : g⁻¹ * (g * r * g⁻¹) * g = r := by group
    rcases h g with hg | hg
    · rw [hg] at h1 ⊢
      exact h1
    · rw [hg] at h1 ⊢
      calc g⁻¹ * r * g = (g⁻¹ * r⁻¹ * g)⁻¹ := by group
        _ = r⁻¹ := by rw [h1]
  have H2 : ∀ g : K, g * r⁻¹ * g⁻¹ = (g * r * g⁻¹)⁻¹ := fun g => by group
  have hB : ∀ a b : K, a * b * r * (a * b)⁻¹ = b * a * r * (b * a)⁻¹ := by
    intro a b
    have e1 : a * b * r * (a * b)⁻¹ = a * (b * r * b⁻¹) * a⁻¹ := by group
    have e2 : b * a * r * (b * a)⁻¹ = b * (a * r * a⁻¹) * b⁻¹ := by group
    rw [e1, e2]
    rcases h b with hb | hb <;> rcases h a with ha | ha <;>
      simp only [ha, hb, H2, inv_inv]
  have hC : ∀ g : K, g * (g * r * g⁻¹) * g⁻¹ = r := by
    intro g
    rcases h g with hg | hg
    · rw [hg]
      exact hg
    · rw [hg]
      calc g * r⁻¹ * g⁻¹ = (g * r * g⁻¹)⁻¹ := by group
        _ = r := by rw [hg, inv_inv]
  have hk : ∀ g k : K, g * k * r * (g * k)⁻¹ = g * (k * r * k⁻¹) * g⁻¹ :=
    fun g k => by group
  have hk2 : (y * x)⁻¹ * r * (y * x)⁻¹⁻¹ = x * y * r * (x * y)⁻¹ := by
    rw [inv_inv, hA (y * x), hB x y]
  have hc : ⁅x, y⁆ = x * y * (y * x)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [hc, hk (x * y) (y * x)⁻¹, hk2]
  exact hC (x * y)

theorem c8_dual {G : Type*} [Group G] {P Z N : Subgroup G} {ρ : G}
    (hZP : ∀ z ∈ Z, ∀ p ∈ P, z * p = p * z)
    (hPP : ∀ p ∈ P, ∀ q ∈ P, ⁅p, q⁆ ∈ Z)
    (hNP : N ≤ P) (hZN : Z ≤ N)
    (hNab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hNsq : ∀ x ∈ N, x * x = 1)
    (hρP : ∀ p ∈ P, ρ * p * ρ⁻¹ ∈ P) (hρN : ∀ x ∈ N, ρ * x * ρ⁻¹ ∈ N)
    (hρZ : ∀ z ∈ Z, ρ * z * ρ⁻¹ = z) (hρ3 : ρ ^ 3 = 1)
    (hδP : ∀ p ∈ P, ρ * p * ρ⁻¹ * p⁻¹ ∈ N) :
    ∀ f ∈ N, ∀ p ∈ P, ⁅ρ * f * ρ⁻¹ * f⁻¹, p⁆ = 1 := by
  have hρ3' : ρ * ρ * ρ = 1 := by
    rw [← pow_three']
    exact hρ3
  have hI1 : ∀ x : G, ρ * (ρ * x * ρ⁻¹) * ρ⁻¹ = ρ⁻¹ * x * ρ := by
    intro x
    have e : ρ * (ρ * x * ρ⁻¹) * ρ⁻¹ = (ρ * ρ * ρ) * (ρ⁻¹ * x * ρ) * (ρ * ρ * ρ)⁻¹ := by
      group
    rw [e, hρ3', one_mul, inv_one, mul_one]
  have hid : ∀ a b d : G, ⁅a * b, d⁆ = a * ⁅b, d⁆ * a⁻¹ * ⁅a, d⁆ := by
    intro a b d
    simp only [commutatorElement_def]
    group
  have hid2 : ∀ a b d : G, ⁅a, b * d⁆ = ⁅a, b⁆ * (b * ⁅a, d⁆ * b⁻¹) := by
    intro a b d
    simp only [commutatorElement_def]
    group
  intro f hf p hp
  have hfP : f ∈ P := hNP hf
  obtain ⟨c, hc⟩ : ∃ c : G, c = ⁅f, p⁆ := ⟨_, rfl⟩
  have hcZ : c ∈ Z := by
    rw [hc]
    exact hPP f hfP p hp
  have hcN : c ∈ N := hZN hcZ
  obtain ⟨z, hz_def⟩ : ∃ z : G, z = ρ⁻¹ * p * ρ * p⁻¹ := ⟨_, rfl⟩
  have hzN : z ∈ N := by
    have e : z = ρ * (ρ * p * ρ⁻¹ * p⁻¹) * ρ⁻¹ * (ρ * p * ρ⁻¹ * p⁻¹) := by
      rw [hz_def, ← hI1 p]
      group
    rw [e]
    exact N.mul_mem (hρN _ (hδP p hp)) (hδP p hp)
  have hzP : z ∈ P := hNP hzN
  have hzp : ρ⁻¹ * p * ρ = z * p := by
    rw [hz_def]
    group
  have hfz : ⁅f, z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hNab f hf z hzN)
  have hcz : c * z = z * c := hZP c hcZ z hzP
  have hzc : z * c * z⁻¹ = c := by
    rw [← hcz]
    group
  have hA : ⁅ρ * f * ρ⁻¹, p⁆ = c := by
    have e1 : ⁅ρ * f * ρ⁻¹, p⁆ = ρ * ⁅f, ρ⁻¹ * p * ρ⁆ * ρ⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e1, hzp, hid2, hfz, one_mul, ← hc, hzc, hρZ c hcZ]
  have haN : ρ * f * ρ⁻¹ ∈ N := hρN f hf
  have haP : ρ * f * ρ⁻¹ ∈ P := hNP haN
  have hf_inv : f⁻¹ = f := inv_eq_of_mul_eq_one_right (hNsq f hf)
  have hfin : ⁅f⁻¹, p⁆ = c := by
    rw [hf_inv, hc]
  have hcomm : c * (ρ * f * ρ⁻¹) = ρ * f * ρ⁻¹ * c := hZP c hcZ _ haP
  have hcc : ρ * f * ρ⁻¹ * c * (ρ * f * ρ⁻¹)⁻¹ = c := by
    rw [← hcomm]
    group
  rw [hid (ρ * f * ρ⁻¹) f⁻¹ p, hfin, hA, hcc]
  exact hNsq c hcN

theorem c8_unipotent {G : Type*} [Group G] {P Z N : Subgroup G} {ρ : G}
    (hZP : ∀ z ∈ Z, ∀ p ∈ P, z * p = p * z)
    (hPP : ∀ p ∈ P, ∀ q ∈ P, ⁅p, q⁆ ∈ Z)
    (hNP : N ≤ P) (hZN : Z ≤ N)
    (hNab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hNsq : ∀ x ∈ N, x * x = 1)
    (hρP : ∀ p ∈ P, ρ * p * ρ⁻¹ ∈ P) (hρN : ∀ x ∈ N, ρ * x * ρ⁻¹ ∈ N)
    (hρZ : ∀ z ∈ Z, ρ * z * ρ⁻¹ = z) (hρ3 : ρ ^ 3 = 1)
    (hδP : ∀ p ∈ P, ρ * p * ρ⁻¹ * p⁻¹ ∈ N)
    (hδN : ∀ f ∈ N, ρ * f * ρ⁻¹ * f⁻¹ ∈ Z) :
    ∀ p ∈ P, ρ * p * ρ⁻¹ * p⁻¹ ∈ Z := by
  have hρ3' : ρ * ρ * ρ = 1 := by
    rw [← pow_three']
    exact hρ3
  have hI2 : ∀ x : G, ρ * (ρ * (ρ * x * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ = x := by
    intro x
    have e : ρ * (ρ * (ρ * x * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ = (ρ * ρ * ρ) * x * (ρ * ρ * ρ)⁻¹ := by
      group
    rw [e, hρ3', one_mul, inv_one, mul_one]
  intro p hp
  obtain ⟨z, hz_def⟩ : ∃ z : G, z = ρ * p * ρ⁻¹ * p⁻¹ := ⟨_, rfl⟩
  have hzN : z ∈ N := by
    rw [hz_def]
    exact hδP p hp
  obtain ⟨w, hw_def⟩ : ∃ w : G, w = ρ * z * ρ⁻¹ * z⁻¹ := ⟨_, rfl⟩
  have hwZ : w ∈ Z := by
    rw [hw_def]
    exact hδN z hzN
  have E1 : ρ * p * ρ⁻¹ = z * p := by
    rw [hz_def]
    group
  have E2 : ρ * z * ρ⁻¹ = w * z := by
    rw [hw_def]
    group
  have E3 : z * z = 1 := hNsq z hzN
  have E4 : ρ * (z * p) * ρ⁻¹ = w * p := by
    calc ρ * (z * p) * ρ⁻¹ = (ρ * z * ρ⁻¹) * (ρ * p * ρ⁻¹) := by group
      _ = (w * z) * (z * p) := by rw [E2, E1]
      _ = w * (z * z) * p := by group
      _ = w * p := by rw [E3, mul_one]
  have E5 : ρ * (w * p) * ρ⁻¹ = w * (z * p) := by
    calc ρ * (w * p) * ρ⁻¹ = (ρ * w * ρ⁻¹) * (ρ * p * ρ⁻¹) := by group
      _ = w * (z * p) := by rw [hρZ w hwZ, E1]
  have E6 : p = w * (z * p) := by
    calc p = ρ * (ρ * (ρ * p * ρ⁻¹) * ρ⁻¹) * ρ⁻¹ := (hI2 p).symm
      _ = ρ * (ρ * (z * p) * ρ⁻¹) * ρ⁻¹ := by rw [E1]
      _ = ρ * (w * p) * ρ⁻¹ := by rw [E4]
      _ = w * (z * p) := E5
  have E7 : w * z = 1 := by
    have h7 : w * z * p = 1 * p := by
      rw [one_mul, mul_assoc]
      exact E6.symm
    exact mul_right_cancel h7
  have hzw : z = w⁻¹ := eq_inv_of_mul_eq_one_right E7
  rw [← hz_def, hzw]
  exact Z.inv_mem hwZ

end CFSG.RankThree.GF2n.Tim79a
