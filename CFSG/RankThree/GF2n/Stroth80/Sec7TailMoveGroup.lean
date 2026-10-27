module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveOpm
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup
open scoped commutatorElement

theorem comm_of_semilinear {X : Type*} [Group X] (V Y : Subgroup X) [Finite Y]
    (hYK : ∀ y ∈ Y, y ∈ Subgroup.normalizer (V : Set X))
    (hti : ∀ g : X, ∀ y ∈ Y, y ≠ 1 → g * y * g⁻¹ ∈ Y → g ∈ Subgroup.normalizer (Y : Set X))
    (hsl : Nat.card Y ≤ 2 * Nat.card ↥(Subgroup.centralizer (V : Set X) ⊓ Y))
    (hY4 : 4 ≤ Nat.card Y)
    (hVY : V ⊓ Y = ⊥) : ∀ v ∈ V, ∀ y ∈ Y, v * y = y * v := by
  have hC2 : 2 ≤ Nat.card ↥(Subgroup.centralizer (V : Set X) ⊓ Y) := by omega
  have hex : ∃ y₀ ∈ Subgroup.centralizer (V : Set X) ⊓ Y, y₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : Subgroup.centralizer (V : Set X) ⊓ Y = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      exact hcon
    rw [hbot, Subgroup.card_bot] at hC2
    omega
  obtain ⟨y₀, hy₀C, hy₀1⟩ := hex
  obtain ⟨hy₀c, hy₀Y⟩ := Subgroup.mem_inf.mp hy₀C
  have hnormY : ∀ v ∈ V, v ∈ Subgroup.normalizer (Y : Set X) := by
    intro v hv
    apply hti v y₀ hy₀Y hy₀1
    have hcomm : v * y₀ = y₀ * v := Subgroup.mem_centralizer_iff.mp hy₀c v hv
    rw [hcomm, mul_inv_cancel_right]
    exact hy₀Y
  intro v hv y hy
  have hc_Y : v * y * v⁻¹ * y⁻¹ ∈ Y := by
    have h1 : v * y * v⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hnormY v hv) y).mp hy
    exact Y.mul_mem h1 (Y.inv_mem hy)
  have hc_V : v * y * v⁻¹ * y⁻¹ ∈ V := by
    have h2 : y * v⁻¹ * y⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hYK y hy) v⁻¹).mp (V.inv_mem hv)
    have e : v * y * v⁻¹ * y⁻¹ = v * (y * v⁻¹ * y⁻¹) := by simp only [mul_assoc]
    rw [e]
    exact V.mul_mem hv h2
  have hc1 : v * y * v⁻¹ * y⁻¹ = 1 := by
    have hmem : v * y * v⁻¹ * y⁻¹ ∈ V ⊓ Y := Subgroup.mem_inf.mpr ⟨hc_V, hc_Y⟩
    rw [hVY, Subgroup.mem_bot] at hmem
    exact hmem
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc1)

theorem exists_conj_in_L_of_adjacent {X : Type*} [Group X] (V Y L NbY : Subgroup X) (y x : X)
    (hYL : ∀ z ∈ Y, z ∈ L → z = 1) (hLab : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a)
    (hyL : ∀ l ∈ L, y * l * y⁻¹ ∈ L)
    (hti : ∀ g : X, ∀ z ∈ Y, z ≠ 1 → g * z * g⁻¹ ∈ Y → g ∈ Subgroup.normalizer (Y : Set X))
    (hsemi : ∀ z ∈ NbY, z ∉ Y → ∀ w ∈ Y, ∃ m ∈ NbY, m * z * m⁻¹ = w * z)
    (hVnot : ∀ n ∈ L, y * n * y⁻¹ * n⁻¹ ∈ V → y * n * y⁻¹ * n⁻¹ = 1)
    (hyY : y ∈ Y) (hy1 : y ≠ 1) (hy2 : y * y = 1)
    (hyV : ∃ a ∈ V, a ≠ 1 ∧ ∃ h : X, y = h * a * h⁻¹)
    (hxL : x ∈ L) (hxy : x * y * x⁻¹ ≠ y) (hxN : x * y * x⁻¹ ∈ NbY) :
    ∃ s ∈ V, s ≠ 1 ∧ ∃ g : X, g * s * g⁻¹ ∈ L ∧ g * s * g⁻¹ ∉ V := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hu_eq : y * (x * y * x⁻¹) = y * x * y⁻¹ * x⁻¹ := by
    rw [hyinv]
    simp only [mul_assoc]
  have huL : y * x * y⁻¹ * x⁻¹ ∈ L := L.mul_mem (hyL x hxL) (L.inv_mem hxL)
  have hu1 : y * x * y⁻¹ * x⁻¹ ≠ 1 := by
    intro h
    have h' : y * (x * y * x⁻¹) = 1 := hu_eq.trans h
    exact hxy ((eq_inv_of_mul_eq_one_right h').trans hyinv)
  have huV : y * x * y⁻¹ * x⁻¹ ∉ V := fun h => hu1 (hVnot x hxL h)
  have hyN : x * y * x⁻¹ ∉ Y := by
    intro h
    have hY' : y * (x * y * x⁻¹) ∈ Y := Y.mul_mem hyY h
    rw [hu_eq] at hY'
    exact hu1 (hYL _ hY' huL)
  obtain ⟨m, hmN, hm⟩ := hsemi (x * y * x⁻¹) hxN hyN y hyY
  obtain ⟨a, haV, ha1, h, hyh⟩ := hyV
  have hconj : m * x * h * a * (m * x * h)⁻¹ = m * (x * y * x⁻¹) * m⁻¹ := by
    rw [hyh]
    simp only [mul_inv_rev, mul_assoc]
  refine ⟨a, haV, ha1, m * x * h, ?_, ?_⟩
  · rw [hconj, hm, hu_eq]
    exact huL
  · rw [hconj, hm, hu_eq]
    exact huV

end CFSG.RankThree.GF2n.Stroth80
