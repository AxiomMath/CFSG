module

public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Finite.Perm
public import Mathlib.GroupTheory.Sylow
import CFSG.Mathlib.Decide.Bounded

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.U43

open Equiv Equiv.Perm
open scoped CFSG.Decide.Bounded

namespace A6Sylow

def c1 : Perm (Fin 6) := c[0, 1, 2]

def c2 : Perm (Fin 6) := c[3, 4, 5]

def S0fin : Finset (Perm (Fin 6)) :=
  (Finset.univ : Finset (Fin 3 × Fin 3)).image fun p => c1 ^ p.1.val * c2 ^ p.2.val

theorem S0fin_card : S0fin.card = 9 := by decide +kernel

theorem S0fin_mul : ∀ a ∈ S0fin, ∀ b ∈ S0fin, a * b ∈ S0fin := by decide +kernel

theorem S0fin_one : (1 : Perm (Fin 6)) ∈ S0fin := by decide +kernel

theorem S0fin_inv : ∀ a ∈ S0fin, a⁻¹ ∈ S0fin := by decide +kernel

theorem S0fin_cent : ∀ x : Perm (Fin 6), (∀ s ∈ S0fin, x * s = s * x) → x ∈ S0fin := by
  decide +kernel

def n0 : Perm (Fin 6) := c[0, 1] * (c[0, 3] * c[1, 4] * c[2, 5])

theorem n0_facts : Perm.sign n0 = 1 ∧ (∀ s : Perm (Fin 6), s ∈ S0fin ↔ n0 * s * n0⁻¹ ∈ S0fin) ∧
    n0 * n0 ∉ S0fin := by decide +kernel

def S0 : Subgroup (Perm (Fin 6)) where
  carrier := ↑S0fin
  mul_mem' := fun {a b} ha hb => S0fin_mul a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb)
  one_mem' := S0fin_one
  inv_mem' := fun {a} ha => S0fin_inv a (Finset.mem_coe.mp ha)

theorem card_S0 : Nat.card S0 = 9 := by
  have : Nat.card S0 = Nat.card {x // x ∈ S0fin} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
  rw [this, Nat.card_eq_fintype_card, Fintype.card_coe, S0fin_card]

theorem card_perm6 : Nat.card (Perm (Fin 6)) = 720 := by
  rw [Nat.card_perm]
  simp [Nat.factorial]

theorem exists_conj_S0 (S : Subgroup (Perm (Fin 6))) (hS : Nat.card S = 9) :
    ∃ g : Perm (Fin 6), ∀ x, x ∈ S ↔ g⁻¹ * x * g ∈ S0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hidx : ∀ T : Subgroup (Perm (Fin 6)), Nat.card T = 9 → ¬ 3 ∣ T.index := by
    intro T hT h3
    have := Subgroup.card_mul_index T
    rw [hT, card_perm6] at this
    have : T.index = 80 := by omega
    rw [this] at h3
    omega
  let P₀ : Sylow 3 (Perm (Fin 6)) :=
    (IsPGroup.of_card (n := 2) (by rw [card_S0]; norm_num)).toSylow (hidx S0 card_S0)
  let P₁ : Sylow 3 (Perm (Fin 6)) :=
    (IsPGroup.of_card (n := 2) (by rw [hS]; norm_num)).toSylow (hidx S hS)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 6)) P₀ P₁
  refine ⟨g, fun x => ?_⟩
  have h1 : (P₁ : Set (Perm (Fin 6))) =
      MulAut.conj g • ((P₀ : Subgroup (Perm (Fin 6))) : Set _) := by
    rw [← hg, Sylow.coe_smul]
    rfl
  have hP₁ : x ∈ S ↔ x ∈ (P₁ : Set (Perm (Fin 6))) := Iff.rfl
  rw [hP₁, h1, Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : g⁻¹ * (MulAut.conj g • y) * g = y := by
      simp [MulAut.smul_def, MulAut.conj_apply]
      group
    rw [this]
    exact hy
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply]
    group

theorem S6_sylow3 (S : Subgroup (Perm (Fin 6))) (hS : Nat.card S = 9) :
    (∀ x : Perm (Fin 6), (∀ s ∈ S, x * s = s * x) → x ∈ S) ∧
    ∃ n : Perm (Fin 6), Perm.sign n = 1 ∧ (∀ s, s ∈ S ↔ n * s * n⁻¹ ∈ S) ∧ n * n ∉ S := by
  obtain ⟨g, hg⟩ := exists_conj_S0 S hS
  constructor
  · intro x hx
    rw [hg]
    apply S0fin_cent
    intro s hs
    have hs' : g * s * g⁻¹ ∈ S := by
      rw [hg]
      have e : g⁻¹ * (g * s * g⁻¹) * g = s := by group
      rw [e]
      exact hs
    have hc := hx _ hs'
    calc g⁻¹ * x * g * s = g⁻¹ * (x * (g * s * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * s * g⁻¹) * x) * g := by rw [hc]
      _ = s * (g⁻¹ * x * g) := by group
  · refine ⟨g * n0 * g⁻¹, ?_, fun s => ?_, ?_⟩
    · rw [map_mul, map_mul, map_inv, n0_facts.1, mul_one, mul_inv_cancel]
    · rw [hg, hg]
      have e : g⁻¹ * ((g * n0 * g⁻¹) * s * (g * n0 * g⁻¹)⁻¹) * g = n0 * (g⁻¹ * s * g) * n0⁻¹ := by
        group
      rw [e]
      exact n0_facts.2.1 (g⁻¹ * s * g)
    · rw [hg]
      have e : g⁻¹ * ((g * n0 * g⁻¹) * (g * n0 * g⁻¹)) * g = n0 * n0 := by group
      rw [e]
      exact n0_facts.2.2

end A6Sylow

end CFSG.Quasithin.H13.U43
