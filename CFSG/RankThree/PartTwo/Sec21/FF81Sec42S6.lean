module

public import Mathlib.GroupTheory.Sylow
import CFSG.LargeExtraspecial.AS35YFSymAut
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open Equiv Equiv.Perm

namespace S6Aut

def c₁ : Perm (Fin 6) := swap 0 1 * swap 1 2

def c₂ : Perm (Fin 6) := swap 3 4 * swap 4 5

set_option maxRecDepth 100000 in
theorem swap_of_fix_P₀ : ∀ π : Perm (Fin 6), π * π = 1 → π * c₂ = c₂ * π →
    π * c₁ * π⁻¹ = c₁⁻¹ → π = swap 0 1 ∨ π = swap 0 2 ∨ π = swap 1 2 := by
  decide

theorem swap01_c₁ : swap (0 : Fin 6) 1 * c₁ * (swap (0 : Fin 6) 1)⁻¹ = c₁⁻¹ := by decide

theorem swap01_c₂ : swap (0 : Fin 6) 1 * c₂ = c₂ * swap (0 : Fin 6) 1 := by decide

def P₀list : Finset (Perm (Fin 6)) :=
  {1, c₁, c₁ * c₁, c₂, c₂ * c₂, c₁ * c₂, c₁ * c₁ * c₂, c₁ * c₂ * c₂, c₁ * c₁ * c₂ * c₂}

set_option maxRecDepth 100000 in
theorem P₀list_card : P₀list.card = 9 := by decide

set_option maxRecDepth 100000 in
theorem P₀list_closed : ∀ x ∈ P₀list, ∀ y ∈ P₀list, x * y ∈ P₀list := by decide

set_option maxRecDepth 100000 in
theorem P₀list_inv : ∀ x ∈ P₀list, x⁻¹ ∈ P₀list := by decide

set_option maxRecDepth 100000 in
theorem P₀list_one : (1 : Perm (Fin 6)) ∈ P₀list := by decide

set_option maxRecDepth 100000 in
theorem P₀list_c₁ : c₁ ∈ P₀list := by decide

set_option maxRecDepth 100000 in
theorem P₀list_c₂ : c₂ ∈ P₀list := by decide

def P₀ : Subgroup (Perm (Fin 6)) where
  carrier := {y | y ∈ P₀list}
  mul_mem' := fun {a b} ha hb => P₀list_closed a ha b hb
  one_mem' := P₀list_one
  inv_mem' := fun {a} ha => P₀list_inv a ha

theorem card_P₀ : Nat.card P₀ = 9 := by
  rw [← P₀list_card, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

theorem card_perm_six : Nat.card (Perm (Fin 6)) = 720 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl

theorem isPGroup_index_of_card_nine {P : Subgroup (Perm (Fin 6))} (hP : Nat.card P = 9) :
    IsPGroup 3 P ∧ ¬ 3 ∣ P.index := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨IsPGroup.of_card (n := 2) (by rw [hP]; norm_num), ?_⟩
  have h := P.index_mul_card
  rw [hP, card_perm_six] at h
  have : P.index = 80 := by omega
  rw [this]; norm_num

end S6Aut

open S6Aut

theorem mulAut_inner_of_fix_card_nine {X : Type*} [Group X] (φ : X ≃* Perm (Fin 6))
    (E : Subgroup X) (hE : Nat.card E = 9) (α : X ≃* X) (hα : ∀ e ∈ E, α e = e) :
    ∃ j : X, ∀ y, α y = j * y * j⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set β : MulAut (Perm (Fin 6)) := (φ.symm.trans α).trans φ with hβ
  have hβapp : ∀ σ, β σ = φ (α (φ.symm σ)) := fun σ => rfl
  set P : Subgroup (Perm (Fin 6)) := E.map φ.toMonoidHom with hPdef
  have hPc : Nat.card P = 9 := by
    rw [hPdef, Subgroup.card_map_of_injective φ.injective, hE]
  have hPfix : ∀ p ∈ P, β p = p := by
    rintro _ ⟨e, he, rfl⟩
    rw [hβapp]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, hα e he]
  obtain ⟨hP3, hPi⟩ := isPGroup_index_of_card_nine hPc
  obtain ⟨hQ3, hQi⟩ := isPGroup_index_of_card_nine card_P₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 6)) (hQ3.toSylow hQi) (hP3.toSylow hPi)
  have hgP : ∀ q ∈ P₀, g * q * g⁻¹ ∈ P := by
    intro q hq
    have h1 : g * q * g⁻¹ ∈ ((g • hQ3.toSylow hQi : Sylow 3 (Perm (Fin 6))) : Subgroup _) := by
      rw [Sylow.coe_subgroup_smul]
      exact ⟨q, hq, rfl⟩
    rw [hg] at h1
    exact h1
  set β' : MulAut (Perm (Fin 6)) := ((MulAut.conj g).trans β).trans (MulAut.conj g⁻¹) with hβ'
  have hβ'app : ∀ σ, β' σ = g⁻¹ * β (g * σ * g⁻¹) * g := by
    intro σ; simp [hβ', MulAut.conj_apply]
  have hfix : ∀ q ∈ P₀, β' q = q := by
    intro q hq
    rw [hβ'app, hPfix _ (hgP q hq)]; group
  have hc₁ : c₁ ∈ P₀ := P₀list_c₁
  have hc₂ : c₂ ∈ P₀ := P₀list_c₂
  set π := β' (swap 0 1) with hπ
  have hπ2 : π * π = 1 := by
    rw [hπ, ← map_mul, swap_mul_self, map_one]
  have hπc₂ : π * c₂ = c₂ * π := by
    rw [hπ, ← hfix c₂ hc₂, ← map_mul, ← map_mul, swap01_c₂]
  have hπc₁ : π * c₁ * π⁻¹ = c₁⁻¹ := by
    rw [hπ, ← hfix c₁ hc₁, ← map_inv, ← map_mul, ← map_mul, swap01_c₁, map_inv]
  have hπs : π.IsSwap := by
    rcases swap_of_fix_P₀ π hπ2 hπc₂ hπc₁ with h | h | h <;> rw [h] <;>
      exact ⟨_, _, by decide, rfl⟩
  have hsw : ∀ σ : Perm (Fin 6), σ.IsSwap → (β' σ).IsSwap := by
    rintro σ ⟨a, b, hab, rfl⟩
    obtain ⟨h, hh⟩ := isConj_iff.mp (isConj_swap (by decide : (0 : Fin 6) ≠ 1) hab)
    rw [← hh, map_mul, map_mul, map_inv, ← hπ]
    obtain ⟨u, v, huv, huvπ⟩ := hπs
    rw [huvπ, ← swap_apply_apply]
    exact ⟨_, _, fun e => huv ((β' h).injective e), rfl⟩
  obtain ⟨π₀, hπ₀⟩ := CFSG.LargeExtraspecial.AS35YF.perm_aut_eq_conj_of_isSwap β' hsw
    (by norm_num)
  refine ⟨φ.symm (g * π₀ * g⁻¹), fun y => ?_⟩
  apply φ.injective
  have h1 : β (φ y) = φ (α y) := by rw [hβapp, MulEquiv.symm_apply_apply]
  have h2 : β (φ y) = g * β' (g⁻¹ * φ y * g) * g⁻¹ := by
    rw [hβ'app]; group
  rw [← h1, h2, hπ₀, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  group

end CFSG.RankThree.PartTwo.Sec21.FF81
