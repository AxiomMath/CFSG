module

public import CFSG.Quasithin.H13.L32AVolI

public section

namespace CFSG.Quasithin.H13.A6.A6S19

open CFSG.Quasithin.H6

@[expose] def IsUl (g : Γ) : Prop :=
  (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 1 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 2 = 1

instance : DecidablePred IsUl := fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem isUl_mul : ∀ g h : Γ, IsUl g → IsUl h → IsUl (g * h) := by
  decide +kernel

theorem isUl_inv : ∀ g : Γ, IsUl g → IsUl g⁻¹ := by
  decide +kernel

@[expose] def Ul : Subgroup Γ where
  carrier := {g | IsUl g}
  one_mem' := by decide
  mul_mem' {g h} hg hh := isUl_mul g h hg hh
  inv_mem' {g} hg := isUl_inv g hg

@[expose] def IsB (g : Γ) : Prop :=
  (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0

instance : DecidablePred IsB := fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem mem_borel_iff (g : Γ) : g ∈ H6.borel ↔ IsB g := by
  unfold H6.borel H6.Lp
  rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  show (g • (![1, 0, 0] : V3) = ![1, 0, 0] ∧ IsLl g) ↔ IsB g
  revert g
  decide +kernel

theorem isUl_of_conj : ∀ c x : Γ, (IsLl c ∧ c ^ 3 = 1 ∧ c ≠ 1 ∧ IsB x ∧
    IsB (c * x * c⁻¹) ∧ IsB (c⁻¹ * x * c)) → IsUl x := by
  decide +kernel

theorem mem_Ul_of_conj {c x : Γ} (hc : c ∈ Ll) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hx : x ∈ H6.borel) (h1 : c * x * c⁻¹ ∈ H6.borel) (h2 : c⁻¹ * x * c ∈ H6.borel) :
    x ∈ Ul := by
  rw [mem_borel_iff] at hx h1 h2
  exact isUl_of_conj c x ⟨hc, hc3, hc1, hx, h1, h2⟩

theorem four_mul_card_fix_st : ∀ g : Γ, IsUl g → g ≠ 1 →
    4 * Fintype.card {m : St // ρSt g m = m} ≤ Fintype.card St := by
  decide +kernel

theorem four_mul_card_fix_core : ∀ g : Γ, IsUl g → g ≠ 1 →
    4 * Fintype.card {m : Core // ρCore g m = m} ≤ Fintype.card Core := by
  decide +kernel

theorem not_quad_st : ∃ a b : Γ, IsUl a ∧ IsUl b ∧ ∃ m : St,
    ρSt b (m - ρSt a m) ≠ m - ρSt a m := by
  decide +kernel

theorem not_quad_core : ∃ a b : Γ, IsUl a ∧ IsUl b ∧ ∃ m : Core,
    ρCore b (m - ρCore a m) ≠ m - ρCore a m := by
  decide +kernel

theorem card_Ul : Nat.card Ul = 4 := by
  show Nat.card {g : Γ // IsUl g} = 4
  rw [Nat.card_eq_fintype_card]
  decide +kernel

end CFSG.Quasithin.H13.A6.A6S19
