module

public import CFSG.Foundations.Basic
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.Quasithin.C1Pack

open Matrix
open scoped commutatorElement

abbrev SL2F2 : Type := SpecialLinearGroup (Fin 2) (ZMod 2)

def sl2A3 : Subgroup SL2F2 where
  carrier := {x | x ^ 3 = 1}
  one_mem' := one_pow 3
  mul_mem' := by
    have key : ∀ x y : SL2F2, x ^ 3 = 1 → y ^ 3 = 1 → (x * y) ^ 3 = 1 := by decide
    exact fun {x y} hx hy => key x y hx hy
  inv_mem' := by
    have key : ∀ x : SL2F2, x ^ 3 = 1 → x⁻¹ ^ 3 = 1 := by decide
    exact fun {x} hx => key x hx

theorem mem_sl2A3 {x : SL2F2} : x ∈ sl2A3 ↔ x ^ 3 = 1 := Iff.rfl

theorem card_sl2F2 : Nat.card SL2F2 = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_sl2A3 : Nat.card sl2A3 = 3 := by
  have h : Nat.card sl2A3 = Nat.card {x : SL2F2 // x ^ 3 = 1} := Nat.card_congr (Equiv.refl _)
  rw [h, Nat.card_eq_fintype_card]
  exact (by decide : Fintype.card {x : SL2F2 // x ^ 3 = 1} = 3)

instance : Nontrivial SL2F2 :=
  Finite.one_lt_card_iff_nontrivial.mp (by rw [card_sl2F2]; norm_num)

theorem sl2A3_normal : sl2A3.Normal := by
  have key : ∀ g x : SL2F2, x ^ 3 = 1 → (g * x * g⁻¹) ^ 3 = 1 := by decide
  exact ⟨fun x hx g => key g x hx⟩

theorem commutator_sl2_eq : commutator SL2F2 = sl2A3 := by
  apply le_antisymm
  · rw [commutator_def, Subgroup.commutator_le]
    have key : ∀ x y : SL2F2, ⁅x, y⁆ ^ 3 = 1 := by decide
    exact fun x _ y _ => key x y
  · intro a ha
    have key : ∀ a : SL2F2, a ^ 3 = 1 → ∃ x y : SL2F2, ⁅x, y⁆ = a := by decide
    obtain ⟨x, y, rfl⟩ := key a ha
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)

instance : Group.IsSolvable SL2F2 := by
  refine ⟨⟨2, ?_⟩⟩
  rw [derivedSeries_succ, derivedSeries_one, commutator_sl2_eq]
  rw [eq_bot_iff, Subgroup.commutator_le]
  have key : ∀ x y : SL2F2, x ^ 3 = 1 → y ^ 3 = 1 → ⁅x, y⁆ = 1 := by decide
  exact fun x hx y hy => (Subgroup.mem_bot).2 (key x y hx hy)

theorem center_sl2_eq_bot : Subgroup.center SL2F2 = ⊥ := by
  have key : ∀ x : SL2F2, (∀ y : SL2F2, y * x = x * y) → x = 1 := by decide
  rw [eq_bot_iff]
  intro x hx
  exact (Subgroup.mem_bot).2 (key x (Subgroup.mem_center_iff.1 hx))

theorem not_isNilpotent_sl2 : ¬ Group.IsNilpotent SL2F2 := by
  intro h
  exact Group.IsNilpotent.center_ne_bot (G := SL2F2) center_sl2_eq_bot

theorem layer_eq_bot_of_isSolvable' {G : Type*} [Group G] [Group.IsSolvable G] :
    CFSG.layer G = ⊥ :=
  CFSG.WholeGroup.layer_eq_bot_of_isSolvable

theorem generalizedFitting_sl2 : CFSG.generalizedFitting SL2F2 = commutator SL2F2 := by
  rw [CFSG.generalizedFitting, layer_eq_bot_of_isSolvable', sup_bot_eq,
    commutator_sl2_eq]
  have hA : IsPGroup 3 sl2A3 := fun x => ⟨1, by
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact mem_sl2A3.1 x.2⟩
  have hnil : Group.IsNilpotent sl2A3 := hA.isNilpotent
  have hle : sl2A3 ≤ CFSG.fittingSubgroup SL2F2 := le_sSup ⟨sl2A3_normal, hnil⟩
  have hne : CFSG.fittingSubgroup SL2F2 ≠ ⊤ := by
    intro htop
    apply not_isNilpotent_sl2
    have h1 : Group.IsNilpotent ↥(CFSG.fittingSubgroup SL2F2) := inferInstance
    rw [htop] at h1
    exact Group.nilpotent_of_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup SL2F2) ≃* SL2F2)
  have hdvd1 : 3 ∣ Nat.card (CFSG.fittingSubgroup SL2F2) := card_sl2A3 ▸ Subgroup.card_dvd_of_le hle
  have hdvd2 : Nat.card (CFSG.fittingSubgroup SL2F2) ∣ 6 :=
    card_sl2F2 ▸ Subgroup.card_subgroup_dvd_card _
  have hcard : Nat.card (CFSG.fittingSubgroup SL2F2) = 3 := by
    have h6 : Nat.card (CFSG.fittingSubgroup SL2F2) ≠ 6 := by
      intro h6
      apply hne
      apply Subgroup.eq_top_of_card_eq
      rw [h6, card_sl2F2]
    have hd : Nat.card (CFSG.fittingSubgroup SL2F2) ∈ Nat.divisors 6 :=
      Nat.mem_divisors.2 ⟨hdvd2, by norm_num⟩
    have hd' : Nat.card (CFSG.fittingSubgroup SL2F2) = 1 ∨ Nat.card (CFSG.fittingSubgroup SL2F2) = 2 ∨
        Nat.card (CFSG.fittingSubgroup SL2F2) = 3 ∨ Nat.card (CFSG.fittingSubgroup SL2F2) = 6 := by
      have : Nat.divisors 6 = {1, 2, 3, 6} := by decide
      rw [this] at hd
      simpa using hd
    rcases hd' with h | h | h | h
    · rw [h] at hdvd1; omega
    · rw [h] at hdvd1; omega
    · exact h
    · exact absurd h h6
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_sl2A3])).symm

theorem sl2_eq_zero_of_fixed : ∀ t : SL2F2, t ^ 3 = 1 → t ≠ 1 → ∀ y : Fin 2 → ZMod 2,
    (t : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ y = y → y = 0 := by decide

theorem sl2_exists_sub_eq : ∀ t : SL2F2, t ^ 3 = 1 → t ≠ 1 → ∀ x : Fin 2 → ZMod 2,
    ∃ y : Fin 2 → ZMod 2, (t : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ y - y = x := by decide

theorem sl2_sq_pow_three : ∀ z : SL2F2, (z ^ 2) ^ 3 = 1 := by decide

theorem sl2_not_commute : ∀ s : SL2F2, s ^ 2 = 1 → s ≠ 1 → ∀ t : SL2F2, t ^ 3 = 1 → t ≠ 1 →
    ⁅t, s⁆ ≠ 1 := by decide

end CFSG.Quasithin.C1Pack
