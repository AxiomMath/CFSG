module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B4L3Fin
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Quasithin CFSG.Quasithin.L3

theorem exists_three : ∀ c : Vec, c ≠ 0 → ∃ y : Γ, act y c = c ∧ y * y * y = 1 ∧ y ≠ 1 := by
  decide +kernel

theorem as_three_cent : ∀ c : Vec, c ≠ 0 → ∀ y : Γ, act y c = c → y * y * y = 1 → y ≠ 1 →
    ∀ γ ∈ AS {0, c}, γ * y = y * γ → γ = 1 := by
  decide +kernel

theorem three_fix : ∀ c : Vec, c ≠ 0 → ∀ y : Γ, act y c = c → y * y * y = 1 → y ≠ 1 →
    ∀ w : Vec, act y w = w → w = 0 ∨ w = c := by
  decide +kernel

theorem card_stab : ∀ c : Vec, c ≠ 0 →
    (Finset.univ.filter fun γ : Γ => act γ c = c).card = 24 := by
  decide +kernel

theorem a4_gen : ∀ c : Vec, c ≠ 0 → ∀ δ γ : Γ, act δ c = c → δ * δ * δ = 1 → δ ≠ 1 →
    act γ c = c → γ * γ * γ ∈ AS {0, c} →
      γ * γ = 1 ∨ (δ⁻¹ * γ) * (δ⁻¹ * γ) = 1 ∨ (δ⁻¹ * δ⁻¹ * γ) * (δ⁻¹ * δ⁻¹ * γ) = 1 := by
  decide +kernel

@[expose] def StabSub (c : Vec) : Subgroup Γ where
  carrier := {γ | act γ c = c}
  mul_mem' := fun {a b} ha hb => by
    change act (a * b) c = c
    rw [act_mul, show act b c = c from hb, show act a c = c from ha]
  one_mem' := act_one c
  inv_mem' := fun {a} ha => by
    change act a⁻¹ c = c
    conv_lhs => rw [← show act a c = c from ha]
    exact act_inv_act a c

theorem card_StabSub {c : Vec} (hc : c ≠ 0) : Nat.card (StabSub c) = 24 := by
  classical
  rw [← card_stab c hc, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun γ => Iff.rfl)

end N1246

end CFSG.Quasithin.H13
