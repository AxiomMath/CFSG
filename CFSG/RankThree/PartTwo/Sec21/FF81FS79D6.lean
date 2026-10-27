module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Fr6
public import CFSG.RankThree.PartOne.Q1327T.Perm3

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open Equiv

namespace J6

def ainv : S6 := swap 0 1 * swap 3 4

def D6fin : Finset S6 := {1, d', d' * d', sg3, d' * sg3, d' * d' * sg3}

theorem D6fin_card : D6fin.card = 6 := by decide +kernel

theorem D6fin_mul : ∀ a ∈ D6fin, ∀ b ∈ D6fin, a * b ∈ D6fin := by decide +kernel

theorem D6fin_inv : ∀ a ∈ D6fin, a⁻¹ ∈ D6fin := by decide +kernel

theorem one_mem_D6fin : (1 : S6) ∈ D6fin := by decide +kernel

def D6 : Subgroup S6 where
  carrier := {σ | σ ∈ D6fin}
  mul_mem' := fun {a b} ha hb => D6fin_mul a ha b hb
  one_mem' := one_mem_D6fin
  inv_mem' := fun {a} ha => D6fin_inv a ha

theorem card_D6 : Nat.card D6 = 6 := by
  rw [card_of_finset D6fin D6 (fun σ => Iff.rfl), D6fin_card]

theorem d'_pow_three : d' ^ 3 = 1 := by decide +kernel

theorem d'_ne_one : d' ≠ 1 := by decide +kernel

theorem sg3_d'_conj : sg3 * d' * sg3⁻¹ = d'⁻¹ := by decide +kernel

theorem sg3_c₁_conj : sg3 * c₁ * sg3⁻¹ = c₂ := by decide +kernel

theorem sg3_c₂_conj : sg3 * c₂ * sg3⁻¹ = c₁ := by decide +kernel

theorem c₁_eq : c₁ = d' * d' * (d * d) := by decide +kernel

theorem c₂_eq : c₂ = d'⁻¹ * d'⁻¹ * (d * d) := by decide +kernel

theorem ainv_d_conj : ainv * d * ainv⁻¹ = d⁻¹ := by decide +kernel

theorem cen_d : ∀ σ : S6, σ * d = d * σ → ∃ ρ ∈ D6fin, ∃ k : Fin 3, σ = ρ * d ^ k.val := by
  decide +kernel

theorem D6fin_comm_d : ∀ ρ ∈ D6fin, ρ * d = d * ρ := by decide +kernel

theorem d_not_mem_D6fin : d ∉ D6fin := by decide +kernel

theorem cen_c₁_acts : ∀ σ : S6, σ * c₁ = c₁ * σ →
    σ * c₂ * σ⁻¹ = c₂ ∨ σ * c₂ * σ⁻¹ = c₂⁻¹ := by decide +kernel

theorem pair_eq_d : ∀ x ∈ ([c₁, c₁⁻¹, c₂, c₂⁻¹] : List S6), ∀ y ∈ ([c₁, c₁⁻¹, c₂, c₂⁻¹] : List S6),
    x * y = d → (x = c₁ ∧ y = c₂) ∨ (x = c₂ ∧ y = c₁) := by decide +kernel

theorem d'_mem_D6 : d' ∈ D6 := (by decide +kernel : d' ∈ D6fin)

theorem sg3_mem_D6 : sg3 ∈ D6 := (by decide +kernel : sg3 ∈ D6fin)

theorem D6_iso : Nonempty (↥D6 ≃* Perm (Fin 3)) := by
  refine CFSG.RankThree.PartOne.Q1327T.nonempty_mulEquiv_perm_three (⟨d', d'_mem_D6⟩ : ↥D6)
    (⟨sg3, sg3_mem_D6⟩ : ↥D6) ?_ ?_ ?_ ?_ ?_ card_D6
  · exact Subtype.ext d'_pow_three
  · intro h
    exact d'_ne_one (congrArg Subtype.val h)
  · exact Subtype.ext sg3_sq
  · intro h
    exact sg3_ne_one (congrArg Subtype.val h)
  · exact Subtype.ext sg3_d'_conj

end J6

end CFSG.RankThree.PartTwo.Sec21.FF81
