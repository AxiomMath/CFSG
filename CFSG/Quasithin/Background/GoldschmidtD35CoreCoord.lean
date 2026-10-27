module

public import CFSG.Quasithin.Background.GoldschmidtD35CoreField

public section

namespace CFSG.Quasithin.D35Core

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

theorem false_of_expansion {u v w : V} (huvw : LinearIndependent F ![u, v, w]) {α β : F}
    (h : w = α • u + β • v) : False := by
  have := Fintype.linearIndependent_iff.1 huvw ![α, β, -1] (by
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, neg_smul, one_smul]
    rw [h]
    module) 2
  simp at this

theorem repr_expansion (b : Module.Basis (Fin 3) F V) (w : V) :
    w = b.repr w 0 • b 0 + b.repr w 1 • b 1 + b.repr w 2 • b 2 := by
  conv_lhs => rw [← b.sum_repr w]
  rw [Fin.sum_univ_three]

theorem coord_ne_zero (b : Module.Basis (Fin 3) F V) {w : V}
    (h01 : LinearIndependent F ![b 0, b 1, w]) (h02 : LinearIndependent F ![b 0, b 2, w])
    (h12 : LinearIndependent F ![b 1, b 2, w]) :
    b.repr w 0 ≠ 0 ∧ b.repr w 1 ≠ 0 ∧ b.repr w 2 ≠ 0 := by
  have hexp := repr_expansion b w
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · refine false_of_expansion h12 (α := b.repr w 1) (β := b.repr w 2) ?_
    conv_lhs => rw [hexp]
    rw [h, zero_smul, zero_add]
  · refine false_of_expansion h02 (α := b.repr w 0) (β := b.repr w 2) ?_
    conv_lhs => rw [hexp]
    rw [h, zero_smul, add_zero]
  · refine false_of_expansion h01 (α := b.repr w 0) (β := b.repr w 1) ?_
    conv_lhs => rw [hexp]
    rw [h, zero_smul, add_zero]

theorem coord_ne_of_unit (b : Module.Basis (Fin 3) F V) {w : V}
    (h0 : LinearIndependent F ![b 0, b 0 + b 1 + b 2, w])
    (h1 : LinearIndependent F ![b 1, b 0 + b 1 + b 2, w])
    (h2 : LinearIndependent F ![b 2, b 0 + b 1 + b 2, w]) :
    b.repr w 0 ≠ b.repr w 1 ∧ b.repr w 0 ≠ b.repr w 2 ∧ b.repr w 1 ≠ b.repr w 2 := by
  have hexp := repr_expansion b w
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · refine false_of_expansion h2 (α := b.repr w 2 - b.repr w 0) (β := b.repr w 0) ?_
    conv_lhs => rw [hexp]
    rw [← h]
    module
  · refine false_of_expansion h1 (α := b.repr w 1 - b.repr w 0) (β := b.repr w 0) ?_
    conv_lhs => rw [hexp]
    rw [← h]
    module
  · refine false_of_expansion h0 (α := b.repr w 0 - b.repr w 1) (β := b.repr w 1) ?_
    conv_lhs => rw [hexp]
    rw [← h]
    module

theorem sq_ratio (hF : Nat.card F = 4) [Finite F] {a₀ a₁ a₂ : F} (h0 : a₀ ≠ 0) (h1 : a₁ ≠ 0)
    (h2 : a₂ ≠ 0) (h01 : a₀ ≠ a₁) (h02 : a₀ ≠ a₂) (h12 : a₁ ≠ a₂) :
    a₂ = a₀ * (a₁ / a₀) ^ 2 := by
  have hs1 : a₁ / a₀ ≠ 1 := fun h => h01 (by rw [div_eq_one_iff_eq h0] at h; exact h.symm)
  have ht1 : a₂ / a₀ ≠ 1 := fun h => h02 (by rw [div_eq_one_iff_eq h0] at h; exact h.symm)
  have ht : a₂ / a₀ = a₁ / a₀ ∨ a₂ / a₀ = (a₁ / a₀) ^ 2 :=
    eq_or_eq_sq hF (div_ne_zero h1 h0) hs1 (div_ne_zero h2 h0) ht1
  rcases ht with h | h
  · exact absurd ((div_left_inj' h0).1 h).symm h12
  · field_simp at h ⊢
    exact h

end CFSG.Quasithin.D35Core
