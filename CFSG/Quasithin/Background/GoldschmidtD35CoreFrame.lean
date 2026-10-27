module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.GoldschmidtD35CoreIrr

public section

namespace CFSG.Quasithin.D35Core

open CFSG.QuasithinUnique.Setup.X3 Equiv
open scoped LinearAlgebra.Projectivization

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
variable {L : Subgroup (V ≃ₗ[F] V)} {pt : Fin 6 → ℙ F V}

theorem eq_smul_of_frame [FiniteDimensional F V] (hV : Module.finrank F V = 3)
    {c₀ c₁ c₂ c₃ : V}
    (h012 : LinearIndependent F ![c₀, c₁, c₂]) (h013 : LinearIndependent F ![c₀, c₁, c₃])
    (h023 : LinearIndependent F ![c₀, c₂, c₃]) (h123 : LinearIndependent F ![c₁, c₂, c₃])
    (y : V →ₗ[F] V) {a₀ a₁ a₂ a₃ : F} (hy₀ : y c₀ = a₀ • c₀) (hy₁ : y c₁ = a₁ • c₁)
    (hy₂ : y c₂ = a₂ • c₂) (hy₃ : y c₃ = a₃ • c₃) : y = a₃ • LinearMap.id := by
  have hspan : Submodule.span F (Set.range ![c₀, c₁, c₂]) = ⊤ :=
    h012.span_eq_top_of_card_eq_finrank (by simp [hV])
  have hmem : ∀ v : V, ∃ b : Fin 3 → F, v = b 0 • c₀ + b 1 • c₁ + b 2 • c₂ := by
    intro v
    have hv : v ∈ Submodule.span F (Set.range ![c₀, c₁, c₂]) := hspan ▸ Submodule.mem_top
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hv
    refine ⟨b, ?_⟩
    rw [← hb, Fin.sum_univ_three]
    rfl
  have hli := Fintype.linearIndependent_iff.1 h012
  have hli013 := Fintype.linearIndependent_iff.1 h013
  have hli023 := Fintype.linearIndependent_iff.1 h023
  have hli123 := Fintype.linearIndependent_iff.1 h123
  obtain ⟨b, hb⟩ := hmem c₃
  have hb2 : b 2 ≠ 0 := by
    intro h0
    have := hli013 ![b 0, b 1, -1] (by
      rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, neg_smul, one_smul]
      rw [hb, h0, zero_smul, add_zero]
      module) 2
    simp at this
  have hb1 : b 1 ≠ 0 := by
    intro h0
    have := hli023 ![b 0, b 2, -1] (by
      rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, neg_smul, one_smul]
      rw [hb, h0, zero_smul, add_zero]
      module) 2
    simp at this
  have hb0 : b 0 ≠ 0 := by
    intro h0
    have := hli123 ![b 1, b 2, -1] (by
      rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, neg_smul, one_smul]
      rw [hb, h0, zero_smul, zero_add]
      module) 2
    simp at this
  have h1 : y c₃ = b 0 • y c₀ + b 1 • y c₁ + b 2 • y c₂ := by
    rw [hb, map_add, map_add, map_smul, map_smul, map_smul]
  rw [hy₃, hy₀, hy₁, hy₂, hb] at h1
  have hrel := hli ![b 0 * a₀ - a₃ * b 0, b 1 * a₁ - a₃ * b 1, b 2 * a₂ - a₃ * b 2] (by
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    have h2 : (b 0 * a₀ - a₃ * b 0) • c₀ + (b 1 * a₁ - a₃ * b 1) • c₁ +
        (b 2 * a₂ - a₃ * b 2) • c₂ =
        (b 0 • a₀ • c₀ + b 1 • a₁ • c₁ + b 2 • a₂ • c₂) -
          a₃ • (b 0 • c₀ + b 1 • c₁ + b 2 • c₂) := by module
    rw [h2, h1, sub_self])
  have e0 : a₀ = a₃ := by
    have h : b 0 * (a₀ - a₃) = 0 := by rw [mul_sub, mul_comm (b 0) a₃]; exact hrel 0
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hb0)
  have e1 : a₁ = a₃ := by
    have h : b 1 * (a₁ - a₃) = 0 := by rw [mul_sub, mul_comm (b 1) a₃]; exact hrel 1
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hb1)
  have e2 : a₂ = a₃ := by
    have h : b 2 * (a₂ - a₃) = 0 := by rw [mul_sub, mul_comm (b 2) a₃]; exact hrel 2
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hb2)
  refine LinearMap.ext fun v => ?_
  obtain ⟨d, hd⟩ := hmem v
  rw [hd, map_add, map_add, map_smul, map_smul, map_smul, hy₀, hy₁, hy₂, e0, e1, e2,
    LinearMap.smul_apply, LinearMap.id_apply, smul_add, smul_add, smul_comm (d 0),
    smul_comm (d 1), smul_comm (d 2)]

end CFSG.Quasithin.D35Core
