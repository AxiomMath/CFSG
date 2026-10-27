module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Quasithin

namespace SBc16

abbrev GL25 : Type := GL (Fin 2) (ZMod 5)

@[expose] def IsFive (x : GL25) : Prop := x ^ 5 = 1 ∧ x ≠ 1

theorem isFive_of_orderOf_eq_five {x : GL25} (hx : orderOf x = 5) : IsFive x := by
  refine ⟨?_, ?_⟩
  · have := pow_orderOf_eq_one x
    rwa [hx] at this
  · intro h
    rw [h, orderOf_one] at hx
    omega

theorem card_GL25 : Nat.card GL25 = 480 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := Matrix.card_GL_field (𝔽 := ZMod 5) 2
  simp only [Fin.prod_univ_two, ZMod.card, Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
  rw [h]
  norm_num

theorem ncard_isFive_le : {x : GL25 | IsFive x}.ncard ≤ 24 := by
  have hinj : Function.Injective (Units.val : GL25 → Matrix (Fin 2) (Fin 2) (ZMod 5)) :=
    Units.val_injective
  have hsub : (Units.val '' {x : GL25 | IsFive x}) ⊆
      ↑(Finset.univ.filter (fun M : Matrix (Fin 2) (Fin 2) (ZMod 5) => M ^ 5 = 1 ∧ M ≠ 1)) := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    refine ⟨?_, ?_⟩
    · have := congrArg Units.val hx.1
      simpa using this
    · intro h
      exact hx.2 (Units.ext h)
  calc {x : GL25 | IsFive x}.ncard = (Units.val '' {x : GL25 | IsFive x}).ncard :=
        (Set.ncard_image_of_injective _ hinj).symm
    _ ≤ (↑(Finset.univ.filter (fun M : Matrix (Fin 2) (Fin 2) (ZMod 5) => M ^ 5 = 1 ∧ M ≠ 1)) :
          Set (Matrix (Fin 2) (Fin 2) (ZMod 5))).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (Finset.univ.filter (fun M : Matrix (Fin 2) (Fin 2) (ZMod 5) =>
          M ^ 5 = 1 ∧ M ≠ 1)).card := Set.ncard_coe_finset _
    _ = 24 := by decide +kernel

theorem core_decide : ∀ (a b c d : ZMod 5),
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) (ZMod 5)) ^ 5 = 1 →
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) (ZMod 5)) ≠ 1 → ∀ c' d' : ZMod 5, c' ≠ 0 → d' ≠ 0 →
    ¬ ((∃ k : Fin 5, (!![-1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod 5)) * !![a, b; c, d] =
        (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) (ZMod 5)) ^ (k : ℕ) * !![-1, 0; 0, 1]) ∧
      (∃ k : Fin 5, (!![0, c'; d', 0] : Matrix (Fin 2) (Fin 2) (ZMod 5)) * !![a, b; c, d] =
        (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) (ZMod 5)) ^ (k : ℕ) * !![0, c'; d', 0])) := by
  decide +kernel

theorem not_both_normalize {σ τ : GL25}
    (hσ00 : (σ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 = -1)
    (hσ01 : (σ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 = 0)
    (hσ10 : (σ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 = 0)
    (hσ11 : (σ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 = 1)
    (hτ00 : (τ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 = 0)
    (hτ11 : (τ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 = 0)
    (hτ01 : (τ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 ≠ 0)
    (hτ10 : (τ : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 ≠ 0)
    {u : GL25} (hu : IsFive u) :
    ¬ ((∃ k : ℕ, k < 5 ∧ σ * u = u ^ k * σ) ∧ (∃ k : ℕ, k < 5 ∧ τ * u = u ^ k * τ)) := by
  rintro ⟨⟨k₁, hk₁, h₁⟩, ⟨k₂, hk₂, h₂⟩⟩
  have hσM : (σ : Matrix (Fin 2) (Fin 2) (ZMod 5)) = !![-1, 0; 0, 1] := by
    have h := Matrix.eta_fin_two (σ : Matrix (Fin 2) (Fin 2) (ZMod 5))
    rwa [hσ00, hσ01, hσ10, hσ11] at h
  have hτM : (τ : Matrix (Fin 2) (Fin 2) (ZMod 5)) = !![0, τ 0 1; τ 1 0, 0] := by
    have h := Matrix.eta_fin_two (τ : Matrix (Fin 2) (Fin 2) (ZMod 5))
    rwa [hτ00, hτ11] at h
  have hM : (u : Matrix (Fin 2) (Fin 2) (ZMod 5)) = !![u 0 0, u 0 1; u 1 0, u 1 1] :=
    Matrix.eta_fin_two _
  have hu5 : (u : Matrix (Fin 2) (Fin 2) (ZMod 5)) ^ 5 = 1 := by
    have := congrArg Units.val hu.1
    simpa using this
  have hu1 : (u : Matrix (Fin 2) (Fin 2) (ZMod 5)) ≠ 1 := fun h => hu.2 (Units.ext h)
  rw [hM] at hu5 hu1
  refine core_decide _ _ _ _ hu5 hu1 _ _ hτ01 hτ10 ⟨⟨⟨k₁, hk₁⟩, ?_⟩, ⟨⟨k₂, hk₂⟩, ?_⟩⟩
  · have := congrArg Units.val h₁
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at this
    rw [hσM, hM] at this
    exact this
  · have := congrArg Units.val h₂
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at this
    rw [hτM, hM] at this
    exact this

end SBc16

end CFSG.Quasithin
