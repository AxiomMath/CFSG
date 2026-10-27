module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

open Equiv

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7Inner

@[expose] def transportAut {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    MulAut X →* MulAut Y where
  toFun τ := e.symm.trans (τ.trans e)
  map_one' := by
    ext y
    simp
  map_mul' τ ρ := by
    ext y
    simp

theorem transportAut_apply {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (τ : MulAut X)
    (y : Y) : transportAut e τ y = e (τ (e.symm y)) := rfl

theorem inner_of_pow_three {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 7))
    (τ : MulAut X) (k : ℕ) (hτ : τ ^ 3 ^ k = 1) :
    ∃ x : X, ∀ y : X, τ y = x * y * x⁻¹ := by
  have hφ : transportAut e τ ^ 3 ^ k = 1 := by
    rw [← map_pow, hτ, map_one]
  obtain ⟨σ, hσ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
      (by norm_num) (by norm_num)).2 (transportAut e τ)
  have hσpow : σ ^ 3 ^ k = 1 := by
    apply CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 7 (by norm_num)
    simp only [map_pow, hσ, hφ, map_one]
  have hsign : Equiv.Perm.sign σ = 1 := by
    have h1 : (Equiv.Perm.sign σ) ^ 3 ^ k = 1 := by
      rw [← map_pow, hσpow, map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · exact h
    · exfalso
      rw [h, Odd.neg_one_pow (Odd.pow (by decide))] at h1
      exact absurd h1 (by decide)
  have hmem : σ ∈ alternatingGroup (Fin 7) := Equiv.Perm.mem_alternatingGroup.mpr hsign
  refine ⟨e.symm ⟨σ, hmem⟩, fun y => ?_⟩
  have key : ∀ z : alternatingGroup (Fin 7),
      (MulAut.conjNormal σ) z = ⟨σ, hmem⟩ * z * ⟨σ, hmem⟩⁻¹ := by
    intro z
    apply Subtype.ext
    rfl
  apply e.injective
  rw [map_mul, map_mul, map_inv, e.apply_symm_apply]
  calc e (τ y) = transportAut e τ (e y) := by rw [transportAut_apply, e.symm_apply_apply]
    _ = MulAut.conjNormal σ (e y) := by rw [hσ]
    _ = ⟨σ, hmem⟩ * e y * ⟨σ, hmem⟩⁻¹ := key _

theorem inner_of_isAlt7_pow_three {X : Type} [Group X]
    (hX : Nonempty (X ≃* alternatingGroup (Fin 7)))
    (τ : MulAut X) (k : ℕ) (hτ : τ ^ 3 ^ k = 1) :
    ∃ x : X, ∀ y : X, τ y = x * y * x⁻¹ := by
  obtain ⟨e⟩ := hX
  exact inner_of_pow_three e τ k hτ

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7Inner

end
