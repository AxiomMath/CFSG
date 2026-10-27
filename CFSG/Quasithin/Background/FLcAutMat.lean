module

public import CFSG.Quasithin.Background.FLcFlag
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.Quasithin.FLc

open Matrix Module

theorem card_multiplicative_Vt (n : ℕ) : Nat.card (Multiplicative (Vt n)) = 2 ^ n := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Vt n) ≃ Vt n), Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_eq_of_bijective {G : Type} [Group G] {U : Subgroup G} {n : ℕ}
    {β : ↥U →* Multiplicative (Vt n)} (hi : Function.Injective β) (hs : Function.Surjective β) :
    Nat.card ↥U = 2 ^ n := by
  rw [Nat.card_congr (Equiv.ofBijective β ⟨hi, hs⟩), card_multiplicative_Vt]

theorem zmod_two_eq_one_of_mul_eq_one {x y : ZMod 2} (h : x * y = 1) : x = 1 := by
  revert x y
  decide

theorem exists_mat_of_mulEquiv {n : ℕ} (φ : Multiplicative (Vt n) ≃* Multiplicative (Vt n)) :
    ∃ g : SLt n, ∀ v : Vt n, Multiplicative.toAdd (φ (Multiplicative.ofAdd v)) = mat g *ᵥ v := by
  let f : Vt n →+ Vt n :=
    { toFun := fun v => Multiplicative.toAdd (φ (Multiplicative.ofAdd v))
      map_zero' := by
        have := map_one φ
        exact this
      map_add' := fun a b => by
        have := map_mul φ (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
        exact this }
  let f' : Vt n →+ Vt n :=
    { toFun := fun v => Multiplicative.toAdd (φ.symm (Multiplicative.ofAdd v))
      map_zero' := by
        have := map_one φ.symm
        exact this
      map_add' := fun a b => by
        have := map_mul φ.symm (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
        exact this }
  let ψ : Vt n →ₗ[ZMod 2] Vt n := f.toZModLinearMap 2
  let ψ' : Vt n →ₗ[ZMod 2] Vt n := f'.toZModLinearMap 2
  have hψ : ∀ v, ψ v = Multiplicative.toAdd (φ (Multiplicative.ofAdd v)) := fun v => rfl
  have hψ' : ∀ v, ψ' v = Multiplicative.toAdd (φ.symm (Multiplicative.ofAdd v)) := fun v => rfl
  have hcomp : ψ ∘ₗ ψ' = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hψ, hψ']
    rw [ofAdd_toAdd, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have hMM : LinearMap.toMatrix' ψ * LinearMap.toMatrix' ψ' = 1 := by
    rw [← LinearMap.toMatrix'_comp, hcomp, LinearMap.toMatrix'_id]
  have hdet : (LinearMap.toMatrix' ψ).det = 1 := by
    have := congrArg Matrix.det hMM
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact zmod_two_eq_one_of_mul_eq_one this
  refine ⟨⟨LinearMap.toMatrix' ψ, hdet⟩, fun v => ?_⟩
  change Multiplicative.toAdd (φ (Multiplicative.ofAdd v)) = (LinearMap.toMatrix' ψ) *ᵥ v
  rw [LinearMap.toMatrix'_mulVec]
  rfl

end CFSG.Quasithin.FLc
