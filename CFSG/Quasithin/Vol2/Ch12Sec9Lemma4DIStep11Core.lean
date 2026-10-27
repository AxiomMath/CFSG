module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.H13.C1294

private theorem matrix_order_three_fact :
    ∀ A B : Matrix (Fin 2) (Fin 2) (ZMod 2), A ^ 3 = 1 → B ^ 3 = 1 → B ≠ 1 →
      A = 1 ∨ A = B ∨ A = B * B := by
  decide

theorem eq_one_or_eq_of_order_three {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    (hM : Module.finrank (ZMod 2) M = 2) (σ τ : M ≃ₗ[ZMod 2] M)
    (hσ : σ ^ 3 = 1) (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    σ = 1 ∨ σ = τ ∨ σ = τ * τ := by
  have hpos : 0 < Module.finrank (ZMod 2) M := by rw [hM]; norm_num
  haveI : Module.Finite (ZMod 2) M := Module.finite_of_finrank_pos hpos
  haveI : Module.Free (ZMod 2) M := Module.Free.of_divisionRing (ZMod 2) M
  let b : Module.Basis (Fin 2) (ZMod 2) M := Module.finBasisOfFinrankEq (ZMod 2) M hM
  let Φ : (M →ₗ[ZMod 2] M) →* Matrix (Fin 2) (Fin 2) (ZMod 2) :=
    { toFun := LinearMap.toMatrix b b
      map_one' := LinearMap.toMatrix_one b
      map_mul' := LinearMap.toMatrix_mul b }
  let ψ : (M ≃ₗ[ZMod 2] M) →* Matrix (Fin 2) (Fin 2) (ZMod 2) :=
    Φ.comp LinearEquiv.automorphismGroup.toLinearMapMonoidHom
  have hinj : Function.Injective ψ := by
    intro e f h
    have h' : LinearMap.toMatrix b b (e : M →ₗ[ZMod 2] M) =
        LinearMap.toMatrix b b (f : M →ₗ[ZMod 2] M) := h
    have h'' : (e : M →ₗ[ZMod 2] M) = (f : M →ₗ[ZMod 2] M) :=
      (LinearMap.toMatrix b b).injective h'
    apply LinearEquiv.ext
    intro x
    exact LinearMap.congr_fun h'' x
  have hmat := matrix_order_three_fact (ψ σ) (ψ τ)
    (by rw [← map_pow ψ σ 3, hσ, map_one])
    (by rw [← map_pow ψ τ 3, hτ, map_one])
    (fun h => hτ1 (hinj (h.trans (map_one ψ).symm)))
  rcases hmat with h | h | h
  · exact Or.inl (hinj (h.trans (map_one ψ).symm))
  · exact Or.inr (Or.inl (hinj h))
  · exact Or.inr (Or.inr (hinj (h.trans (map_mul ψ τ τ).symm)))

end CFSG.Quasithin.H13.C1294
