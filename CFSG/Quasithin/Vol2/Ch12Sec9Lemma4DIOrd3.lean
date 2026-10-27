module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIFacts

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin

@[expose] def omegaE : (Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
  LinearEquiv.ofLinear (Matrix.toLin' !![0, 1; 1, 1]) (Matrix.toLin' !![1, 1; 1, 0])
    (by
      rw [← Matrix.toLin'_mul, show (!![0, 1; 1, 1] * !![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 2))
        = 1 by decide, Matrix.toLin'_one])
    (by
      rw [← Matrix.toLin'_mul, show (!![1, 1; 1, 0] * !![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) (ZMod 2))
        = 1 by decide, Matrix.toLin'_one])

theorem omegaE_apply (x : Fin 2 → ZMod 2) : omegaE x = ![x 1, x 0 + x 1] := by
  funext i
  fin_cases i <;> simp [omegaE, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem omegaE_cube (x : Fin 2 → ZMod 2) : omegaE (omegaE (omegaE x)) = x := by
  have hx : x = ![x 0, x 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hx, omegaE_apply, omegaE_apply, omegaE_apply]
  generalize x 0 = a
  generalize x 1 = b
  revert a b
  decide

theorem omegaE_ne_one : omegaE ≠ LinearEquiv.refl (ZMod 2) (Fin 2 → ZMod 2) := by
  intro h
  have h1 := LinearEquiv.congr_fun h ![1, 0]
  rw [omegaE_apply] at h1
  have h2 : (![(![1, 0] : Fin 2 → ZMod 2) 1, (![1, 0] : Fin 2 → ZMod 2) 0 +
      (![1, 0] : Fin 2 → ZMod 2) 1] : Fin 2 → ZMod 2) = ![1, 0] := h1
  have h3 := congrFun h2 0
  simp at h3

theorem exists_order_three_fix {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
    [Module.Finite (ZMod 2) M] (hM : Module.finrank (ZMod 2) M = 4)
    (ℓ : Submodule (ZMod 2) M) (hℓ : Module.finrank (ZMod 2) ℓ = 2) :
    ∃ γ : M ≃ₗ[ZMod 2] M, γ ^ 3 = 1 ∧ γ ≠ 1 ∧ ∀ v ∈ ℓ, γ v = v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl ℓ
  have hWr : Module.finrank (ZMod 2) W = 2 := by
    have := Submodule.finrank_add_eq_of_isCompl hW
    omega
  let b := Module.finBasisOfFinrankEq (ZMod 2) W hWr
  let γW : W ≃ₗ[ZMod 2] W := b.equivFun.trans (omegaE.trans b.equivFun.symm)
  let Φ : (ℓ × W) ≃ₗ[ZMod 2] M := Submodule.prodEquivOfIsCompl ℓ W hW
  let γ : M ≃ₗ[ZMod 2] M :=
    Φ.symm.trans ((LinearEquiv.prodCongr (LinearEquiv.refl (ZMod 2) ℓ) γW).trans Φ)
  have hγW : ∀ w : W, γW w = b.equivFun.symm (omegaE (b.equivFun w)) := by
    intro w
    rfl
  have hγW3 : ∀ w : W, γW (γW (γW w)) = w := by
    intro w
    apply b.equivFun.injective
    rw [hγW, hγW, hγW]
    simp only [LinearEquiv.apply_symm_apply]
    exact omegaE_cube _
  have hγΦ : ∀ (a : ℓ) (c : W), γ (Φ (a, c)) = Φ (a, γW c) := by
    intro a c
    show Φ (LinearEquiv.prodCongr (LinearEquiv.refl (ZMod 2) ℓ) γW (Φ.symm (Φ (a, c)))) =
      Φ (a, γW c)
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have hγ3 : ∀ x : M, γ (γ (γ x)) = x := by
    intro x
    obtain ⟨⟨a, c⟩, rfl⟩ := Φ.surjective x
    rw [hγΦ, hγΦ, hγΦ, hγW3 c]
  refine ⟨γ, ?_, ?_, ?_⟩
  · apply LinearEquiv.ext
    intro x
    rw [pow_three]
    exact hγ3 x
  · intro h
    set w₀ : W := b.equivFun.symm ![1, 0] with hw₀
    have key : γ (Φ (0, w₀)) = Φ (0, w₀) := by
      rw [h]
      rfl
    rw [hγΦ] at key
    have hfix : γW w₀ = w₀ := (Prod.mk.inj (Φ.injective key)).2
    have h2 : omegaE ![1, 0] = ![1, 0] := by
      have := congrArg b.equivFun hfix
      rw [hγW, hw₀, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
      exact this
    rw [omegaE_apply] at h2
    have h3 := congrFun h2 0
    simp at h3
  · intro v hv
    have hΦv : Φ (⟨v, hv⟩, 0) = v := by
      show v + 0 = v
      rw [add_zero]
    have h1 := hγΦ ⟨v, hv⟩ 0
    rw [map_zero, hΦv] at h1
    exact h1

end CFSG.Quasithin.H13.C1294
