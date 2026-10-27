module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace S153EO61

theorem finite_check : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), Aᵀ = A →
    (∀ v : Fin 3 → ZMod 2, (∀ w : Fin 3 → ZMod 2, v ⬝ᵥ (A *ᵥ w) = 0) → v = 0) →
    ∃ γ : Matrix (Fin 3) (Fin 3) (ZMod 2), γ * γ * γ = 1 ∧ γ ≠ 1 ∧
      ∀ ξ η : Fin 3 → ZMod 2, ((γ * γ) *ᵥ ξ) ⬝ᵥ (A *ᵥ η) = ξ ⬝ᵥ (A *ᵥ (γ *ᵥ η)) := by
  decide +kernel

theorem biadd_eq_dot (β : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → ZMod 2)
    (h₁ : ∀ x x' y, β (x + x') y = β x y + β x' y) (h₂ : ∀ x y y', β x (y + y') = β x y + β x y')
    (x y : Fin 3 → ZMod 2) :
    β x y = x ⬝ᵥ ((Matrix.of fun i j => β (Pi.single i 1) (Pi.single j 1)) *ᵥ y) := by
  classical
  have hs : ∀ i : Fin 3, (Pi.single i (1 : ZMod 2) : Fin 3 → ZMod 2) =
      fun j => if i = j then 1 else 0 := by
    intro i
    funext j
    simp [Pi.single_apply, eq_comm]
  have e1 : ∀ y, β x y = ∑ i, x i * β (Pi.single i 1) y := by
    intro y
    let L : (Fin 3 → ZMod 2) →+ ZMod 2 := AddMonoidHom.mk' (fun v => β v y) (fun a b => h₁ a b y)
    have h := LinearMap.pi_apply_eq_sum_univ (L.toZModLinearMap 2) x
    simp only [smul_eq_mul] at h
    simp only [← hs] at h
    exact h
  have e2 : ∀ i, β (Pi.single i 1) y = ∑ j, y j * β (Pi.single i 1) (Pi.single j 1) := by
    intro i
    let L : (Fin 3 → ZMod 2) →+ ZMod 2 :=
      AddMonoidHom.mk' (fun v => β (Pi.single i 1) v) (fun a b => h₂ _ a b)
    have h := LinearMap.pi_apply_eq_sum_univ (L.toZModLinearMap 2) y
    simp only [smul_eq_mul] at h
    simp only [← hs] at h
    exact h
  rw [e1 y]
  simp only [e2, dotProduct, Matrix.mulVec, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end S153EO61

end CFSG.Quasithin
