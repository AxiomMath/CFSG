module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveRootRankU3
import CFSG.LocalAnalysis.WeakClosure81.SU3RankConj
import CFSG.LocalAnalysis.WeakClosure81.SU3RankKer
import CFSG.LocalAnalysis.WeakClosure81.SU3RankGeneric
import CFSG.LocalAnalysis.WeakClosure81.SU3RankEightCase
public import CFSG.LocalAnalysis.WeakClosure81.SU3RankDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.SignalizerFunctorTheorem.Quadratic

private theorem modCommRank_conj {F : Type} [AddCommGroup F] [Module (ZMod 2) F]
    (a t : LGL 2 F) : modCommRank (a * t * a⁻¹) = modCommRank t := by
  unfold modCommRank
  have hcomp : ((a * t * a⁻¹ : LGL 2 F) : F →ₗ[ZMod 2] F) - LinearMap.id =
      (a : F →ₗ[ZMod 2] F).comp
        (((t : F →ₗ[ZMod 2] F) - LinearMap.id).comp
          ((a⁻¹ : LGL 2 F) : F →ₗ[ZMod 2] F)) := by
    ext x
    simp
  rw [hcomp, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range,
    Submodule.map_top]
  exact LinearEquiv.finrank_map_eq a _

theorem su3IrreducibleRank_holds : SU3IrreducibleRank := by
  unfold SU3IrreducibleRank
  intro n F₀ _ _ hn hcard F _ _ _ σ _ g hg hσg
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F₀ 2 :=
    CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hcard
  have hσne : σ ≠ 1 := fun h => hσg (by rw [h, MonoidHom.one_apply])
  have hker : ∀ x, σ x = 1 → (x : GL (Fin 3) F₀) ∈ StatedScalars (Fin 3) F₀ :=
    fun x hx => mem_statedScalars_of_map_eq_one hn hcard σ hσne hx
  obtain ⟨m, hm⟩ := exists_mul_mul_inv_eq_permSU_swap hcard g hg
  have hconj : modCommRank (σ g) =
      modCommRank (σ (permSU n F₀ (Equiv.swap 0 1))) := by
    have h1 : σ g = (σ m)⁻¹ * σ (permSU n F₀ (Equiv.swap 0 1)) * σ m := by
      have h := congrArg σ hm
      simp only [map_mul, map_inv] at h
      rw [← h]
      group
    rw [h1]
    simpa using modCommRank_conj (a := (σ m)⁻¹)
      (t := σ (permSU n F₀ (Equiv.swap 0 1)))
  by_cases hn3 : n = 3
  · subst n
    have h6 := six_le_modCommRank_permSU_swap hcard σ hker
    rw [hconj]
    omega
  · have h2 := two_mul_le_modCommRank_permSU_swap_of_ne_three hn hn3 hcard σ hker
    rw [hconj]
    exact h2

end CFSG.LocalAnalysis.WeakClosure81

end
