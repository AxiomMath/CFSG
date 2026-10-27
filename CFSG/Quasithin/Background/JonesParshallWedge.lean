module

public import CFSG.Quasithin.Background.JonesParshallBasic

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix

@[expose] def pr5 : Fin 10 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

section Minors

variable {K : Type*} [Field K]

@[expose] def minorAlt (i j : Fin 5) : (Fin 5 → K) [⋀^Fin 2]→ₗ[K] K :=
  (Matrix.detRowAlternating : (Fin 2 → K) [⋀^Fin 2]→ₗ[K] K).compLinearMap
    (LinearMap.pi ![LinearMap.proj i, LinearMap.proj j])

theorem minorAlt_apply (i j : Fin 5) (v : Fin 2 → Fin 5 → K) :
    minorAlt i j v = v 0 i * v 1 j - v 0 j * v 1 i := by
  change Matrix.det (Matrix.of fun a => (LinearMap.pi ![LinearMap.proj i, LinearMap.proj j] :
    (Fin 5 → K) →ₗ[K] (Fin 2 → K)) (v a)) = _
  rw [det_fin_two]
  simp

@[expose] def wedgeCoord : ⋀[K]^2 (Fin 5 → K) →ₗ[K] (Fin 10 → K) :=
  LinearMap.pi fun k => exteriorPower.alternatingMapLinearEquiv (minorAlt (pr5 k).1 (pr5 k).2)

theorem wedgeCoord_ιMulti (v : Fin 2 → Fin 5 → K) (k : Fin 10) :
    wedgeCoord (exteriorPower.ιMulti K 2 v) k =
      v 0 (pr5 k).1 * v 1 (pr5 k).2 - v 0 (pr5 k).2 * v 1 (pr5 k).1 := by
  rw [wedgeCoord, LinearMap.pi_apply, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    minorAlt_apply]

@[expose] def wedgeMat (g : Matrix (Fin 5) (Fin 5) K) : Matrix (Fin 10) (Fin 10) K :=
  Matrix.of fun k l => g (pr5 k).1 (pr5 l).1 * g (pr5 k).2 (pr5 l).2 -
    g (pr5 k).1 (pr5 l).2 * g (pr5 k).2 (pr5 l).1

theorem wedgeCoord_map (g : Matrix (Fin 5) (Fin 5) K) (x : ⋀[K]^2 (Fin 5 → K)) :
    wedgeCoord (exteriorPower.map 2 (Matrix.toLin' g) x) = wedgeMat g *ᵥ wedgeCoord x := by
  have h : wedgeCoord ∘ₗ exteriorPower.map 2 (Matrix.toLin' g) =
      (wedgeMat g).mulVecLin ∘ₗ wedgeCoord := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v => ?_)
    funext k
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, Matrix.mulVecLin_apply]
    rw [wedgeCoord_ιMulti]
    simp only [mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, wedgeCoord_ιMulti,
      Function.comp_apply, Matrix.toLin'_apply]
    fin_cases k <;> simp [wedgeMat, pr5] <;> ring
  exact LinearMap.congr_fun h x

@[expose] def wedgeBasis (k : Fin 10) : ⋀[K]^2 (Fin 5 → K) :=
  exteriorPower.ιMulti K 2 ![Pi.single (pr5 k).1 1, Pi.single (pr5 k).2 1]

theorem wedgeCoord_basis (k : Fin 10) :
    wedgeCoord (wedgeBasis k : ⋀[K]^2 (Fin 5 → K)) = Pi.single k 1 := by
  funext l
  rw [wedgeBasis, wedgeCoord_ιMulti]
  fin_cases k <;> fin_cases l <;> simp [pr5]

theorem wedgeCoord_surjective : Function.Surjective (wedgeCoord (K := K)) := by
  intro c
  refine ⟨∑ k, c k • wedgeBasis k, ?_⟩
  rw [map_sum]
  simp only [map_smul, wedgeCoord_basis]
  funext l
  simp [Finset.sum_apply, Pi.single_apply]

theorem finrank_wedge : Module.finrank K (⋀[K]^2 (Fin 5 → K)) = 10 := by
  rw [exteriorPower.finrank_eq, Module.finrank_fin_fun]
  rfl

theorem wedgeCoord_bijective : Function.Bijective (wedgeCoord (K := K)) := by
  have h : Module.finrank K (⋀[K]^2 (Fin 5 → K)) = Module.finrank K (Fin 10 → K) := by
    rw [finrank_wedge, Module.finrank_fin_fun]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank h).mpr wedgeCoord_surjective,
    wedgeCoord_surjective⟩

variable (K) in
@[expose] def wedgeEquiv : ⋀[K]^2 (Fin 5 → K) ≃ₗ[K] (Fin 10 → K) :=
  LinearEquiv.ofBijective wedgeCoord wedgeCoord_bijective

theorem wedgeEquiv_apply (x : ⋀[K]^2 (Fin 5 → K)) : wedgeEquiv K x = wedgeCoord x :=
  rfl

end Minors

end CFSG.Quasithin.JonesParshall
