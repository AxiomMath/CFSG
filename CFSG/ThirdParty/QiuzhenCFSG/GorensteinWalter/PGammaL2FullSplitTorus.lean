module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The full standard split torus in `PGL₂`

This module provides the injective diagonal parametrization by `Kˣ` and its
compatibility with coefficient automorphisms.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-- The diagonal general-linear parametrization underlying the full split
torus. -/
@[expose] public def pGammaL2FullSplitTorusGL
    (K : Type u) [Field K] : Kˣ →* GL (Fin 2) K :=
  { toFun := fun a => Matrix.GeneralLinearGroup.mkOfDetNeZero
      (Matrix.diagonal ![(a : K), 1]) (by
        simp [Matrix.det_diagonal, Fin.prod_univ_two, a.ne_zero])
    map_one' := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp
    map_mul' := by
      intro a b
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] }

/-- The full standard split torus of `PGL₂(K)`, parametrized injectively by
`Kˣ`. -/
@[expose] public def pGammaL2FullSplitTorus
    (K : Type u) [Field K] : Kˣ →* PGL2 K :=
  Matrix.ProjGenLinGroup.mk.comp (pGammaL2FullSplitTorusGL K)

/-- The full split-torus parametrization by `Kˣ` is injective. -/
public theorem pGammaL2FullSplitTorus_injective
    (K : Type u) [Field K] :
    Function.Injective (pGammaL2FullSplitTorus K) := by
  intro a b hab
  change Matrix.ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL K a) =
    Matrix.ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL K b) at hab
  rcases Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hab with ⟨r, hr⟩
  have h11 := congrArg (fun A : GL (Fin 2) K =>
    ((A : Matrix (Fin 2) (Fin 2) K) 1 1)) hr
  have h00 := congrArg (fun A : GL (Fin 2) K =>
    ((A : Matrix (Fin 2) (Fin 2) K) 0 0)) hr
  have hr1 : (r : K) = 1 := by
    simpa [pGammaL2FullSplitTorusGL, Matrix.GeneralLinearGroup.scalar,
      Matrix.mul_apply, Fin.sum_univ_two] using h11
  apply Units.ext
  simpa [pGammaL2FullSplitTorusGL, Matrix.GeneralLinearGroup.scalar,
    Matrix.mul_apply, Fin.sum_univ_two, hr1] using h00

/-- Coefficient automorphisms act on the split torus through their natural
action on the parameter. -/
public theorem pGammaL2FullSplitTorus_map_field
    (K : Type u) [Field K] (sigma : K ≃+* K) (a : Kˣ) :
    pgl2FieldAut K sigma (pGammaL2FullSplitTorus K a) =
      pGammaL2FullSplitTorus K (Units.map sigma.toRingHom a) := by
  change pgl2RingEquiv sigma
      (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) K))
        (pGammaL2FullSplitTorusGL K a)) =
    QuotientGroup.mk' (Subgroup.center (GL (Fin 2) K))
      (pGammaL2FullSplitTorusGL K (Units.map sigma.toRingHom a))
  rw [pgl2RingEquiv_mk]
  change QuotientGroup.mk' (Subgroup.center (GL (Fin 2) K))
      (Matrix.GeneralLinearGroup.map sigma.toRingHom
        (pGammaL2FullSplitTorusGL K a)) = _
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [pGammaL2FullSplitTorusGL, Matrix.GeneralLinearGroup.map]

/-- Projective commutation with a pure coefficient automorphism fixes the
split-torus parameter itself. -/
public theorem pGammaL2FullSplitTorus_fixed
    (K : Type u) [Field K] (sigma : K ≃+* K) (a : Kˣ)
    (hcomm : Commute
      (SemidirectProduct.inr sigma : PGammaL2 K)
      (SemidirectProduct.inl (pGammaL2FullSplitTorus K a))) :
    Units.map sigma.toRingHom a = a := by
  have hmul := hcomm.eq
  rw [SemidirectProduct.mul_def, SemidirectProduct.mul_def] at hmul
  have hproj :
      pgl2FieldAut K sigma (pGammaL2FullSplitTorus K a) =
        pGammaL2FullSplitTorus K a := by
    simpa using congrArg SemidirectProduct.left hmul
  rw [pGammaL2FullSplitTorus_map_field] at hproj
  exact pGammaL2FullSplitTorus_injective K hproj

end CFSG.GorensteinWalter
