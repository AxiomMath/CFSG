module

public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.Assembly.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Symplectic
open scoped Matrix

variable {m : ℕ} {K : Type} [Field K]

theorem finrank_range_spEquiv_sub_one (g : StatedSp m K) :
    Module.finrank K (LinearMap.range
      (((spEquiv g : LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)) :
        (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K)) - 1)) =
      Matrix.rank (((g : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1) := by
  have h : (((spEquiv g : LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)) :
        (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K)) - 1) =
      Matrix.mulVecLin (((g : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1) := by
    refine LinearMap.ext fun v => ?_
    have h1 := spEquiv_app g v
    simp only [LinearMap.sub_apply, Module.End.one_apply, Matrix.mulVecLin_apply,
      Matrix.sub_mulVec, Matrix.one_mulVec]
    exact congrArg (· - v) h1
  rw [h]
  rfl

theorem spForm_spEquiv_sub_one_apply (g : StatedSp m K) (v : Fin m ⊕ Fin m → K) :
    spForm m K v ((((spEquiv g : LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)) :
        (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K)) - 1) v) =
      spForm m K v ((((g : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1) *ᵥ v) := by
  have h1 := spEquiv_app g v
  simp only [LinearMap.sub_apply, Module.End.one_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
  exact congrArg (fun w => spForm m K v (w - v)) h1

end CFSG.RankThree.GF2n.Stroth80
