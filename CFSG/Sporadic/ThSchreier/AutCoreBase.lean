
module

public import CFSG.Sporadic.ThSchreier.RigidityBase
public import CFSG.Milestones.AT_alternating_automorphism_permutation
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.DataBase
public import CFSG.Sporadic.ThSchreier.RigidityInputs
public meta import CFSG.Sporadic.ThSchreier.Enc8
public import CFSG.Permutation.AlternatingAutomorphism

@[expose] public section

namespace CFSG.Sporadic.ThSchreier.AutCore

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.ThSchreier CFSG.Certificates
open scoped commutatorElement

namespace Data

theorem matrix_ext {A B : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (h : ∀ v, A.mulVec v = B.mulVec v) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact h v)

open Matrix in
theorem bil_cInv (ℓ : Fin 8 → ZMod 2) (j : Fin 8) :
    ExtraspecialNF.bil c (cInv *ᵥ ℓ) (Pi.single j 1) = ℓ j := by
  have hb : ∀ v w : Fin 8 → ZMod 2, ExtraspecialNF.bil c v w = v ⬝ᵥ (Matrix.of c *ᵥ w) := by
    intro v w
    simp only [ExtraspecialNF.bil, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum,
      mul_assoc]
  have hT : (Matrix.of c)ᵀ = Matrix.of c := by
    ext i k
    exact c_symm i k
  rw [hb, dotProduct_comm, Matrix.dotProduct_mulVec, ← hT, Matrix.mulVec_transpose,
    Matrix.vecMul_vecMul, c_mul_cInv, Matrix.vecMul_one, single_one_dotProduct]

end Data

end CFSG.Sporadic.ThSchreier.AutCore
