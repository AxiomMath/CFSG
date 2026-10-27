
module

public import CFSG.Sporadic.ThSchreier.NoTransvectionBase
public import CFSG.Sporadic.ThSchreier.Max3AutBase
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.CoreBase
public import CFSG.Sporadic.Th.Max3.AltNine
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Sporadic.Th.Max3.QuotientInputsBase
public import CFSG.Sporadic.Th.Max3.DataBase
public import CFSG.Sporadic.ThSchreier.NoTransvectionInputs
public meta import CFSG.Sporadic.ThSchreier.RigidityBase
public import CFSG.Sporadic.ThSchreier.NoTransvection

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Certificates Matrix

theorem c_diag : ∀ i, c i i = 0 := by decide

theorem bil_eq_dot (v w : Fin 8 → ZMod 2) :
    ExtraspecialNF.bil c v w = (Matrix.of c *ᵥ w) ⬝ᵥ v := by
  rw [dotProduct_comm]
  simp only [ExtraspecialNF.bil, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum,
    mul_assoc]

theorem bil_eq_dot' (v w : Fin 8 → ZMod 2) :
    ExtraspecialNF.bil c v w = (Matrix.of c *ᵥ v) ⬝ᵥ w := by
  have hT : (Matrix.of c)ᵀ = Matrix.of c := by
    ext i k
    exact c_symm i k
  rw [bil_eq_dot, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT]

theorem c_mulVec_injective : Function.Injective (Matrix.of c *ᵥ ·) := by
  intro u w h
  have hinv : cInv * Matrix.of c = 1 := mul_eq_one_comm.1 c_mul_cInv
  have e := congrArg (cInv *ᵥ ·) h
  simp only [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at e
  exact e

end CFSG.Sporadic.ThSchreier
