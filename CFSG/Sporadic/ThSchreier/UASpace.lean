
module

public import CFSG.Sporadic.ThSchreier.UASpaceBase1

public import CFSG.Sporadic.ThSchreier.CentralizerData
public import CFSG.Sporadic.ThSchreier.Words
public meta import CFSG.Sporadic.ThSchreier.CentralizerData
public meta import CFSG.Sporadic.ThSchreier.Words
public import CFSG.Sporadic.ThSchreier.UASpaceInputs
public import Certificates.Certificate2325
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.Data
public meta import CFSG.Sporadic.Th.Chain
public import CFSG.Sporadic.Th.Chain
public meta import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.Sporadic.ThSchreier.AutCore
public meta import Certificates.Certificate10088Base
public import Certificates.Certificate10088Base
public import Certificates.Certificate10089Base
public meta import Certificates.Certificate10089Base
public import Certificates.Certificate10091Base
public meta import Certificates.Certificate10091Base

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

theorem a_smul_of_mem_planeUA {r : RowV} (hr : r ∈ planeUA) : a • r = r := by
  obtain ⟨s, rfl⟩ := hr
  rw [rowSmul_def, AllConj.a_inv]
  simp only [ofRow_toRow]
  rw [Matrix.vecMul_vecMul]
  have hA : toMat a * toMat a = 1 := by rw [← toMat_mul, AllConj.a_mul_self, toMat_one]
  have h2 : (toMat a - 1) * toMat a = toMat a - 1 := by
    rw [Matrix.sub_mul, hA, Matrix.one_mul]
    ext i j
    simp only [Matrix.sub_apply, zmod2_sub_eq_add]
    exact add_comm _ _
  rw [h2]

theorem a_smul_plane_of_subset {P : Set RowV} (hP : P ⊆ (planeUA : Set RowV)) : a • P = P := by
  ext r
  constructor
  · rintro ⟨s, hs, rfl⟩
    show a • s ∈ P
    rw [a_smul_of_mem_planeUA (hP hs)]
    exact hs
  · intro hr
    exact ⟨r, hr, a_smul_of_mem_planeUA (hP hr)⟩

end CFSG.Sporadic.ThSchreier
