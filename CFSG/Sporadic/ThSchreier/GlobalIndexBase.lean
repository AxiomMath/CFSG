
module

public import CFSG.Sporadic.ThSchreier.GlobalTransportBase
public import CFSG.Sporadic.ThSchreier.ScanCheck
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.ThSchreier.GlobalDataBase
public import CFSG.Sporadic.Th.SimpleBase
public meta import CFSG.Sporadic.ThSchreier.RowBase
public meta import CFSG.Sporadic.ThSchreier.LocalOrbitBase
public import CFSG.Sporadic.ThSchreier.RowInputs
public meta import Certificates.Data.CFSGNative.Th.Base

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.Sporadic.LySchreier
  Pointwise

noncomputable def colPlane (i : ℕ) : Set RowV := psiSet (planeAt i)

noncomputable def colImg (k i : ℕ) : ℕ := if k = 0 then αIdx i else βIdx i

theorem colImg_zero (i : ℕ) : colImg 0 i = αIdx i := if_pos rfl

theorem colImg_one (i : ℕ) : colImg 1 i = βIdx i := if_neg one_ne_zero

noncomputable def colLab (j : ℕ) : ℕ := labIdx j - 1

section Facts

variable (hF : OrbitFacts) (hS : ThScanFacts)
include hF

include hS

end Facts

end CFSG.Sporadic.ThSchreier
