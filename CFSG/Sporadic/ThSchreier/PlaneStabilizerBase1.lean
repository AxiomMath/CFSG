
module

public import CFSG.Sporadic.ThSchreier.PlaneStabilizerBase

public import CFSG.Sporadic.ThSchreier.OrbitCheck819Base
public import CFSG.Sporadic.ThSchreier.PlaneFactsBase1
public meta import CFSG.Sporadic.ThSchreier.TransporterBase
public meta import CFSG.Sporadic.ThSchreier.UASpaceBase1
public import CFSG.Sporadic.ThSchreier.TransporterBase
public import CFSG.Sporadic.ThSchreier.UASpaceBase1
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.Th.SimpleBase1
public meta import CFSG.Sporadic.ThSchreier.Row
public meta import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public import CFSG.Sporadic.ThSchreier.LocalOrbitInputs
public meta import CFSG.Sporadic.ThSchreier.WordsBase1
public meta import CFSG.Sporadic.ThSchreier.LocalData
public import CFSG.Sporadic.ThSchreier.OrbitCheck819Inputs
public import CFSG.Sporadic.ThSchreier.RowInputs
public meta import Certificates.Data.CFSGNative.Th.Base
public import CFSG.Sporadic.ThSchreier.UASpaceInputs
public meta import CFSG.Sporadic.ThSchreier.CentralizerData
public import CFSG.Sporadic.Th.Plane
public import CFSG.Sporadic.Th.FormBase
public import Certificates.Data.CFSGNative.Th.Base
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.Data

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

@[expose] noncomputable def labGenH (l : ℕ) : J := if l = 1 then localX else localY

@[expose] noncomputable def orbElem (i : ℕ) : J :=
  if _h : 0 < i ∧ orbPar i < i then
    labGenH (orbLab i) * orbElem (orbPar i) * (labGenH (orbLab i))⁻¹
  else involT
termination_by i
decreasing_by exact _h.2

theorem orbElem_zero : orbElem 0 = involT := by
  rw [orbElem]
  simp

@[expose] noncomputable def orbSet : Set J := orbElem '' (Finset.range 819 : Set ℕ)

end CFSG.Sporadic.ThSchreier
