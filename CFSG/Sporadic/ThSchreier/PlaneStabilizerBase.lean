
module

public import CFSG.Sporadic.ThSchreier.OrbitCheck819Base
public import CFSG.Sporadic.ThSchreier.PlaneFactsBase
public meta import CFSG.Sporadic.ThSchreier.TransporterBase
public meta import CFSG.Sporadic.ThSchreier.UASpaceBase
public import CFSG.Sporadic.ThSchreier.TransporterBase
public import CFSG.Sporadic.ThSchreier.UASpaceBase
public import CFSG.Sporadic.ThSchreier.GlobalDataBase
public import CFSG.Sporadic.Th.SimpleBase
public meta import CFSG.Sporadic.ThSchreier.RowBase
public meta import CFSG.Sporadic.ThSchreier.LocalOrbitBase
public import CFSG.Sporadic.ThSchreier.LocalOrbitInputs
public meta import CFSG.Sporadic.ThSchreier.WordsBase
public meta import CFSG.Sporadic.ThSchreier.LocalDataBase
public import CFSG.Sporadic.ThSchreier.OrbitCheck819Inputs
public import CFSG.Sporadic.ThSchreier.RowInputs
public meta import Certificates.Data.CFSGNative.Th.Base
public import CFSG.Sporadic.ThSchreier.UASpaceInputs
public meta import CFSG.Sporadic.ThSchreier.CentralizerDataBase
public import CFSG.Sporadic.Th.PlaneBase
public import CFSG.Sporadic.Th.FormBase
public import Certificates.Data.CFSGNative.Th.Base
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.DataBase

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

theorem orbTable_getElem {i : ℕ} (hi : i < 819) : orbTable[i]! = orbRows i := by
  rw [getElem!_pos orbTable i (by simp [orbTable, hi])]
  simp [orbTable]

end CFSG.Sporadic.ThSchreier
