
module

public import CFSG.Sporadic.ThSchreier.TwoGenerateBase

public import CFSG.Sporadic.ThSchreier.CentralCentralizerBase1
public import CFSG.Sporadic.ThSchreier.TwoCentralizerBase1
public import CFSG.Sporadic.ThSchreier.AutAssembly
public import CFSG.Sporadic.Th.Plane
public import CFSG.Sporadic.Th.FormBase
public import Certificates.Data.CFSGNative.Th.Base
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.ThSchreier.CentralizerDataInputs
public meta import CFSG.Sporadic.ThSchreier.Text
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.Th.SimpleBase1
public meta import CFSG.Sporadic.ThSchreier.Row
public meta import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public import CFSG.Sporadic.ThSchreier.LocalOrbitInputs
public meta import CFSG.Sporadic.ThSchreier.WordsBase1
public meta import CFSG.Sporadic.ThSchreier.LocalData
public import CFSG.Sporadic.ThSchreier.OrbitCheck819Inputs
public meta import CFSG.Sporadic.ThSchreier.TransporterBase
public import CFSG.Sporadic.ThSchreier.GlobalIndexBase1
public import CFSG.Sporadic.ThSchreier.RowInputs
public meta import Certificates.Data.CFSGNative.Th.Base
public import CFSG.Sporadic.ThSchreier.TwoCentralizerInputs
public meta import CFSG.Sporadic.ThSchreier.OrbitCheck819Base
public meta import CFSG.Sporadic.Th.Max3.PacketBase1
public import CFSG.Sporadic.ThSchreier.UASpaceInputs
public meta import CFSG.Sporadic.ThSchreier.CentralizerData
public import CFSG.Sporadic.Th.Max3.CoreBase1
public import CFSG.Sporadic.Th.Max3.AltNine
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Sporadic.Th.Max3.QuotientInputs
public import CFSG.Sporadic.Th.Max3.Data

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 Pointwise

theorem conj_mem_centralizer_a
    {x : J} (hx : x * involT = involT * x) :
    transporterV * x * transporterV⁻¹ ∈ Subgroup.centralizer {a} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have e : a = transporterV * involT * transporterV⁻¹ := by rw [involT]; group
  rw [e]
  calc transporterV * x * transporterV⁻¹ * (transporterV * involT * transporterV⁻¹) =
        transporterV * (x * involT) * transporterV⁻¹ := by group
    _ = transporterV * (involT * x) * transporterV⁻¹ := by rw [hx]
    _ = _ := by group

section Facts

variable {c : ℕ} (hC : CertFacts c) (hS : ThScanFacts)
include hC hS

end Facts

end CFSG.Sporadic.ThSchreier
