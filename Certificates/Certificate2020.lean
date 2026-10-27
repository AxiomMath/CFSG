module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixIsoCheckInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixGraph
public meta import CFSG.Sporadic.SmallOddCore.HeLocalCheck
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Certificates.Data.CFSGNative.PSL3Four.Certificate
import Certificates.Kernel.LocalComp.HeldFixGraph.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.GrSLit in
open CFSG.ComponentClassification.GrSLit.HeldFix CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore in
theorem certificate2020 : enumOK 147 heldFixGraphGens heldFixGraphEnum = true ∧ heldFixGraphEnum.tabs.size = 20160 := KernelLC.HeldFixGraph.graph_true

end Certificates
