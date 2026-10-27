module

public import CFSG.Sporadic.Recognition.McLCentralizerInputs
public meta import CFSG.Sporadic.SmallOddCore.McLData
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
import Certificates.Kernel.McL.MooreFacts
import CFSG.Certificates.Kernel.Spor.RawSound

public section

namespace Certificates

open CertificateChecks

theorem certificate21000 : (CFSG.Sporadic.Recognition.McLCentralizer.mooreCheck = true)
    ∧ (CFSG.Sporadic.Recognition.McLCentralizer.liftCheck = true) := KernelMcL.Moore.facts21000

end Certificates
