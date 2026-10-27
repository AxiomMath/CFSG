
module

public import CFSG.Sporadic.SuzRecog.SuzL34.Facts
import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0SuzTests
import CFSG.Sporadic.SuzRecog.LocalRFusionGenTests
import CFSG.Sporadic.SuzRecog.C1ModelTests
import CFSG.Sporadic.SuzOddCore.ArraysCheckInputs
import CFSG.Sporadic.SuzOddCore.FamilyCheckInputs
meta import CFSG.Sporadic.SuzOddCore.ArraysCheck
meta import Certificates.Data.CFSGNative.Schreier.Refine
meta import Certificates.Data.CFSGNative.Perm.Chain
import CFSG.Sporadic.SuzOddCore.InvArrays
import CFSG.Sporadic.SuzOddCore.ArraysCheck
import Certificates.Data.CFSGNative.Schreier.Refine
meta import CFSG.Sporadic.SuzOddCore.InvArrays
import CFSG.Sporadic.SuzOddCore.InvArraysCheck
import Certificates.Data.CFSGNative.Schreier.Check
meta import CFSG.Sporadic.SuzOddCore.InvArraysCheck
meta import Certificates.Data.CFSGNative.Schreier.Check
import CFSG.Sporadic.SuzOddCore.InvGraphCheckInputs
meta import Mathlib.Data.Fintype.Card
import CFSG.Sporadic.SuzOddCore.InvTCheckInputs
meta import CFSG.Sporadic.SuzOddCore.InvGraphCheck
meta import CFSG.Sporadic.SuzOddCore.SmallChainCheck
import CFSG.Sporadic.SuzOddCore.SmallChainCheckInputs
import Certificates.Kernel.Sporadic.OddCore.SuzBtCG
import Certificates.Kernel.Sporadic.OddCore.SuzBtZG
import Certificates.Kernel.Sporadic.OddCore.SuzBtLG
import Certificates.Kernel.Sporadic.OddCore.SuzBtOG
import Certificates.Kernel.Sporadic.OddCore.SuzBtTG
import Certificates.Kernel.Sporadic.OddCore.SuzBtFG
import Certificates.Kernel.Sporadic.OddCore.SuzBtVG
import Certificates.Kernel.Sporadic.OddCore.SuzBtQG
import Certificates.Kernel.Sporadic.OddCore.SuzBtWG

public section

namespace Certificates

open CertificateChecks.KernelSpor

open CFSG in
theorem certificate727301 : CFSG.Sporadic.SuzRecog.SuzL34Cert.F1Prop ∧
    CFSG.Sporadic.SuzRecog.SuzL34Cert.F1MProp ∧
    CFSG.Sporadic.SuzRecog.SuzL34Cert.F2Prop ∧
    CFSG.Sporadic.SuzRecog.SuzL34Cert.F3Prop ∧
    CFSG.Sporadic.SuzRecog.SuzL34Cert.F4Prop ∧
    CFSG.Sporadic.SuzRecog.SuzL34Cert.F5Prop ∧
    CFSG.Sporadic.SuzRecog.SuzL34Cert.F6Prop ∧
    CFSG.Sporadic.SuzRecog.SuzL34Cert.F7Prop ∧
    CFSG.Sporadic.SuzRecog.SuzL34Cert.F8Prop :=
  ⟨SuzBtCG.f1Prop, SuzBtZG.f1mProp, SuzBtLG.f2Prop, SuzBtOG.f3Prop, SuzBtTG.f4Prop,
    SuzBtFG.f5Prop, SuzBtVG.f6Prop, SuzBtQG.f7Prop, SuzBtWG.f8Prop⟩

end Certificates
