module

public import Certificates.Data.GH74EvSporCheck
public meta import Certificates.Data.GH74EvSporCheck
import Certificates.Kernel.GH74.J2Norm
import Certificates.Kernel.GH74.J2Ev
import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.GH74.M12C4F
import Certificates.Kernel.GH74.M12C4
import CFSG.Sporadic.Schreier.PairJ2CertInputs
import CFSG.Sporadic.Schreier.PairJ2CheckInputs
import CFSG.Sporadic.SmallOddCore.J2CheckInputs
meta import CFSG.Sporadic.SmallOddCore.J2Data
meta import CFSG.Sporadic.Schreier.PairJ2Check

public section

namespace Certificates

open CertificateChecks

theorem certificate5150 :
    CFSG.GH74.Generic.S45.EvSpor.j2RepsOK = true ∧
    CFSG.GH74.Generic.S45.EvSpor.j2C2AEnumOK = true ∧
    CFSG.GH74.Generic.S45.EvSpor.j2C2BEnumOK = true ∧
    CFSG.GH74.Generic.S45.EvSpor.j2Cent5OK = true ∧
    CFSG.GH74.Generic.S45.EvSpor.j2OuterOK = true ∧
    CFSG.GH74.Generic.S45.EvSpor.j2KbEnumOK = true ∧
    CFSG.GH74.Generic.S45.EvSpor.j2DerivedOK = true ∧
    CFSG.GH74.Generic.S45.EvSpor.j2NormCount = 720 ∧
    CFSG.GH74.Generic.S45.EvSpor.j2E16OK = true ∧
    CFSG.GH74.Generic.S45.EvSpor.m12RepsOK = true ∧
    CFSG.GH74.Generic.S45.EvSpor.m12C2AEnumOK = true ∧
    CFSG.GH74.Generic.S45.EvSpor.m12KaEnumOK = true ∧
    CFSG.GH74.Generic.S45.EvSpor.m12DerivedOK = true ∧
    CFSG.GH74.Generic.S45.EvSpor.m12OuterOK = true :=
  ⟨KernelGH74.J2Ev.reps_ok, KernelGH74.J2Ev.c2A_ok, KernelGH74.J2Ev.c2B_ok,
    KernelGH74.J2Ev.cent5_ok, KernelGH74.J2Ev.outer_ok, KernelGH74.J2Ev.kb_ok,
    KernelGH74.J2Ev.derived_ok, KernelGH74.J2Norm.normCount_eq, KernelGH74.J2Ev.e16_ok,
    KernelGH74.M12C4.reps_ok, KernelGH74.M12C4.c2A_ok, KernelGH74.M12C4.ka_ok,
    KernelGH74.M12C4.m12_derived, KernelGH74.M12C4.outer_ok⟩

end Certificates
