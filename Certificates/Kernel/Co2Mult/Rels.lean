module

public import CFSG.Sporadic.Recognition.Co2MultiplierInputs
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Kernel.Co2Cover.Tabs

public section

namespace CertificateChecks.KernelCo2Mult

open CFSG.KC.MiscCoset CFSG.Sporadic.Recognition.Co2Multiplier

theorem co2Cover_enc : co2Cover.map encW = CFSG.KBRoute.F24011a.rels := by decide +kernel

end CertificateChecks.KernelCo2Mult

end
