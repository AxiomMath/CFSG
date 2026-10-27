module

public import CFSG.Sporadic.Recognition.RuMultiplierTables
import Certificates.Kernel.CosetJ.RuTab
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

namespace Certificates

open CertificateChecks

theorem certificate15024 : CFSG.Sporadic.Recognition.RuMultiplier.RuTabFact := KernelCosetJ.RuTab.fact

end Certificates
