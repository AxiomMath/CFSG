module

public import CFSG.Monster.Schur.M24Pres
import Certificates.Kernel.M24.Bridge
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.Schur CFSG.Monster.Schur.M24 in
open TauCeti in
theorem certificate9250 : pres.generatorCount = 2 := KernelBounds.m24_gens

end Certificates
