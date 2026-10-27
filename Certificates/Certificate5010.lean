module

import Certificates.Kernel.Census.Small.C5010
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.GH74.E2.SD16CertInputs

public section

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.E2 in
open Subgroup in
theorem certificate5010 : ∃ z : SD16M, z ≠ 1 ∧ z * z = 1 ∧ ∀ y : SD16M, y * z = z * y := KernelCensus.check5010

end Certificates
