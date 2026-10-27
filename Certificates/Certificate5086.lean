module

public import CFSG.GH74.GLS.C3.Prop121.CzCoordInputs
import Certificates.Kernel.Census.Small.C5086

public section

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open Subgroup Equiv Perm CFSG.GH74.GLS in
theorem certificate5086 : (okOdd 5 = true)
    ∧ (okOdd 6 = true)
    ∧ (okOdd 7 = true) := KernelCensus.check5086

end Certificates
