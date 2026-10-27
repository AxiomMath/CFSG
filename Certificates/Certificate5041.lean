module

public import CFSG.GH74.GLS.C3.Layer2.FinModelTabInputs
import Certificates.Kernel.Direct.C5041

public section

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.Model in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2 in
theorem certificate5041 : ((mkTab 6).validB = true)
    ∧ ((mkTab 7).validB = true) :=
  ⟨KernelDirect.C5041.validB6_0, KernelDirect.C5041.validB7_1⟩

end Certificates
