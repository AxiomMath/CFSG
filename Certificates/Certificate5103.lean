module

public import CFSG.GH74.GLS.Stage4.Q9.ThetaPropsInputs
import Certificates.Kernel.Direct.C5103

public section

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.Stage4 in
open CFSG.GH74.GLS.Stage4.Q9 in
open CFSG.GH74.GLS.Stage4.Q9.ThetaProps in
open CFSG Subgroup in
theorem certificate5103 : (∀ l : Lg, typ l ∈ typList)
    ∧ (typCountsOK = true) :=
  ⟨KernelDirect.C5103.typ_memList_0, KernelDirect.C5103.typCountsOK_eq_1⟩

end Certificates
