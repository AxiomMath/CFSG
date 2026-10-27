
module

public import Certificates.Certificate5065Base
import all Certificates.Certificate5065Base


public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open CFSG.Certificates.Kernel
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Layer2 in
open CFSG.GH74.GLS.C3.Layer2.L5 in
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5065 : (mt0Chk = true)
    ∧ (inv0Chk = true)
    ∧ (decide (Sh0L.getD 0 1 = 1) = true)
    ∧ (idx0Chk = true) := by
  exact ⟨CertificateChecks.Batch5065.mt0Chk_true_0, CertificateChecks.Batch5065.inv0Chk_true_1, CertificateChecks.Batch5065.one0Chk_true_2, CertificateChecks.Batch5065.idx0Chk_true_3⟩

end Certificates
