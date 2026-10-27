module

public import CFSG.GH74.GLS.C3.Prop121.FinCentInputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Prop121
open Equiv Perm

namespace CertificateChecks.Batch5088

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Prop121
open Equiv Perm

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem okCent5_0 : okCent 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem okCent6_1 : okCent 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem okCent7_2 : okCent 7 = true := by
  decide +kernel

end CertificateChecks.Batch5088

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open Equiv Perm in
theorem certificate5088 : (okCent 5 = true)
    ∧ (okCent 6 = true)
    ∧ (okCent 7 = true) := by
  exact ⟨CertificateChecks.Batch5088.okCent5_0, CertificateChecks.Batch5088.okCent6_1, CertificateChecks.Batch5088.okCent7_2⟩

end Certificates
