
module

public import Certificates.Certificate5014Base
import all Certificates.Certificate5014Base


public section

open CFSG
open CFSG.GH74
open CFSG.GH74.E2
open Subgroup

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.E2 in
open Subgroup in
theorem certificate5014 : Nat.card (MulAut (QuaternionGroup 2)) = 24 := by
  exact CertificateChecks.Batch5014.card_mulAut_q8_0

end Certificates
