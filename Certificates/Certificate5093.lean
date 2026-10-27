
module

public import Certificates.Certificate5093Base
import all Certificates.Certificate5093Base

import all CFSG.GH74.GLS.C3.Prop121.MooreFiniteBase

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Prop121
open Equiv Perm

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open Equiv Perm in
theorem certificate5093 : (searchAll5 a4C5 oddC5 evenC5)
    ∧ (searchAll6 a4C6 oddC6 evenC6) := by
  exact ⟨CertificateChecks.Batch5093.searchAll5_true_0, CertificateChecks.Batch5093.searchAll6_true_1⟩

end Certificates
