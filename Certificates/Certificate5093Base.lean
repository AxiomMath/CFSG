
module

public import CFSG.GH74.GLS.C3.Prop121.MooreFiniteInputs
import all CFSG.GH74.GLS.C3.Prop121.MooreFiniteBase
import all CFSG.GH74.GLS.C3.Prop121.MooreFiniteInputs

@[expose] public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Prop121
open Equiv Perm

namespace CertificateChecks.Batch5093

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option Elab.async false in
private theorem searchAll5_true_0 : searchAll5 a4C5 oddC5 evenC5 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option Elab.async false in
private theorem searchAll6_true_1 : searchAll6 a4C6 oddC6 evenC6 := by
  decide +kernel

end CertificateChecks.Batch5093

