module

public import CFSG.GH74.GLS.C3.Prop121.CzCoordInputs

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open Subgroup Equiv Perm CFSG.GH74.GLS in
theorem check5086 : (okOdd 5 = true)
    ∧ (okOdd 6 = true)
    ∧ (okOdd 7 = true) := by
  repeat' apply And.intro
  all_goals decide +kernel

end CertificateChecks.KernelCensus
