module

public import CFSG.GH74.GLS.C3.Prop121.Card7F5Inputs
import Certificates.Kernel.Census.Small.C5079

public section

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open CFSG.GH74.GLS.C3.Prop121.Card7 in
open CFSG.GH74.GLS.C3.Prop121.Card7.FF in
open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5079 : XAll.countP (fun s : F7 => decide ((s : Amb 7) ∈ Tl 7)) = 14 := KernelCensus.check5079

end Certificates
