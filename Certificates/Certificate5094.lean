module

public import CFSG.GH74.GLS.C3.Prop121.MooreFinite7Inputs
import Certificates.Kernel.Moore7.Checks
import CFSG.Certificates.Kernel.PermCent.Moore7CSound

public section

open CFSG.Certificates.Kernel.PkCV Certificates.Kernel.Moore7

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open Equiv Perm in
theorem certificate5094 : okAll7 a4L7 oddL7 evenL7 = true :=
  okAll7_eq.trans m7F_true

end Certificates
