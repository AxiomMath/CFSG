module

public import CFSG.GH74.GLS.C3.Prop121.L122FinInputs
import Certificates.Kernel.L122.Checks
import CFSG.Certificates.Kernel.PermCent.Ok122CSound

public section

open CFSG.Certificates.Kernel.PkCV Certificates.Kernel.L122

namespace Certificates

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open Equiv Perm in
theorem certificate5090 : (ok122 = true)
    ∧ ((inv7.all fun a => ord3.any fun ρ => decide (ρ * a = a * ρ)) = true) :=
  ⟨ok122_eq.trans ok122F_true, comm3_eq.trans comm3F_true⟩

end Certificates
