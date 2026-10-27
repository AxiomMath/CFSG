module

public import CFSG.GH74.GLS.C3.Prop121.Card7H3Inputs
import Certificates.Kernel.Card7H3.Checks
import CFSG.Certificates.Kernel.Card7H3.Sound

public section

namespace Certificates

open CFSG.Certificates.Kernel.Card7H3 in
open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open CFSG.GH74.GLS.C3.Prop121.Card7 in
open CFSG.GH74.GLS.C3.Prop121.Card7.HC in
open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Layer3 in
theorem certificate5082 : (classesCheck = true)
    ∧ (powCheck = true)
    ∧ (ryCheck = true) :=
  ⟨classesCheck_of Kernel.Card7H3.k5082a_true, powCheck_of Kernel.Card7H3.k5082b_true,
    ryCheck_of Kernel.Card7H3.k5082c_true⟩

end Certificates
