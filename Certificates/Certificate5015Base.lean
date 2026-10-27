
module

public import CFSG.GH74.E2.SD16CertInputs
import all CFSG.GH74.E2.OuterL33
import all CFSG.GH74.E2.OuterCore
import all CFSG.GH74.E2.L33AutTable
import all CFSG.GH74.E2.LocalLeaves
import all CFSG.GH74.E2.Alpha1Core
import all CFSG.CharacterTheory.Semidihedral.Model
import all CFSG.GH74.E2.SD16Cert
import all CFSG.GH74.E2.OuterL33GBase

@[expose] public section

open CFSG
open CFSG.GH74
open CFSG.GH74.E2
open Subgroup CFSG.GH74.GLS

namespace CertificateChecks.Batch5015

private theorem sd16_exists_central_0 : ∃ z : SD16M, (∀ w : SD16M, w * z = z * w) ∧ z * z = 1 ∧ z ≠ 1 := 
  ⟨(gx 4).1 ^ 4, by decide +kernel, by decide +kernel, by decide +kernel⟩

end CertificateChecks.Batch5015

