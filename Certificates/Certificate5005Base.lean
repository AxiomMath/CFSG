
module

public import CFSG.GH74.E2.Alpha1CoreInputs
import all CFSG.GH74.E2.Alpha1Rank
import all CFSG.GH74.E2.Alpha1AutCert
import all CFSG.GH74.E2.NonCentralProd
import all CFSG.GH74.E2.QuasiRank
import all CFSG.GH74.E2.FrattiniRank
import all CFSG.GH74.E2.CaseIGlue
import all CFSG.LocalAnalysis.ComponentInitial.FourGroupCommuting
import all CFSG.CharacterTheory.Semidihedral.Model
import all CFSG.GH74.E2.SD16Cert
import all CFSG.GH74.E2.Alpha1CoreInputs
import all CFSG.GH74.E2.Alpha1CoreBase

@[expose] public section

open CFSG
open CFSG.GH74
open CFSG.GH74.E2
open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.Semidihedral

namespace CertificateChecks.Batch5005

private theorem sd16_nonabelian_0 : ∃ x y : SD16M, x * y ≠ y * x := 
  ⟨modelR 4 (by norm_num), modelS 4 (by norm_num), by decide +kernel⟩

private theorem sd16_central_involutions_aux_1 : ∀ x y z : SD16M, IsCentralInv16 x → IsCentralInv16 y →
    IsCentralInv16 z → x = y ∨ x = z ∨ y = z := by
  decide +kernel

end CertificateChecks.Batch5005

