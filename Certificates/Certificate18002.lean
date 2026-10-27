module

public import CFSG.CharacterTheory.SteinbergBYAlternatingSixDefs
import Certificates.Kernel.Misc.Perm.A6Rep

public section

namespace Certificates

open CertificateChecks

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix in
open Matrix Equiv FieldFour in
open scoped Kronecker in
theorem certificate18002 : (
    ∀ σ : Perm (Fin 6), invCheckIfThreeCycle σ = true
  ) ∧ (
    cert8a.check rep8aTab = true
  ) ∧ (
    classCheck = true
  ) ∧ (
    classSumCheck = true
  ) := KernelMisc.A6Rep.facts

end Certificates
