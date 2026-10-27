module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemTitsPerms
import Certificates.Kernel.SporSch.Tits.Syl8117
public import CFSG.Sporadic.Schreier.TitsInv

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier.Tits CFSG.RankThree.PartTwo.Sec4.Item434RemTits in
theorem certificate8117 :
    sylPerms.Nodup ∧ (∀ g ∈ sylPerms, ∀ h ∈ sylPerms, g * h ∈ sylPerms) ∧
      (∀ g ∈ sylPerms, g ^ 3 = 1) ∧ (∃ g ∈ sylPerms, ∃ h ∈ sylPerms, g * h ≠ h * g) ∧
      (∀ w ∈ sylWords, wordIn 13 titsT w ≠ 1 →
        ¬ 5 ∣ Fintype.card {p : Fin 2925 // wordIn 13 titsTStar w p = p} ∧
        ¬ 13 ∣ Fintype.card {p : Fin 2925 // wordIn 13 titsTStar w p = p}) ∧
      bOne ≠ 1 ∧ bOne ^ 3 = 1 ∧ bOne * titsTInv = titsTInv * bOne ∧
      ∀ n ∈ titsN, n * n = 1 → n * titsTInv = titsTInv * n → n * bOne = bOne * n →
        n = 1 ∨ n = titsTInv := KernelSporSch.TitsSyl.facts

end Certificates
