module

public import Certificates.Certificate8117

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemTits

open CFSG.Sporadic.Schreier.Tits

theorem tits_three_check :
    sylPerms.Nodup ∧ (∀ g ∈ sylPerms, ∀ h ∈ sylPerms, g * h ∈ sylPerms) ∧
      (∀ g ∈ sylPerms, g ^ 3 = 1) ∧ (∃ g ∈ sylPerms, ∃ h ∈ sylPerms, g * h ≠ h * g) ∧
      (∀ w ∈ sylWords, wordIn 13 titsT w ≠ 1 →
        ¬ 5 ∣ Fintype.card {p : Fin 2925 // wordIn 13 titsTStar w p = p} ∧
        ¬ 13 ∣ Fintype.card {p : Fin 2925 // wordIn 13 titsTStar w p = p}) ∧
      bOne ≠ 1 ∧ bOne ^ 3 = 1 ∧ bOne * titsTInv = titsTInv * bOne ∧
      ∀ n ∈ titsN, n * n = 1 → n * titsTInv = titsTInv * n → n * bOne = bOne * n →
        n = 1 ∨ n = titsTInv :=
  Certificates.certificate8117

end CFSG.RankThree.PartTwo.Sec4.Item434RemTits
