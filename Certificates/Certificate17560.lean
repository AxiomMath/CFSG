module

public import CFSG.Sporadic.Schreier.TitsLocal
import CFSG.RankThree.PartOne.KE.TitsFiveCentralizer

public section

open CFSG.RankThree.PartOne.KE

namespace Certificates

open CFSG.Sporadic.Schreier.Tits in
theorem certificate17560 : ∃ b ∈ titsH, b ≠ 1 ∧ b ^ 5 = 1 ∧
    Nat.card ↥(titsH ⊓ Subgroup.centralizer ({b} : Set (Equiv.Perm (Fin 1755)))) ≤ 10 :=
  ⟨titsFive, titsFive_mem_titsH, titsFive_ne_one, titsFive_pow_five, card_titsCH5.le⟩

end Certificates
