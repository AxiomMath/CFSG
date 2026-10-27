module

public import CFSG.RankThree.PartOne.Q1327S.Square
public import CFSG.RankThree.PartOne.MultRes.Suz

public section

namespace CFSG.RankThree.PartOne.Q1327S

open CFSG CFSG.RankThree.PartOne CFSG.Blueprint

variable {Q : Type} [Group Q] [Finite Q]

theorem not_perm3_Suz
    (e : Q ≃* NativeSporadic.Carrier .Suz) {Ē : Subgroup Q} (hEcard : Nat.card Ē = 5 ^ 2) :
    ¬ Nonempty (torusImage Ē ⊤ ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨x, y, h, hx, hy, hxy, hcard, hhx, hhy⟩ := MultRes.Suz_sylow5_square_witness
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hQ : ¬ 5 ^ 3 ∣ Nat.card (NativeSporadic.Carrier .Suz) := by
    rw [show Nat.card (NativeSporadic.Carrier .Suz) = 448345497600 from
      CFSG.Sporadic.Suz.card_Suz]
    norm_num
  exact not_perm3_of_square_witness_equiv e hEcard hQ hx hy hxy hcard hhx hhy (by decide +kernel)

theorem not_perm3_He
    (e : Q ≃* NativeSporadic.Carrier .He) {Ē : Subgroup Q} (hEcard : Nat.card Ē = 5 ^ 2) :
    ¬ Nonempty (torusImage Ē ⊤ ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨x, y, h, hx, hy, hxy, hcard, hhx, hhy⟩ := CFSG.SectionRank.He_sylow5_square_witness
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hQ : ¬ 5 ^ 3 ∣ Nat.card (NativeSporadic.Carrier .He) := by
    rw [show Nat.card (NativeSporadic.Carrier .He) = 4030387200 from
      CFSG.Sporadic.He.card_He]
    norm_num
  exact not_perm3_of_square_witness_equiv e hEcard hQ hx hy hxy hcard hhx hhy (by decide +kernel)

end CFSG.RankThree.PartOne.Q1327S
