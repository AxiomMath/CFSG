module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86PresIso11
public import CFSG.Quasithin.Recognition.GoldschmidtFan86PresIso12

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Quasithin

theorem iso_of_admitsPres :
    IsoOfAdmitsPres := by
  intro n A C B A' C' B' _ _ _ _ _ _ X X' hAi hBi hAi' hBi' hC hC' hX hX'
  have cA : Nat.card A = 5 * 2 ^ n := by rw [card_vertexA X, hC, hAi, mul_comm]
  have cB : Nat.card B = 3 * 2 ^ n := by rw [card_vertexB X, hC, hBi, mul_comm]
  have cA' : Nat.card A' = 5 * 2 ^ n := by rw [card_vertexA X', hC', hAi', mul_comm]
  have cB' : Nat.card B' = 3 * 2 ^ n := by rw [card_vertexB X', hC', hBi', mul_comm]
  rcases hX with ⟨rfl, hX⟩ | ⟨rfl, hX⟩
  · rcases hX' with ⟨-, hX'⟩ | ⟨h, -⟩
    · obtain ⟨φA, φB, hl, hb⟩ := exists_presEquiv11 hX cA cB
      obtain ⟨φA', φB', hl', hb'⟩ := exists_presEquiv11 hX' cA' cB'
      exact isIso_of_links (φA.symm.trans φA') (φB.symm.trans φB') _ _ _ _ hl hl' hb hb'
        (fun i => by simp) (fun i => by simp)
    · omega
  · rcases hX' with ⟨h, -⟩ | ⟨-, hX'⟩
    · omega
    · obtain ⟨φA, φB, hl, hb⟩ := exists_presEquiv12 hX cA cB
      obtain ⟨φA', φB', hl', hb'⟩ := exists_presEquiv12 hX' cA' cB'
      exact isIso_of_links (φA.symm.trans φA') (φB.symm.trans φB') _ _ _ _ hl hl' hb hb'
        (fun i => by simp) (fun i => by simp)

end CFSG.Quasithin.Fan86
