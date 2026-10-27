module

public import CFSG.RankThree.PartOne.CTP.SporadicOrders

public section

namespace CFSG.RankThree.PartOne.Q1327S

open CFSG.Blueprint TauCeti CFSG.RankThree.PartOne.CTP

theorem cube_of_pairNC
    {s : SporadicName} {p : ℕ} (h : SporadicPairNC s p)
    (hLy : s ≠ .Ly) (hHN : s ≠ .HN) (hp7 : p ≠ 7) :
    p ^ 3 ∣ Nat.card (NativeSporadic.Carrier s) ∧
      ¬ p ^ 4 ∣ Nat.card (NativeSporadic.Carrier s) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [show Nat.card (NativeSporadic.Carrier .J4) = 86775571046077562880 from
      CFSG.Sporadic.J4.card_J4]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .McL) = 898128000 from CFSG.Sporadic.McL.card_McL]
    norm_num
  · exact absurd rfl hLy
  · rw [show Nat.card (NativeSporadic.Carrier .HS) = 44352000 from CFSG.Sporadic.HS.card_HS]
    norm_num
  · exact absurd rfl hp7
  · rw [show Nat.card (NativeSporadic.Carrier .Ru) = 145926144000 from CFSG.Sporadic.Ru.card_Ru]
    norm_num
  · exact absurd rfl hp7
  · rw [show Nat.card (NativeSporadic.Carrier .Co3) = 495766656000 from
      CFSG.Sporadic.Co3.card_Co3]
    norm_num
  · rw [show Nat.card (NativeSporadic.Carrier .Co2) = 42305421312000 from
      CFSG.Sporadic.Co2.card_Co2]
    norm_num
  · exact absurd rfl hHN
  · rw [show Nat.card (NativeSporadic.Carrier .Th) = 90745943887872000 from card_Th]
    norm_num

end CFSG.RankThree.PartOne.Q1327S
