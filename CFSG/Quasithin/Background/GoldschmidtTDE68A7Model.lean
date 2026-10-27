module

public import CFSG.Quasithin.Background.GoldschmidtTDE68A7Gen

public section

namespace CFSG.Quasithin.E6.Alt.A7

theorem altModel_seven : AltModel G7 D7q where
  encard_le := encard_invSet_le
  gen := gen_seven
  cases := by
    intro β hβ
    rw [invSet_eq] at hβ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
    rcases hβ with rfl | rfl | rfl
    · exact Or.inl isSolvable_fixedSub_pa
    · exact Or.inr ⟨N7, N7_le_fixedSub_pb, card_N7, fun H hH hp => le_N7_of_perfect H hH hp⟩
    · exact Or.inl isSolvable_fixedSub_pab

end CFSG.Quasithin.E6.Alt.A7
