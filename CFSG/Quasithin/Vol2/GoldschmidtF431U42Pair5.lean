module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Pair4
public import CFSG.Quasithin.Background.F1Amalgam

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise

theorem not_isTwoLocal_top :
    ¬ IsTwoLocal (⊤ : Subgroup Y) := by
  rintro ⟨R, hR, hp, h⟩
  have hnorm : R.Normal := Subgroup.normalizer_eq_top_iff.1 h.symm
  exact hR (normal_two_group_trivial hnorm hp)

theorem isMaximalTwoLocal_P1 :
    IsMaximalTwoLocal P1 := by
  refine ⟨P1_isTwoLocal, fun M hM hle => ?_⟩
  rcases lattice (B0_le_P1.trans hle) with h | h | h | h
  · exact absurd (B0_le_P2 (h ▸ hle D1_mem_P1)) D1_not_mem_P2
  · exact h
  · exact absurd (h ▸ hle D1_mem_P1) D1_not_mem_P2
  · exact absurd (h ▸ hM) not_isTwoLocal_top

theorem isMaximalTwoLocal_P2 :
    IsMaximalTwoLocal P2 := by
  refine ⟨P2_isTwoLocal, fun M hM hle => ?_⟩
  rcases lattice (B0_le_P2.trans hle) with h | h | h | h
  · exact absurd (B0_le_P1 (h ▸ hle D2_mem_P2)) D2_not_mem_P1
  · exact absurd (h ▸ hle D2_mem_P2) D2_not_mem_P1
  · exact h
  · exact absurd (h ▸ hM) not_isTwoLocal_top

theorem P1_ne_P2 : P1 ≠ P2 := fun h =>
  D1_not_mem_P2 (h ▸ D1_mem_P1)

theorem isYAmalgamPair :
    IsYAmalgamPair T P1 P2 := by
  refine ⟨isSylow_T, P1_ne_P2, fun M => ⟨?_, ?_⟩⟩
  · rintro ⟨hM, hN⟩
    rw [normalizer_T] at hN
    rcases lattice hN with h | h | h | h
    · exfalso
      have := hM.2 P1 P1_isTwoLocal (h ▸ B0_le_P1)
      exact D1_not_mem_P2 (B0_le_P2 (h ▸ this ▸ D1_mem_P1))
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (h ▸ hM.1) not_isTwoLocal_top
  · rintro (rfl | rfl)
    · exact ⟨isMaximalTwoLocal_P1, by rw [normalizer_T]; exact B0_le_P1⟩
    · exact ⟨isMaximalTwoLocal_P2, by rw [normalizer_T]; exact B0_le_P2⟩

end CFSG.Quasithin.H13.F431.U42
