module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAFiveEquiv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAFiveOmEq

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

theorem s16c13bcA_orderOf_ne_nine_om {Y : Type} [Group Y] (hY : IsOmegaPlus Y 4 2) (y : Y) :
    orderOf y ≠ 9 := by
  obtain ⟨K, hKf, hKfin, -, hcard, ⟨e⟩⟩ := s16c13bcA_omegaPlus_equiv hY
  letI := hKf
  letI := hKfin
  have h60 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 60 := s16c13bcA_card_sl2_four hcard
  have hy60 : y ^ 60 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    refine Prod.ext ?_ ?_
    · rw [Prod.pow_fst, ← h60]
      exact pow_card_eq_one'
    · rw [Prod.pow_snd, ← h60]
      exact pow_card_eq_one'
  intro h9
  have hd : orderOf y ∣ 60 := orderOf_dvd_of_pow_eq_one hy60
  rw [h9] at hd
  revert hd
  decide

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
