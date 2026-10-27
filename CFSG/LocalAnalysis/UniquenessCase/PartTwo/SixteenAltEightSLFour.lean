module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.H13.A6S1372L76X

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.H13.A6

theorem s16low_isSLn_of_isAlt_eight {X : Type} [Group X] (hAlt : IsAlt X 8) :
    IsSLn X 4 1 := by
  obtain ⟨e⟩ := hAlt
  refine ⟨ZMod 2, inferInstance, inferInstance, ?_, ⟨e.trans A6L76X.alt8Equiv⟩⟩
  rw [Nat.card_zmod]
  norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
