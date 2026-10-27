module

public import CFSG.RankThree.Chevalley.SteinbergCFOddCommutingSL2

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem higher_ordinary_exceptional_four_commuting_faithful_SL2 (K : Type) [Field K]
    (hK : ringChar K ≠ 2) (τ : Tag) (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∃ ι : Fin 4 → (SL2 K →* adjointGroup τ K), (∀ i, Function.Injective (ι i)) ∧
      ∀ i j, i ≠ j → ∀ A B : SL2 K, ι i A * ι j B = ι j B * ι i A := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact exists_commuting_faithful_of_check_of_ringChar_ne_two hK .F4
      ![![0, 1, 0, 0], ![0, 1, 2, 0], ![0, 1, 2, 2], ![2, 3, 4, 2]] (by decide +kernel)
  · exact exists_commuting_faithful_of_check_of_ringChar_ne_two hK .E6
      ![![0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 1], ![1, 2, 2, 3, 2, 1]]
      (by decide +kernel)
  · exact exists_commuting_faithful_of_check_of_ringChar_ne_two hK .E7
      ![![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0, 0],
        ![0, 1, 0, 0, 0, 0, 0]] (by decide +kernel)
  · exact exists_commuting_faithful_of_check_of_ringChar_ne_two hK .E8
      ![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0],
        ![0, 1, 1, 1, 0, 0, 0, 0]] (by decide +kernel)

end CFSG.RankThree.Chevalley
