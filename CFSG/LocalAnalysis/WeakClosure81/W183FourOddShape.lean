module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Odd
import CFSG.Quasithin.Vol2.F134Orders
import CFSG.Quasithin.Vol2.Ch3Sec3InspA312KG

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)

theorem w183fourodd_oddShape_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : OddShape X) : OddShape Y := by
  rcases h with ⟨p, k, hp, hp2, h9, hL⟩ | ⟨p, hp, h5, ⟨h4, hL⟩ | ⟨h4, hL⟩⟩
  · exact Or.inl ⟨p, k, hp, hp2, h9, CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e hL⟩
  · exact Or.inr ⟨p, hp, h5, Or.inl ⟨h4, CFSG.Blueprint.LieModel.of_mulEquiv e hL⟩⟩
  · exact Or.inr ⟨p, hp, h5, Or.inr ⟨h4, CFSG.Blueprint.LieModel.of_mulEquiv e hL⟩⟩

theorem w183fourodd_oddShape_three_dvd {X : Type} [Group X] (h : OddShape X) :
    3 ∣ Nat.card X := by
  rcases h with ⟨p, k, -, -, -, hL⟩ | ⟨p, -, -, ⟨-, hL⟩ | ⟨-, hL⟩⟩
  · exact CFSG.Quasithin.F134.three_dvd_card_of_statedPSL_two hL
  · exact CFSG.Quasithin.F134.three_dvd_card_of_statedPSL_three
      (hL.statedClassicalModel (by decide))
  · exact CFSG.Quasithin.F134.three_dvd_card_of_statedPSU_three
      (hL.statedClassicalModel (by decide))

theorem w183fourodd_oddShape_simple_nonab {X : Type} [Group X] (h : OddShape X) :
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  rcases h with ⟨p, k, -, -, -, hL⟩ | ⟨p, -, -, ⟨-, hL⟩ | ⟨-, hL⟩⟩
  · exact ⟨CFSG.Quasithin.H13.InspA312.isSimpleGroup_of_isPSL hL,
      CFSG.Quasithin.H13.InspA312.exists_noncomm_of_isPSL hL⟩
  · have hS := hL.statedClassicalModel (by decide)
    exact ⟨CFSG.Quasithin.H13.InspA312.isSimpleGroup_of_isPSL hS,
      CFSG.Quasithin.H13.InspA312.exists_noncomm_of_isPSL hS⟩
  · have hS := hL.statedClassicalModel (by decide)
    exact ⟨CFSG.Quasithin.H13.InspA312.isSimpleGroup_of_isPSU hS,
      CFSG.Quasithin.H13.InspA312.exists_noncomm_of_isPSU hS⟩

end CFSG.LocalAnalysis.WeakClosure81

end
