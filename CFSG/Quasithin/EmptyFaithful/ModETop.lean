module

public import CFSG.Quasithin.EmptyFaithful.ModEFour
public import CFSG.Quasithin.EmptyFaithful.ModEAbs3
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1469Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem input14610Four_proved :
    Input14610Four := by
  intro D _ _ G₁ G₂ z A hGT hF hz1 hz2 hzG hzc hcent hAG hAel hAnorm hAcard
  have h13 : F6.IsAutM12 D → False := fun hD =>
    ModE.four_of_autM12 hD hGT hz1 hz2 hzG hzc hcent hAG hAel hAnorm hAcard
  have hle : Nat.card A ≤ 8 := by
    rcases hF with h | h
    · exact ModE.case_bound hGT h (Or.inr rfl) hAG hAel hAnorm h13
    · exact ModE.case_bound hGT.symm h (Or.inl rfl) hAG hAel hAnorm h13
  omega

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

end CFSG.Quasithin
