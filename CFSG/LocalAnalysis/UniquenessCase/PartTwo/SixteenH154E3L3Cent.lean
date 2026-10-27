module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16h_isL3_centreless {X : Type} [Group X] (h : IsL3 X 1) :
    ∀ a : X, (∀ b : X, a * b = b * a) → a = 1 := by
  have hSC : StatedClassicalModel X .PSL 3 2 1 :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  haveI : Finite X := CFSG.LieType.Simplicity.finite_of_statedClassicalModel hSC
  have hc : Subgroup.center X = ⊥ := center_eq_bot_of_isL3 h
  intro a ha
  have ha' : a ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr fun b => (ha b).symm
  rwa [hc, Subgroup.mem_bot] at ha'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
