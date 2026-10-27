module

public import CFSG.Milestones.ASVolI.F431.L39Two
public import CFSG.Milestones.ASVolI.F431.AInvMain

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Asm

set_option linter.unusedSectionVars false

@[expose] def burnsideF4m_OddIndexU2 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M →
    ((κ = .U4 ∧ f = 1) ∨ (κ = .U5 ∧ f = 1)) → Odd Gp.index

theorem burnsideF4m_F_4_38_of_top (hlie : burnsideF4m_LieCoreInput) (htop : burnsideF4m_TopSp2)
    (hU : burnsideF4m_OddIndexU2) : F_4_38 := by
  refine burnsideF4m_F_4_38_of_lie' hlie ?_
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hL43 hκ
  rcases hκ with ⟨rfl, rfl⟩ | hκ
  · rw [htop E Gp M₁ M₂ hyp.amalgam, Subgroup.index_top]
    exact odd_one
  · exact hU κ f E Gp M₁ M₂ Y β M ε z hyp hL43 hκ

theorem burnsideF4m_F_4_40_of (h35 : F_4_35) (h38 : F_4_38) : F_4_40 :=
  burnsideF4ja_F_4_40_of burnsideF4m_F_4_33 h35 h38

theorem burnsideF4m_F_4_43_of (h35 : F_4_35) (h38 : F_4_38) (h39 : F_4_39) (h42 : F_4_42) :
    F_4_43 :=
  burnsideF4ja_F_4_43_of burnsideF4m_centInput h35 h38 h39 h42

end Asm

end CFSG.ASVolI
