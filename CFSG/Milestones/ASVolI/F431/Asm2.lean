module

public import CFSG.Milestones.ASVolI.F431.L35Sp
public import CFSG.Milestones.ASVolI.F431.ASp2Facts
public import CFSG.Milestones.ASVolI.F431.Asm

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Asm2

set_option linter.unusedSectionVars false

theorem burnsideF4m_F_4_38_of_core (hlie : burnsideF4m_LieCoreInput)
    (hU : burnsideF4m_OddIndexU2) : F_4_38 :=
  burnsideF4m_F_4_38_of_top hlie burnsideF4m_topSp2 hU

@[expose] def burnsideF4m_F435Rest : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → κ ≠ .L3 → κ ≠ .Sp4 →
    ∀ i j : ↥(M₁ ⊓ M₂), (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      i ≠ 1 → j ≠ 1 → i * i = 1 → j * j = 1 →
      ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j))

theorem burnsideF4m_F_4_35_of (hcore : burnsideF4m_LieCoreSp) (hrest : burnsideF4m_F435Rest) :
    F_4_35 := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp i j hi hj hi1 hj1 hi2 hj2
  by_cases hL3 : κ = .L3
  · subst hL3
    exact burnsideF4j_F_4_35_L3 hyp i j hi hj hi1 hj1 hi2 hj2
  by_cases hSp : κ = .Sp4
  · subst hSp
    exact burnsideF4m_F_4_35_Sp4 hcore burnsideF4m_sp2Facts burnsideF4m_topSp2 hyp i j hi hj
      hi1 hj1 hi2 hj2
  exact hrest κ f E Gp M₁ M₂ Y β M ε z hyp hL3 hSp i j hi hj hi1 hj1 hi2 hj2

end Asm2

end CFSG.ASVolI
