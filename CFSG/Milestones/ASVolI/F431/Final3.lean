module

public import CFSG.Milestones.ASVolI.F431.Final2
public import CFSG.Milestones.ASVolI.F431.A35Tits
public import CFSG.Milestones.ASVolI.F431.F4Two

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF

@[expose] def burnsideF4m_A35Rest4 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z →
    ((κ = .G2 ∧ f < 2) ∨ (κ = .U4 ∧ f < 2) ∨ (κ = .U5 ∧ f < 2)) →
    ∀ i j : ↥(M₁ ⊓ M₂), (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) →
      i ≠ 1 → j ≠ 1 → i * i = 1 → j * j = 1 →
      ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j))

section Final3

set_option linter.unusedSectionVars false


theorem burnsideF4m_A35Rest'''_of4 (hrest : burnsideF4m_A35Rest4) : burnsideF4m_A35Rest''' := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hk i j hi hj hi1 hj1 hi2 hj2
  rcases hk with hk | ⟨rfl, hf⟩ | hk | hk
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp (Or.inl hk) i j hi hj hi1 hj1 hi2 hj2
  · exact burnsideF4m_F_4_35_F4Two hyp hf i j hi hj hi1 hj1 hi2 hj2
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp (Or.inr (Or.inl hk)) i j hi hj hi1 hj1 hi2 hj2
  · exact hrest _ _ _ _ _ _ _ _ _ _ _ hyp (Or.inr (Or.inr hk)) i j hi hj hi1 hj1 hi2 hj2

theorem burnsideF4m_A35Rest'_of4 (hrest : burnsideF4m_A35Rest4) : burnsideF4m_A35Rest' :=
  burnsideF4m_A35Rest'_of'' (burnsideF4m_A35Rest''_of''' (burnsideF4m_A35Rest'''_of4 hrest))

theorem burnsideF4m_F_4_35_final4 (h35 : burnsideF4m_A35Rest4) : F_4_35 :=
  burnsideF4m_F_4_35_final' (burnsideF4m_A35Rest'_of4 h35)

theorem burnsideF4m_F_4_40_final4 (hU : burnsideF4m_OddIndexU2) (h35 : burnsideF4m_A35Rest4) :
    F_4_40 :=
  burnsideF4m_F_4_40_final' hU (burnsideF4m_A35Rest'_of4 h35)

theorem burnsideF4m_F_4_43_final4 (hU : burnsideF4m_OddIndexU2) (h35 : burnsideF4m_A35Rest4)
    (h42 : burnsideF4m_A42Rest') : F_4_43 :=
  burnsideF4m_F_4_43_final' hU (burnsideF4m_A35Rest'_of4 h35) h42

end Final3

end CFSG.ASVolI
