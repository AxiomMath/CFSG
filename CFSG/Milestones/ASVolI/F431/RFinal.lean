module

public import CFSG.Milestones.ASVolI.F431.RA35G2
public import CFSG.Milestones.ASVolI.F431.RU4Out
public import CFSG.Milestones.ASVolI.F431.RU5Out
public import CFSG.Milestones.ASVolI.F431.RD4
public import CFSG.Milestones.ASVolI.F431.A42F4Two
public import CFSG.Milestones.ASVolI.F431.Final3

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion

section Final

set_option linter.unusedSectionVars false


theorem burnsideF4r_A35Rest4 : burnsideF4m_A35Rest4 := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hκ i j hi hj hi1 hj1 hi2 hj2
  rcases hκ with ⟨rfl, hf⟩ | ⟨rfl, hf⟩ | ⟨rfl, hf⟩
  · exact burnsideF4r_A35_G2 hyp hf i j hi hj hi1 hj1 hi2 hj2
  · exact burnsideF4r_A35_U4 hyp hf i j hi hj hi1 hj1 hi2 hj2
  · exact burnsideF4r_A35_U5 hyp hf i j hi hj hi1 hj1 hi2 hj2

@[expose] def burnsideF4r_A42Rest4 : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y]
    (β : Cpl M₁ M₂ Y) (M : Type) [Group M] (ε : Y →* M) (z : M),
    HypF_4_31 κ f Gp M₁ M₂ β ε z → ¬ IsL43 M → Gp = ⊤ →
    ((κ = .G2 ∧ f = 1) ∨ (κ = .U5 ∧ f = 1)) →
    ∃ t : ↥M₂, (t : E) ∈ pCoreOf 2 (Gp ⊓ M₂) ∧ IsShortRootInv κ Gp M₁ M₂ (t : E) ∧
      Subgroup.centralizer ({epsG β ε (f2 (c := β) t)} : Set M) ≤ MiTwo β ε

theorem burnsideF4r_A42Rest'''_of4 (hrest : burnsideF4r_A42Rest4) : burnsideF4m_A42Rest''' := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp hL43 hodd hκ
  haveI := hyp.amalgam.finite
  rcases hκ with ⟨rfl, hf⟩ | ⟨rfl, hf⟩ | ⟨rfl, hf⟩ | ⟨rfl, hf⟩
  · have hf1 : 1 ≤ f := hyp.amalgam.model.2.1
    obtain rfl : f = 1 := by omega
    exact hrest .G2 1 E Gp M₁ M₂ Y β M ε z hyp hL43 (burnsideF4m_top_G2two hyp.amalgam)
      (Or.inl ⟨rfl, rfl⟩)
  · exact burnsideF4r_A42_D4 hyp hf
  · exact burnsideF4r_A42_U4 hyp hf hodd
  · have hf1 : 1 ≤ f := hyp.amalgam.model.2.1
    obtain rfl : f = 1 := by omega
    exact hrest .U5 1 E Gp M₁ M₂ Y β M ε z hyp hL43
      (burnsideF4r_top_of_odd_sq hyp.amalgam.normal
        (burnsideF4m_u5_sq_mem hyp.amalgam.toHypF_4_4g) hodd)
      (Or.inr ⟨rfl, rfl⟩)

end Final

end CFSG.ASVolI
