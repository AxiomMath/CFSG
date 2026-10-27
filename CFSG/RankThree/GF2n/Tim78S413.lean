module

public import CFSG.RankThree.GF2n.Tim78S412Core
public import CFSG.RankThree.GF2n.Tim78S4Closing

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

section Root

theorem comm_T_le_B_of_outer (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hRT : RootTypeStep M B) (h48 : Step48 M B P T) (h412 : Step412 M B P Q) {g : G}
    (hgM : conjSubgroup g B ≤ M) (hgP : ¬ conjSubgroup g B ≤ P) :
    ∀ a ∈ conjSubgroup g B, ∀ t ∈ T, ⁅a, t⁆ ∈ B := by
  intro a ha t ht
  by_cases ha1 : a = 1
  · rw [ha1, commutatorElement_one_left]
    exact B.one_mem
  rcases H.outer_pfull_or_tfull hCen hU hRT h48 hgM hgP ha with h | h
  · exact absurd ⟨a, mem_classD_of_mem_conjSubgroup ha ha1, hgM ha,
      H.outer_not_mem_Q hCen hU hgP ha ha1, h⟩ h412
  · exact h t ht

theorem conj_le_P_of_conj_le_M (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hRT : RootTypeStep M B) (h48 : Step48 M B P T) (h412 : Step412 M B P Q) :
    ∀ g : G, conjSubgroup g B ≤ M → conjSubgroup g B ≤ P := by
  intro g hgM
  by_contra hgP
  have hgM' : conjSubgroup g⁻¹ B ≤ M := H.conj_le_M_symm hgM
  have hgP' : ¬ conjSubgroup g⁻¹ B ≤ P := by
    intro h
    have := H.conj_inv_le_P_of_conj_le_P h
    rw [inv_inv] at this
    exact hgP this
  exact hgP (h48 g (H.hyp48_of_tfull hgM (H.comm_T_le_B_of_outer hCen hU hRT h48 h412 hgM hgP)
    (H.comm_T_le_B_of_outer hCen hU hRT h48 h412 hgM' hgP')))

theorem tim78_4_13_of_4_12 (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hRT : RootTypeStep M B) (h48 : Step48 M B P T) (h412 : Step412 M B P Q) :
    (∀ g : G, conjSubgroup g B ≤ M → conjSubgroup g B ≤ P) ∧
      (∀ b ∈ B, ∀ g : G, g * b * g⁻¹ ∈ M → g * b * g⁻¹ ∈ P) := by
  have h1 := H.conj_le_P_of_conj_le_M hCen hU hRT h48 h412
  refine ⟨h1, fun b hb g hgb => ?_⟩
  by_cases hb1 : b = 1
  · rw [hb1]
    simpa using P.one_mem
  have hgM : conjSubgroup g B ≤ M := hRT g b hb hb1 hgb
  have hmem : g * b * g⁻¹ ∈ conjSubgroup g B := by
    rw [mem_conjSubgroup, show g⁻¹ * (g * b * g⁻¹) * g = b by group]
    exact hb
  exact h1 g hgM hmem

theorem tim78_4_13 (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hRT : RootTypeStep M B) (h48 : Step48 M B P T) :
    (∀ g : G, conjSubgroup g B ≤ M → conjSubgroup g B ≤ P) ∧
      (∀ b ∈ B, ∀ g : G, g * b * g⁻¹ ∈ M → g * b * g⁻¹ ∈ P) :=
  H.tim78_4_13_of_4_12 hCen hU hRT h48 (H.tim78_4_12 hCen hU hRT h48)

theorem step413 (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hRT : RootTypeStep M B) (h48 : Step48 M B P T) : Step413 M B P :=
  (H.tim78_4_13 hCen hU hRT h48).2

end Root

end Hyp4

end CFSG.RankThree.GF2n.Tim78
