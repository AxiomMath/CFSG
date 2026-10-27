module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Step1
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Step2
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Step3
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136MoveIrr
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Two
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136ConclB

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

variable {W : Type} [CommGroup W] [Finite W]

theorem case_fix_irr (h135 : W4Lem13_5) (hw2 : ∀ w : W, w ^ 2 = 1)
    {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)} (c : Ctx136 Y t L)
    (hfix : ∀ I ∈ irrSet L, I.map t.toMonoidHom = I) :
    ∃ L' : Subgroup (MulAut W), Conc4_136W Y t L' := by
  rcases case_T_or_two hw2 c hfix with hT | h2
  · exact ⟨L, case_T_conc h135 hw2 c hfix hT⟩
  · exact h2

theorem w4Lem13_6_of_inputs (h133N : R4_133N) (h134 : W4Lem13_4) (h135 : W4Lem13_5) :
    W4Lem13_6 := by
  apply w4Lem13_6_of_std
  intro W _ _ hw2 Y t S
  by_cases h1 : ∃ p : ℕ, p.Prime ∧ ⁅pCoreOf p Y, Subgroup.zpowers t⁆ ≠ ⊥
  · obtain ⟨p, hp, hne⟩ := h1
    exact step1 h133N hw2 S hp hne
  simp only [not_exists, not_and, not_not] at h1
  by_cases h2 : ∃ K : Subgroup (MulAut W), IsComponentOf K Y ∧
      K.map (MulAut.conj t).toMonoidHom ≠ K
  · obtain ⟨K, hK, hmove⟩ := h2
    exact step2 h134 hw2 S hK hmove
  simp only [not_exists, not_and, not_not] at h2
  obtain ⟨L, hL, hLt⟩ := exists_component_comm hw2 S h1 h2
  have c : Ctx136 Y t L := ⟨S, hL, hLt, h1, h2⟩
  by_cases h3 : ∃ I ∈ irrSet L, I.map t.toMonoidHom ≠ I
  · exact ⟨L, case_move_irr hw2 c h3⟩
  · simp only [not_exists, not_and, not_not] at h3
    exact case_fix_irr h135 hw2 c h3

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
