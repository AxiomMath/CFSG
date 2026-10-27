module

public import CFSG.LocalAnalysis.StandardType.GGK0LCDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcove

public section

namespace CFSG.StandardType.GGK0LC

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem kacBox_E8 : KacBox .E8 := by
  have hhr : ∀ i : Fin Tag.E8.rank,
      (hr .E8 i : ℤ) = CFSG.HardMathSupport.Timmesfeld.CrossChar.kacE8.θ i := by
    intro i
    fin_cases i <;> rfl
  have hθ : theta .E8 = CFSG.HardMathSupport.Timmesfeld.CrossChar.kacE8.θ :=
    funext fun i => hhr i
  have facts := CFSG.HardMathSupport.Timmesfeld.CrossChar.facts_E8
  refine ⟨?_, ?_, ?_⟩
  · intro γ hγ i
    rcases hγ.nonneg_or_nonpos with hn | hp
    · constructor
      · have h1 : 0 ≤ γ i := hn i
        have h2 : 0 < CFSG.HardMathSupport.Timmesfeld.CrossChar.kacE8.θ i := facts.θ_pos i
        linarith [hhr i]
      · have h := facts.le_θ γ hγ hn i
        linarith [hhr i]
    · constructor
      · have h := facts.le_θ (-γ) (IsRoot.neg hγ) (fun j => by
          have hj : γ j ≤ 0 := hp j
          show (0 : ℤ) ≤ -γ j
          linarith) i
        simp only [Pi.neg_apply] at h
        linarith [hhr i]
      · have h1 : γ i ≤ 0 := hp i
        have h2 : 0 < CFSG.HardMathSupport.Timmesfeld.CrossChar.kacE8.θ i := facts.θ_pos i
        linarith [hhr i]
  · rw [hθ]
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.kacE8.isRoot_θ
  · intro i
    fin_cases i <;> decide

theorem kacCentred_E8 : KacCentred .E8 1 := by
  refine ⟨!![4, 5, 7, 10, 8, 6, 4, 2;
            5, 8, 10, 15, 12, 9, 6, 3;
            7, 10, 14, 20, 16, 12, 8, 4;
            10, 15, 20, 30, 24, 18, 12, 6;
            8, 12, 16, 24, 20, 15, 10, 5;
            6, 9, 12, 18, 15, 12, 8, 4;
            4, 6, 8, 12, 10, 8, 6, 3;
            2, 3, 4, 6, 5, 4, 3, 2], ?_, ?_⟩
  · decide +kernel
  · intro i hi
    fin_cases i <;> (exfalso; exact absurd hi (by decide))

end CFSG.StandardType.GGK0LC

end
