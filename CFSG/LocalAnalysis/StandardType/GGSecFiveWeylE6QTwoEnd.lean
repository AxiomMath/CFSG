module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoBridgeDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoEndExc
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoEndLabel
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoEndRows
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoEndU5

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggSecFiveE6QTwoEndInput_of_inputs
    (hRk1 : GGSecFiveRk1PhanInput) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hW : GGTBTorWRows) (hLift : GGTBTorLiftRows) :
    GGSecFiveE6QTwoEndInput := by
  intro G _ _ B Bs x L D J _ _ hC
  have hC_copy := hC
  obtain ⟨𝒦, hR, hNS, ι, M, e, hP, ⟨e', hM⟩, r, hrA, hrC, hr6⟩ := hC_copy
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := GGIsWeylMatrixE.le_three (Or.inl ⟨e', hM⟩)
  have hlab := ggL_baseLabel_qTwo_of_rk1 hRk1 hR hNS hP hle3 hrA hrC hr6
  have hU : GGInnerDiagOnLabel (fun p lab =>
      (((lab.tag = .twA ∧ lab.rank = 5) ∨ (lab.tag = .D ∧ lab.rank = 4) ∨
          (lab.tag = .twD ∧ lab.rank = 5)) ∧ lab.n = 1) ∨
        (∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
          GGTBTorRowAt p lab r m N C M ∧ (N ≤ 3 ∨ ¬ Nat.card M.Group ∣ 51840)) ∨
        (lab.tag = .twA ∧ lab.rank = 4 ∧ lab.n = 1) ∨ GGF4ThreeLabel p lab ∨
        GGTwE6BadLabel p lab) 3 Bs L := by
    refine GGInnerDiagOnLabel.mono' ?_ hlab
    intro lab hS
    obtain ⟨hn, hrows⟩ := hS
    rcases hrows with h1 | h2 | h3 | ⟨_, h4⟩
    · exact E6QTwo.endLabel_cases hn (Or.inl h1)
    · exact E6QTwo.endLabel_cases hn (Or.inr (Or.inl h2))
    · exact E6QTwo.endLabel_cases hn (Or.inr (Or.inr (Or.inl h3)))
    · exact E6QTwo.endLabel_cases hn (Or.inr (Or.inr (Or.inr h4)))
  rcases GGInnerDiagOnLabel.elim_or hU with hA | hBCDE
  · exact GGInnerDiagOnLabel.toMarking hA
  · rcases GGInnerDiagOnLabel.elim_or hBCDE with hB | hCDE
    · exact (GGSecFiveE6QTwoCfg.false_of_endRow hW hLift hTBF hC
        (GGInnerDiagOnLabel.mono' (fun _ h => h) hB)).elim
    · rcases GGInnerDiagOnLabel.elim_or hCDE with hC' | hDE
      · exact (GGSecFiveE6QTwoCfg.false_of_twA4 hW hLift hTBF hC
          (GGInnerDiagOnLabel.mono' (fun _ h => h) hC')).elim
      · rcases GGInnerDiagOnLabel.elim_or hDE with hD | hE
        · exact (GGSecFiveE6QTwoCfg.false_of_f4 hC
            (GGInnerDiagOnLabel.mono' (fun _ h => h) hD)).elim
        · exact (GGSecFiveE6QTwoCfg.false_of_twE6 hTBF hWI hC
            (GGInnerDiagOnLabel.mono' (fun _ h => h) hE)).elim

end CFSG.StandardType

end
