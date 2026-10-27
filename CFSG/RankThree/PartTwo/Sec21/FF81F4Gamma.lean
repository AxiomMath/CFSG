module

public import CFSG.RankThree.PartTwo.Sec21.FF81F4GammaCheck
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG.LieType.Simplicity.TitsBits CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree
open CFSG.RankThree.PartTwo.Sec4.Item434F42
open CFSG.RankThree.PartOne.SEITZX (codeBits wordOfCodes letterOfCode)

section Sound

variable
  {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem letterOfCode_flipCode {c : ℕ} (hc : c < 8) :
    letterOfCode (flipCode c) = (letterOfCode c).flip := by
  interval_cases c <;> rfl

theorem wordOfCodes_flip (w : List ℕ) (hw : ∀ c ∈ w, c < 8) :
    wordOfCodes (w.map flipCode) = (wordOfCodes w).map Letter.flip := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    simp only [wordOfCodes, List.map_cons] at ih ⊢
    rw [letterOfCode_flipCode (hw c (List.mem_cons_self ..)),
      ih (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc'))]

theorem finite_adj : Finite (adjointGroup ReeTag.F4.tag K) := by
  have : Finite (Module.End K (RootModule Tag.F4 K)) := Module.finite_of_finite K
  infer_instance

end Sound

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
