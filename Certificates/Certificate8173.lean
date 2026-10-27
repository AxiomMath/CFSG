module

public import CFSG.RankThree.PartTwo.Toolkit.Statements
public import CFSG.RankThree.PartTwo.Toolkit.Cocycle
public import CFSG.RankThree.PartTwo.Toolkit.H1Inputs
import CFSG.LinearAlgebra.LinearGroups.SLThreeRootGeneration

public section

open Matrix CFSG.RankThree.PartTwo.Toolkit CFSG.RankThree.PartTwo.Toolkit.Raw

namespace CertificateChecks.Batch8173

open Matrix CFSG.RankThree.PartTwo.Toolkit CFSG.RankThree.PartTwo.Toolkit.Raw

@[expose] def w12 : Word := [(true, 1), (false, 1), (true, 2)]

@[expose] def w20 : Word := [(true, 2), (false, 1), (true, 1)]

@[expose] def w02 : Word := [(false, 1)] ++ w12 ++ [(false, 2)] ++ w12 ++ w12

@[expose] def rootWords : List Word :=
  let ws : List Word := [[(false, 1)], w12, w20, w02, [(true, 1)] ++ w02 ++ [(true, 2)],
    [(true, 2)] ++ w02 ++ [(true, 1)]]
  [] :: ws ++ ws.map fun w => w ++ w

theorem cover : ∀ i j : Fin 3, ∀ t : ZMod 3, ∀ h : i ≠ j, ∃ w ∈ rootWords,
    ofMat (SpecialLinearGroup.transvection h t : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
      evalRaw (ofMat (slA : Matrix (Fin 3) (Fin 3) (ZMod 3)))
        (ofMat (slB : Matrix (Fin 3) (Fin 3) (ZMod 3))) w := by
  decide +kernel

theorem evalWord_mem (w : Word) : evalWord slA slB w ∈
    Subgroup.closure {y : SpecialLinearGroup (Fin 3) (ZMod 3) | y ∈ [slA, slB]} := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons p w ih =>
    obtain ⟨s, e⟩ := p
    rw [evalWord]
    refine Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure ?_) _) ih
    cases s <;> simp

end CertificateChecks.Batch8173

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Toolkit
  CFSG.RankThree.PartTwo.Toolkit.Raw Subgroup in
open scoped Matrix in
theorem certificate8173 : Subgroup.closure {y : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) | y ∈ [slA, slB]} = ⊤ := by
  apply CFSG.LinearAlgebra.SLThreeRootGeneration.closure_transvections_eq_top
  intro i j hij t
  obtain ⟨w, -, hw⟩ := CertificateChecks.Batch8173.cover i j t hij
  have e : SpecialLinearGroup.transvection hij t = evalWord slA slB w :=
    Subtype.ext (ofMat_injective (by rw [hw, ofMat_evalWord_SL]))
  rw [e]
  exact CertificateChecks.Batch8173.evalWord_mem w

end Certificates
