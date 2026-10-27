module

public import CFSG.RankThree.PartOne.KS.LyFiveInputs
public import CFSG.Sporadic.Schreier.LySeven
public import CFSG.Sporadic.Schreier.LySevenRep

public section

namespace CFSG.RankThree.PartOne.LyFive

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier
  CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.RankThree.Native Matrix

theorem repM_classT (τ : List ℤ) :
    RepM (classT τ) (evalWord seedFam τ) :=
  repM_evalWordM repM_seedM repM_seedMInv τ

theorem classOK_facts
    {w : Mat} {wJ : J} (hw : RepM w wJ) {τ : List ℤ} {N : ℕ}
    {closed : Bool} (h : classOK w τ N closed = true) :
    ∃ (root : Array ℕ) (T : Array (Array ℕ) × Array ℕ × Array ℕ),
      mat7 root = restr7 ((evalWord seedFam τ)⁻¹ * wJ * evalWord seedFam τ) ∧
      conjTreeOK root (hGenPairs asArr) T = true ∧ 0 < N ∧ N ≤ T.1.size ∧
      (closed = true → conjClosedOK (hGenPairs asArr) T = true ∧ T.1.size = N) := by
  unfold classOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hinv, htree⟩, hN0⟩, hNle⟩, hcl⟩ := h
  have ht := repM_classT τ
  have hti := ht.inv_of_check hinv
  have hRep := (hti.mul hw).mul ht
  refine ⟨classR w τ, classTree w τ N, mat7_restrArr hRep, htree, hN0, hNle, fun hc => ?_⟩
  rcases hcl with h | h
  · rw [h] at hc; exact absurd hc (by decide)
  · exact h

end CFSG.RankThree.PartOne.LyFive
