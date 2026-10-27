module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelBlocksInputs
public import CFSG.RankThree.Native.ONTripleMatSound

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

open CFSG.KC.Misc.F7 CFSG.KC.Loop CFSG.RankThree.Native.ONTriple

attribute [local irreducible] dotProduct

theorem ifB_true_right {c t : Bool} : ifB c t true = true ↔ (c = true → t = true) := by
  cases c <;> simp [ifB]

theorem nPt_eq : nPt = 122760 := rfl

theorem startOf_eq_ite (k : ℕ) : startOf k = if k < 1 then 0 else if k < 58654 then 1 else
    if k < 110790 then 58654 else if k < 116376 then 110790 else 116376 := by
  simp only [startOf, nIf_eq, Nat.blt_eq]

theorem startOf_of_le {k p : ℕ} (h1 : startOf k ≤ p) (h2 : p ≤ k) : startOf p = startOf k := by
  rw [startOf_eq_ite] at h1 ⊢
  rw [startOf_eq_ite]
  split_ifs at h1 ⊢ <;> omega

theorem orbStart_eq (o : ℕ) : orbStart o = [0, 1, 58654, 110790, 116376, 122760].getD o 0 :=
  nthN_eq _ _

theorem orbStart_succ_le {o : ℕ} (ho : o < 5) : orbStart (o + 1) ≤ nPt := by
  rw [orbStart_eq, nPt_eq]
  interval_cases o <;> simp

theorem startOf_of_mem {o k : ℕ} (ho : o < 5) (h1 : orbStart o ≤ k) (h2 : k < orbStart (o + 1)) :
    startOf k = orbStart o := by
  rw [orbStart_eq] at h1 h2 ⊢
  rw [startOf_eq_ite]
  interval_cases o <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at h1 h2 ⊢ <;>
    split_ifs <;> omega

@[expose] noncomputable def rangeOf (k : ℕ) : Fin 5 :=
  if k < 1 then 0 else if k < 58654 then 1 else if k < 110790 then 2 else
    if k < 116376 then 3 else 4

theorem rangeOf_mem {k : ℕ} (hk : k < nPt) :
    orbStart (rangeOf k) ≤ k ∧ k < orbStart ((rangeOf k : ℕ) + 1) := by
  rw [nPt_eq] at hk
  rw [rangeOf]
  split_ifs <;> simp only [orbStart_eq] <;> simp <;> omega

theorem rangeOf_eq {k : ℕ} {o : ℕ} (ho : o < 5) (h1 : orbStart o ≤ k)
    (h2 : k < orbStart (o + 1)) : (rangeOf k : ℕ) = o := by
  rw [orbStart_eq] at h1 h2
  rw [rangeOf]
  interval_cases o <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at h1 h2 <;>
    split_ifs <;> first | rfl | omega

theorem exists_range {k : ℕ} (hk : k < nPt) :
    ∃ o < 5, orbStart o ≤ k ∧ k < orbStart (o + 1) :=
  ⟨rangeOf k, (rangeOf k).isLt, rangeOf_mem hk⟩

@[expose] noncomputable def ptMat (k : ℕ) : Matrix (Fin 8) (Fin 45) (ZMod 7) := decC 8 (ptCode k)

@[expose] noncomputable def ptS (k : ℕ) : Sub7 := rowSpan (ptMat k)

theorem ptS_eq (k : ℕ) : ptS k = rowSpan (ptMat k) := rfl

@[expose] noncomputable def letU (s : ℕ) : Mat45ˣ :=
  if h : s / 2 < 8 then (if s % 2 = 0 then (gM ⟨s / 2, h⟩)⁻¹ else gM ⟨s / 2, h⟩) else 1

@[expose] noncomputable def resW (g : Mat45) : Matrix (Fin 8) (Fin 8) (ZMod 7) :=
  fun i c => (ptMat 0 * g) i (Fin.castLE (by norm_num) c)

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37
