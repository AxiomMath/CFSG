module

public import CFSG.Quasithin.Recognition.CertF8
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin

abbrev w183finM2 := Matrix (Fin 2) (Fin 2) GF8

@[expose] def w183finU (s : GF8) : w183finM2 := !![1, s; 0, 1]

@[expose] def w183finL (t : GF8) : w183finM2 := !![1, 0; t, 1]

@[expose] def w183finMulM2 (X Y : w183finM2) : w183finM2 :=
  Matrix.of fun i j => X i 0 * Y 0 j + X i 1 * Y 1 j

private theorem w183finMulM2_eq (X Y : w183finM2) : w183finMulM2 X Y = X * Y := by
  ext i j
  simp [w183finMulM2, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def w183finEvalM (g : Fin 4 → w183finM2) (w : List (Fin 4)) : w183finM2 :=
  w.foldl (fun X i => w183finMulM2 X (g i)) 1

@[expose] def w183finEvalW (g : Fin 4 → w183finM2) (w : List (Fin 4)) : w183finM2 :=
  w.foldl (fun X i => X * g i) 1

private theorem w183finEvalM_eq (g : Fin 4 → w183finM2) (w : List (Fin 4)) :
    w183finEvalM g w = w183finEvalW g w := by
  unfold w183finEvalM w183finEvalW
  suffices h : ∀ X : w183finM2, w.foldl (fun Y i => w183finMulM2 Y (g i)) X =
      w.foldl (fun Y i => Y * g i) X by simpa using h 1
  intro X
  induction w generalizing X with
  | nil => rfl
  | cons i w ih => simp only [List.foldl_cons]; rw [w183finMulM2_eq]; exact ih _

@[expose] def w183finWords : List (List (Fin 4)) :=
  [[2,0,2,1,2,1,2,0,2],
   [2,1,2,0,2,0,2,1,2],
   [3,0,3,1,3,1,3,0,3],
   [3,1,3,0,3,0,3,1,3],
   [2,0,3,0,2],
   [2,1,3,1,2],
   [2,0,1,3,0,1,2],
   [3,0,2,3,1,2,3,0,3],
   [3,1,2,3,0,2,3,1,3],
   [3,0,2,0,3],
   [3,1,2,1,3],
   [2,0,2,3,0,2,3,0,2],
   [2,1,2,3,0,2,3,1,2],
   [2,0,3,0,3,0,3,0,2],
   [2,1,3,1,3,1,3,1,2],
   [3,0,2,0,2,0,2,0,3],
   [3,1,2,1,2,1,2,1,3]]

private def w183finCodes : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

private theorem w183finCodes_mem (i : Fin 8) : i ∈ w183finCodes := by
  fin_cases i <;> decide

private def w183finGood (a₁ a₂ b₁ b₂ : GF8) : Bool :=
  w183finWords.any fun w => w183finCodes.any fun i =>
    decide ((⟨i⟩ : GF8) ≠ 0 ∧ (⟨i⟩ : GF8) ≠ a₁ ∧ (⟨i⟩ : GF8) ≠ a₂ ∧
      (⟨i⟩ : GF8) ≠ a₁ + a₂ ∧
      w183finEvalM ![w183finU a₁, w183finU a₂, w183finL b₁, w183finL b₂] w =
        w183finU (⟨i⟩ : GF8))

private def w183finKeyCheck : Bool :=
  w183finCodes.all fun i₁ => w183finCodes.all fun i₂ => w183finCodes.all fun i₃ =>
    w183finCodes.all fun i₄ =>
      decide ((⟨i₁⟩ : GF8) = 0) || decide ((⟨i₂⟩ : GF8) = 0) ||
      decide ((⟨i₁⟩ : GF8) = (⟨i₂⟩ : GF8)) || decide ((⟨i₃⟩ : GF8) = 0) ||
      decide ((⟨i₄⟩ : GF8) = 0) || decide ((⟨i₃⟩ : GF8) = (⟨i₄⟩ : GF8)) ||
      w183finGood (⟨i₁⟩ : GF8) (⟨i₂⟩ : GF8) (⟨i₃⟩ : GF8) (⟨i₄⟩ : GF8)

private theorem w183finKeyCheck_eq_true : w183finKeyCheck = true := by decide +kernel

private theorem w183finGood_spec {a₁ a₂ b₁ b₂ : GF8} (h : w183finGood a₁ a₂ b₁ b₂ = true) :
    ∃ w ∈ w183finWords, ∃ c : GF8, c ≠ 0 ∧ c ≠ a₁ ∧ c ≠ a₂ ∧ c ≠ a₁ + a₂ ∧
      w183finEvalW ![w183finU a₁, w183finU a₂, w183finL b₁, w183finL b₂] w = w183finU c := by
  simp only [w183finGood, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨w, hw, i, -, hconj⟩ := h
  obtain ⟨hc0, hc1, hc2, hc3, hw'⟩ := hconj
  exact ⟨w, hw, ⟨i⟩, hc0, hc1, hc2, hc3, by rw [← w183finEvalM_eq]; exact hw'⟩

theorem w183finKey : ∀ a₁ a₂ b₁ b₂ : GF8, a₁ ≠ 0 → a₂ ≠ 0 → a₁ ≠ a₂ → b₁ ≠ 0 → b₂ ≠ 0 →
    b₁ ≠ b₂ → ∃ w ∈ w183finWords, ∃ c : GF8, c ≠ 0 ∧ c ≠ a₁ ∧ c ≠ a₂ ∧ c ≠ a₁ + a₂ ∧
      w183finEvalW ![w183finU a₁, w183finU a₂, w183finL b₁, w183finL b₂] w = w183finU c := by
  intro a₁ a₂ b₁ b₂ ha₁ ha₂ ha₁₂ hb₁ hb₂ hb₁₂
  have hgood : w183finGood a₁ a₂ b₁ b₂ = true := by
    have h := w183finKeyCheck_eq_true
    simp only [w183finKeyCheck, List.all_eq_true] at h
    have h' := h a₁.val (w183finCodes_mem _) a₂.val (w183finCodes_mem _) b₁.val
      (w183finCodes_mem _) b₂.val (w183finCodes_mem _)
    simpa [ha₁, ha₂, ha₁₂, hb₁, hb₂, hb₁₂] using h'
  exact w183finGood_spec hgood

end CFSG.LocalAnalysis.WeakClosure81

end
