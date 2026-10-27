module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameE78Facts
import CFSG.LocalAnalysis.StandardType.GGFrameE78Refl
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Index
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly

variable {G : Type} [Group G]

private def glue0rAux_w (n : ℕ) (l : List (Fin n)) : FEMat n :=
  (l.map (feS n)).prod

@[simp] private theorem glue0rAux_w_nil (n : ℕ) : glue0rAux_w n [] = 1 := rfl

@[simp] private theorem glue0rAux_w_cons (n : ℕ) (i : Fin n) (l : List (Fin n)) :
    glue0rAux_w n (i :: l) = feS n i * glue0rAux_w n l := by
  simp [glue0rAux_w]

private theorem glue0rAux_w_append (n : ℕ) (l₁ l₂ : List (Fin n)) :
    glue0rAux_w n (l₁ ++ l₂) = glue0rAux_w n l₁ * glue0rAux_w n l₂ := by
  simp [glue0rAux_w, List.map_append, List.prod_append]

private theorem glue0rAux_w_reverse_mul (n : ℕ) (l : List (Fin n)) :
    glue0rAux_w n l.reverse * glue0rAux_w n l = 1 := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [List.reverse_cons, glue0rAux_w_append]
      simp only [glue0rAux_w_cons, glue0rAux_w_nil, mul_one]
      calc (glue0rAux_w n l.reverse * feS n i) * (feS n i * glue0rAux_w n l)
          = glue0rAux_w n l.reverse * (feS n i * feS n i) * glue0rAux_w n l := by
              noncomm_ring
        _ = glue0rAux_w n l.reverse * glue0rAux_w n l := by rw [feS_mul_self, mul_one]
        _ = 1 := ih

private theorem glue0rAux_w_mul_reverse (n : ℕ) (l : List (Fin n)) :
    glue0rAux_w n l * glue0rAux_w n l.reverse = 1 := by
  simpa using glue0rAux_w_reverse_mul n l.reverse

private theorem glue0rAux_normal (n : ℕ) {t : FEMat n} (ht : FEConjDer n t) :
    ∃ (l : List (Fin n)) (i : Fin n),
      t = glue0rAux_w n l * feS n i * glue0rAux_w n l.reverse := by
  induction ht with
  | base i => exact ⟨[], i, by simp⟩
  | conj j _ ih =>
      obtain ⟨l, i, rfl⟩ := ih
      refine ⟨j :: l, i, ?_⟩
      rw [List.reverse_cons, glue0rAux_w_append]
      simp only [glue0rAux_w_cons, glue0rAux_w_nil, mul_one]
      noncomm_ring

private theorem glue0rAux_root_line (n : ℕ) {t : FEMat n} (ht : t ∈ feT n) {v : FEVec n}
    (hv0 : v ≠ 0) (htv : t.mulVec v = -v) :
    ∃ (l : List (Fin n)) (i : Fin n) (c : ZMod 3), c ≠ 0 ∧
      v = c • (glue0rAux_w n l).mulVec (feCol n i) := by
  obtain ⟨l, i, ht_eq⟩ := glue0rAux_normal n (show FEConjDer n t from ht)
  set y : FEVec n := (glue0rAux_w n l.reverse).mulVec v with hy
  set c : ZMod 3 := 2 * y i with hcdef
  have hw1 : glue0rAux_w n l * glue0rAux_w n l.reverse = 1 := glue0rAux_w_mul_reverse n l
  have hw2 : glue0rAux_w n l.reverse * glue0rAux_w n l = 1 := glue0rAux_w_reverse_mul n l
  have hbase : (glue0rAux_w n l).mulVec ((feS n i).mulVec y) = -v := by
    have h := htv
    rw [ht_eq] at h
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h
    simpa [hy] using h
  have hsy : (feS n i).mulVec y = -y := by
    have h := congrArg (fun z => (glue0rAux_w n l.reverse).mulVec z) hbase
    rw [Matrix.mulVec_mulVec, hw2, Matrix.one_mulVec] at h
    have h' : (feS n i).mulVec y = - ((glue0rAux_w n l.reverse).mulVec v) := by
      calc (feS n i).mulVec y = (glue0rAux_w n l.reverse).mulVec (-v) := h
        _ = - ((glue0rAux_w n l.reverse).mulVec v) := Matrix.mulVec_neg v _
    simpa [hy] using h'
  have hc : y = c • feCol n i := by
    simpa [hcdef] using feS_neg_line n i y hsy
  have hv_eq : v = c • (glue0rAux_w n l).mulVec (feCol n i) := by
    calc v = (glue0rAux_w n l).mulVec y := by
            rw [hy, Matrix.mulVec_mulVec, hw1, Matrix.one_mulVec]
      _ = (glue0rAux_w n l).mulVec (c • feCol n i) := by rw [hc]
      _ = c • (glue0rAux_w n l).mulVec (feCol n i) := Matrix.mulVec_smul _ _ _
  refine ⟨l, i, c, ?_, hv_eq⟩
  intro hc0
  apply hv0
  rw [hv_eq, hc0, zero_smul]

private theorem glue0rAux_feRow_self (n : ℕ) (i : Fin n) : feRow n i i = 1 := by
  have h := feRow_dot n i (Pi.single i 1)
  simpa using h

private theorem glue0rAux_feCol_entry (n : ℕ) (p i : Fin n) :
    feCol n i p = (if p = i then 1 else 0) - feS n i p i := by
  rw [feS_eq]
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply]
  rw [glue0rAux_feRow_self]
  ring

private theorem glue0rAux_colWord7_0 :
    (glue0rAux_w 7 []).mulVec (feCol 7 0) = feCol 7 0 := by
  simp only [glue0rAux_w_nil, Matrix.one_mulVec]

private theorem glue0rAux_colWord7_1 :
    (glue0rAux_w 7 [3, 1, 2, 3, 0, 2]).mulVec (feCol 7 0) = feCol 7 1 := by
  simp only [glue0rAux_w_cons, glue0rAux_w_nil, mul_one,
    ← Matrix.mulVec_mulVec, feS_mulVec]
  try
    ext p
    simp only [glue0rAux_feCol_entry, Pi.sub_apply, Pi.smul_apply]
    fin_cases p <;> decide +kernel

private theorem glue0rAux_colWord7_2 :
    (glue0rAux_w 7 [0, 2]).mulVec (feCol 7 0) = feCol 7 2 := by
  simp only [glue0rAux_w_cons, glue0rAux_w_nil, mul_one,
    ← Matrix.mulVec_mulVec, feS_mulVec]
  try
    ext p
    simp only [glue0rAux_feCol_entry, Pi.sub_apply, Pi.smul_apply]
    fin_cases p <;> decide +kernel

private theorem glue0rAux_colWord7_3 :
    (glue0rAux_w 7 [2, 3, 0, 2]).mulVec (feCol 7 0) = feCol 7 3 := by
  simp only [glue0rAux_w_cons, glue0rAux_w_nil, mul_one,
    ← Matrix.mulVec_mulVec, feS_mulVec]
  try
    ext p
    simp only [glue0rAux_feCol_entry, Pi.sub_apply, Pi.smul_apply]
    fin_cases p <;> decide +kernel

private theorem glue0rAux_colWord7_4 :
    (glue0rAux_w 7 [3, 4, 2, 3, 0, 2]).mulVec (feCol 7 0) = feCol 7 4 := by
  simp only [glue0rAux_w_cons, glue0rAux_w_nil, mul_one,
    ← Matrix.mulVec_mulVec, feS_mulVec]
  try
    ext p
    simp only [glue0rAux_feCol_entry, Pi.sub_apply, Pi.smul_apply]
    fin_cases p <;> decide +kernel

private theorem glue0rAux_colWord7_5 :
    (glue0rAux_w 7 [4, 5, 3, 4, 2, 3, 0, 2]).mulVec (feCol 7 0) = feCol 7 5 := by
  simp only [glue0rAux_w_cons, glue0rAux_w_nil, mul_one,
    ← Matrix.mulVec_mulVec, feS_mulVec]
  try
    ext p
    simp only [glue0rAux_feCol_entry, Pi.sub_apply, Pi.smul_apply]
    fin_cases p <;> decide +kernel

private theorem glue0rAux_colWord7_6 :
    (glue0rAux_w 7 [5, 6, 4, 5, 3, 4, 2, 3, 0, 2]).mulVec (feCol 7 0) = feCol 7 6 := by
  simp only [glue0rAux_w_cons, glue0rAux_w_nil, mul_one,
    ← Matrix.mulVec_mulVec, feS_mulVec]
  try
    ext p
    simp only [glue0rAux_feCol_entry, Pi.sub_apply, Pi.smul_apply]
    fin_cases p <;> decide +kernel

private theorem glue0rAux_colWord8_0 :
    (glue0rAux_w 8 []).mulVec (feCol 8 0) = feCol 8 0 := by
  simp only [glue0rAux_w_nil, Matrix.one_mulVec]

private theorem glue0rAux_colWord8_1 :
    (glue0rAux_w 8 [3, 1, 2, 3, 0, 2]).mulVec (feCol 8 0) = feCol 8 1 := by
  simp only [glue0rAux_w_cons, glue0rAux_w_nil, mul_one,
    ← Matrix.mulVec_mulVec, feS_mulVec]
  try
    ext p
    simp only [glue0rAux_feCol_entry, Pi.sub_apply, Pi.smul_apply]
    fin_cases p <;> decide +kernel

private theorem glue0rAux_colWord8_2 :
    (glue0rAux_w 8 [0, 2]).mulVec (feCol 8 0) = feCol 8 2 := by
  simp only [glue0rAux_w_cons, glue0rAux_w_nil, mul_one,
    ← Matrix.mulVec_mulVec, feS_mulVec]
  try
    ext p
    simp only [glue0rAux_feCol_entry, Pi.sub_apply, Pi.smul_apply]
    fin_cases p <;> decide +kernel

private theorem glue0rAux_colWord8_3 :
    (glue0rAux_w 8 [2, 3, 0, 2]).mulVec (feCol 8 0) = feCol 8 3 := by
  simp only [glue0rAux_w_cons, glue0rAux_w_nil, mul_one,
    ← Matrix.mulVec_mulVec, feS_mulVec]
  try
    ext p
    simp only [glue0rAux_feCol_entry, Pi.sub_apply, Pi.smul_apply]
    fin_cases p <;> decide +kernel

private theorem glue0rAux_colWord8_4 :
    (glue0rAux_w 8 [3, 4, 2, 3, 0, 2]).mulVec (feCol 8 0) = feCol 8 4 := by
  simp only [glue0rAux_w_cons, glue0rAux_w_nil, mul_one,
    ← Matrix.mulVec_mulVec, feS_mulVec]
  try
    ext p
    simp only [glue0rAux_feCol_entry, Pi.sub_apply, Pi.smul_apply]
    fin_cases p <;> decide +kernel

private theorem glue0rAux_colWord8_5 :
    (glue0rAux_w 8 [4, 5, 3, 4, 2, 3, 0, 2]).mulVec (feCol 8 0) = feCol 8 5 := by
  simp only [glue0rAux_w_cons, glue0rAux_w_nil, mul_one,
    ← Matrix.mulVec_mulVec, feS_mulVec]
  try
    ext p
    simp only [glue0rAux_feCol_entry, Pi.sub_apply, Pi.smul_apply]
    fin_cases p <;> decide +kernel

private theorem glue0rAux_colWord8_6 :
    (glue0rAux_w 8 [5, 6, 4, 5, 3, 4, 2, 3, 0, 2]).mulVec (feCol 8 0) = feCol 8 6 := by
  simp only [glue0rAux_w_cons, glue0rAux_w_nil, mul_one,
    ← Matrix.mulVec_mulVec, feS_mulVec]
  try
    ext p
    simp only [glue0rAux_feCol_entry, Pi.sub_apply, Pi.smul_apply]
    fin_cases p <;> decide +kernel

private theorem glue0rAux_colWord8_7 :
    (glue0rAux_w 8 [6, 7, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2]).mulVec (feCol 8 0) = feCol 8 7 := by
  simp only [glue0rAux_w_cons, glue0rAux_w_nil, mul_one,
    ← Matrix.mulVec_mulVec, feS_mulVec]
  try
    ext p
    simp only [glue0rAux_feCol_entry, Pi.sub_apply, Pi.smul_apply]
    fin_cases p <;> decide +kernel

private abbrev glue0rAux_theta7 : FEVec 7 := Pi.single (0:Fin 7) 1
private abbrev glue0rAux_theta8 : FEVec 8 := Pi.single (7:Fin 8) 1
private abbrev glue0rAux_lTheta7 : List (Fin 7) :=
  [0,2,3,4,5,6,1,3,4,5,2,3,4,1,3,2]
private abbrev glue0rAux_lTheta8 : List (Fin 8) :=
  [7,6,5,4,3,2,1,3,4,5,6,7,0,2,3,4,5,6,1,3,4,5,2,3,4,1,3,2]

private theorem glue0rAux_theta7_spec :
    (glue0rAux_w 7 glue0rAux_lTheta7).mulVec (feCol 7 0) = glue0rAux_theta7 := by
  simp only [glue0rAux_w_cons, glue0rAux_w_nil, mul_one,
    ← Matrix.mulVec_mulVec, feS_mulVec]
  ext p
  simp only [glue0rAux_feCol_entry, Pi.sub_apply, Pi.smul_apply, Pi.single_apply]
  fin_cases p <;> decide +kernel

private theorem glue0rAux_theta8_spec :
    (glue0rAux_w 8 glue0rAux_lTheta8).mulVec (feCol 8 0) = glue0rAux_theta8 := by
  simp only [glue0rAux_w_cons, glue0rAux_w_nil, mul_one,
    ← Matrix.mulVec_mulVec, feS_mulVec]
  ext p
  simp only [glue0rAux_feCol_entry, Pi.sub_apply, Pi.smul_apply, Pi.single_apply]
  fin_cases p <;> decide +kernel

private theorem glue0rAux_theta_rev {n : ℕ} {theta : FEVec n} {l : List (Fin n)}
    (i0 : Fin n) (h : (glue0rAux_w n l).mulVec (feCol n i0) = theta) :
    (glue0rAux_w n l.reverse).mulVec theta = feCol n i0 := by
  have h' := congrArg (fun v => (glue0rAux_w n l.reverse).mulVec v) h
  rw [Matrix.mulVec_mulVec, glue0rAux_w_reverse_mul, Matrix.one_mulVec] at h'
  exact h'.symm

private theorem glue0rAux_w_col_from_theta {n : ℕ} {theta : FEVec n}
    (i0 : Fin n) {lrev l : List (Fin n)} {i : Fin n}
    (hrev : (glue0rAux_w n lrev).mulVec theta = feCol n i0)
    (hcol : (glue0rAux_w n l).mulVec (feCol n i0) = feCol n i) :
    (glue0rAux_w n (l ++ lrev)).mulVec theta = feCol n i := by
  rw [glue0rAux_w_append, ← Matrix.mulVec_mulVec, hrev, hcol]

private theorem glue0rAux_w_neg_theta {n : ℕ} {theta : FEVec n} {l : List (Fin n)}
    (i0 : Fin n) (hθ : (glue0rAux_w n l).mulVec (feCol n i0) = theta) :
    (glue0rAux_w n (l ++ [i0] ++ l.reverse)).mulVec theta = -theta := by
  have hrev : (glue0rAux_w n l.reverse).mulVec theta = feCol n i0 :=
    glue0rAux_theta_rev i0 hθ
  have hC0 : (feS n i0).mulVec (feCol n i0) = -feCol n i0 := by
    rw [feS_mulVec, feCol_self, two_smul]
    abel
  calc (glue0rAux_w n (l ++ [i0] ++ l.reverse)).mulVec theta
      = (glue0rAux_w n l).mulVec ((feS n i0).mulVec
          ((glue0rAux_w n l.reverse).mulVec theta)) := by
          rw [glue0rAux_w_append, glue0rAux_w_append, glue0rAux_w_cons,
            glue0rAux_w_nil, mul_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    _ = (glue0rAux_w n l).mulVec ((feS n i0).mulVec (feCol n i0)) := by rw [hrev]
    _ = (glue0rAux_w n l).mulVec (-feCol n i0) := by rw [hC0]
    _ = - (glue0rAux_w n l).mulVec (feCol n i0) := Matrix.mulVec_neg _ _
    _ = -theta := by rw [hθ]

private theorem glue0rAux_root_word_theta {n : ℕ} {theta : FEVec n}
    (hcol : ∀ i : Fin n, ∃ l : List (Fin n), (glue0rAux_w n l).mulVec theta = feCol n i)
    {t : FEMat n} (ht : t ∈ feT n) {v : FEVec n} (hv0 : v ≠ 0)
    (htv : t.mulVec v = -v) :
    ∃ (l : List (Fin n)) (ε : ZMod 3), ε ≠ 0 ∧
      v = ε • (glue0rAux_w n l).mulVec theta := by
  obtain ⟨l, i, c, hc0, hv⟩ := glue0rAux_root_line n ht hv0 htv
  obtain ⟨li, hli⟩ := hcol i
  refine ⟨l ++ li, c, hc0, ?_⟩
  rw [hv, ← hli, Matrix.mulVec_mulVec, ← glue0rAux_w_append]

private theorem glue0rAux_col7_from_theta : ∀ i : Fin 7,
    ∃ l : List (Fin 7), (glue0rAux_w 7 l).mulVec glue0rAux_theta7 = feCol 7 i := by
  have hrev : (glue0rAux_w 7 glue0rAux_lTheta7.reverse).mulVec glue0rAux_theta7 =
      feCol 7 0 := glue0rAux_theta_rev 0 glue0rAux_theta7_spec
  intro i
  fin_cases i
  · exact ⟨[] ++ glue0rAux_lTheta7.reverse,
      glue0rAux_w_col_from_theta 0 hrev glue0rAux_colWord7_0⟩
  · exact ⟨[3,1,2,3,0,2] ++ glue0rAux_lTheta7.reverse,
      glue0rAux_w_col_from_theta 0 hrev glue0rAux_colWord7_1⟩
  · exact ⟨[0,2] ++ glue0rAux_lTheta7.reverse,
      glue0rAux_w_col_from_theta 0 hrev glue0rAux_colWord7_2⟩
  · exact ⟨[2,3,0,2] ++ glue0rAux_lTheta7.reverse,
      glue0rAux_w_col_from_theta 0 hrev glue0rAux_colWord7_3⟩
  · exact ⟨[3,4,2,3,0,2] ++ glue0rAux_lTheta7.reverse,
      glue0rAux_w_col_from_theta 0 hrev glue0rAux_colWord7_4⟩
  · exact ⟨[4,5,3,4,2,3,0,2] ++ glue0rAux_lTheta7.reverse,
      glue0rAux_w_col_from_theta 0 hrev glue0rAux_colWord7_5⟩
  · exact ⟨[5,6,4,5,3,4,2,3,0,2] ++ glue0rAux_lTheta7.reverse,
      glue0rAux_w_col_from_theta 0 hrev glue0rAux_colWord7_6⟩

private theorem glue0rAux_col8_from_theta : ∀ i : Fin 8,
    ∃ l : List (Fin 8), (glue0rAux_w 8 l).mulVec glue0rAux_theta8 = feCol 8 i := by
  have hrev : (glue0rAux_w 8 glue0rAux_lTheta8.reverse).mulVec glue0rAux_theta8 =
      feCol 8 0 := glue0rAux_theta_rev 0 glue0rAux_theta8_spec
  intro i
  fin_cases i
  · exact ⟨[] ++ glue0rAux_lTheta8.reverse,
      glue0rAux_w_col_from_theta 0 hrev glue0rAux_colWord8_0⟩
  · exact ⟨[3,1,2,3,0,2] ++ glue0rAux_lTheta8.reverse,
      glue0rAux_w_col_from_theta 0 hrev glue0rAux_colWord8_1⟩
  · exact ⟨[0,2] ++ glue0rAux_lTheta8.reverse,
      glue0rAux_w_col_from_theta 0 hrev glue0rAux_colWord8_2⟩
  · exact ⟨[2,3,0,2] ++ glue0rAux_lTheta8.reverse,
      glue0rAux_w_col_from_theta 0 hrev glue0rAux_colWord8_3⟩
  · exact ⟨[3,4,2,3,0,2] ++ glue0rAux_lTheta8.reverse,
      glue0rAux_w_col_from_theta 0 hrev glue0rAux_colWord8_4⟩
  · exact ⟨[4,5,3,4,2,3,0,2] ++ glue0rAux_lTheta8.reverse,
      glue0rAux_w_col_from_theta 0 hrev glue0rAux_colWord8_5⟩
  · exact ⟨[5,6,4,5,3,4,2,3,0,2] ++ glue0rAux_lTheta8.reverse,
      glue0rAux_w_col_from_theta 0 hrev glue0rAux_colWord8_6⟩
  · exact ⟨[6,7,5,6,4,5,3,4,2,3,0,2] ++ glue0rAux_lTheta8.reverse,
      glue0rAux_w_col_from_theta 0 hrev glue0rAux_colWord8_7⟩

private theorem glue0rAux_root7_word {t : FEMat 7} (ht : t ∈ feT 7) {v : FEVec 7}
    (hv0 : v ≠ 0) (htv : t.mulVec v = -v) :
    ∃ (l : List (Fin 7)) (ε : ZMod 3), ε ≠ 0 ∧
      v = ε • (glue0rAux_w 7 l).mulVec glue0rAux_theta7 :=
  glue0rAux_root_word_theta glue0rAux_col7_from_theta ht hv0 htv

private theorem glue0rAux_root8_word {t : FEMat 8} (ht : t ∈ feT 8) {v : FEVec 8}
    (hv0 : v ≠ 0) (htv : t.mulVec v = -v) :
    ∃ (l : List (Fin 8)) (ε : ZMod 3), ε ≠ 0 ∧
      v = ε • (glue0rAux_w 8 l).mulVec glue0rAux_theta8 :=
  glue0rAux_root_word_theta glue0rAux_col8_from_theta ht hv0 htv

private theorem glue0rAux_zmod_smul_mem {n : ℕ} (S : AddSubgroup (FEVec n)) {x : FEVec n}
    (hx : x ∈ S) (c : ZMod 3) : c • x ∈ S := by
  have h := AddSubgroup.nsmul_mem S hx c.val
  convert h using 1
  ext i
  simp

private abbrev glue0rAux_col (n : ℕ) (i : Fin n) : FEVec n :=
  fun p => (if p = i then 1 else 0) - feS n i p i

private theorem glue0rAux_col_eq_feCol (n : ℕ) (i : Fin n) :
    glue0rAux_col n i = feCol n i := by
  ext p
  rw [glue0rAux_feCol_entry]

private abbrev glue0rAux_basisCol (n : ℕ) (j k : Fin n) : FEVec n :=
  if k = j then Pi.single j 1 else glue0rAux_col n k

private abbrev glue0rAux_basis (n : ℕ) (j : Fin n) : FEMat n :=
  fun i k => glue0rAux_basisCol n j k i

private abbrev glue0rAux_inv7 : FEMat 7 :=
  !![1,1,0,2,0,1,2; 0,0,1,2,0,1,2; 0,1,0,2,0,1,2; 0,2,2,1,0,2,1;
     0,0,0,0,0,2,1; 0,1,1,2,2,2,1; 0,2,2,1,1,1,1]

private abbrev glue0rAux_inv8 : FEMat 8 :=
  !![2,2,0,1,0,2,1,0; 2,2,1,0,0,0,0,0; 0,1,0,2,0,1,2,0; 1,0,2,0,0,0,0,0;
     0,0,0,0,0,2,1,0; 2,0,1,0,2,1,2,0; 1,0,2,0,1,2,0,0; 1,0,2,0,1,2,0,1]

private theorem glue0rAux_basis7_mul_inv : glue0rAux_basis 7 0 * glue0rAux_inv7 = 1 := by
  decide +kernel

private theorem glue0rAux_basis8_mul_inv : glue0rAux_basis 8 7 * glue0rAux_inv8 = 1 := by
  decide +kernel

private theorem glue0rAux_mulVec_eq_sum {n : ℕ} (M : FEMat n) (v : FEVec n) :
    M.mulVec v = ∑ k, v k • Matrix.col M k := by
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.col, Finset.sum_apply, smul_eq_mul, mul_comm]

private theorem glue0rAux_basis7_mulVec_inv (v : FEVec 7) :
    (glue0rAux_basis 7 0).mulVec (glue0rAux_inv7.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, glue0rAux_basis7_mul_inv, Matrix.one_mulVec]

private theorem glue0rAux_basis8_mulVec_inv (v : FEVec 8) :
    (glue0rAux_basis 8 7).mulVec (glue0rAux_inv8.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, glue0rAux_basis8_mul_inv, Matrix.one_mulVec]

private theorem glue0rAux_span7 (S : AddSubgroup (FEVec 7))
    (hθ : glue0rAux_theta7 ∈ S)
    (hC : ∀ k : Fin 7, k ≠ 0 → glue0rAux_col 7 k ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hb : ∀ k : Fin 7, glue0rAux_basisCol 7 0 k ∈ S := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simpa [glue0rAux_basisCol, glue0rAux_theta7] using hθ
    · simpa [glue0rAux_basisCol, hk] using hC k hk
  have hv : v = ∑ k, (glue0rAux_inv7.mulVec v) k • glue0rAux_basisCol 7 0 k := by
    calc v = (glue0rAux_basis 7 0).mulVec (glue0rAux_inv7.mulVec v) :=
            (glue0rAux_basis7_mulVec_inv v).symm
      _ = ∑ k, (glue0rAux_inv7.mulVec v) k • Matrix.col (glue0rAux_basis 7 0) k :=
            glue0rAux_mulVec_eq_sum _ _
  rw [hv]
  exact AddSubgroup.sum_mem S (fun k _ => glue0rAux_zmod_smul_mem S (hb k) _)

private theorem glue0rAux_span8 (S : AddSubgroup (FEVec 8))
    (hθ : glue0rAux_theta8 ∈ S)
    (hC : ∀ k : Fin 8, k ≠ 7 → glue0rAux_col 8 k ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hb : ∀ k : Fin 8, glue0rAux_basisCol 8 7 k ∈ S := by
    intro k
    by_cases hk : k = 7
    · subst hk
      simpa [glue0rAux_basisCol, glue0rAux_theta8] using hθ
    · simpa [glue0rAux_basisCol, hk] using hC k hk
  have hv : v = ∑ k, (glue0rAux_inv8.mulVec v) k • glue0rAux_basisCol 8 7 k := by
    calc v = (glue0rAux_basis 8 7).mulVec (glue0rAux_inv8.mulVec v) :=
            (glue0rAux_basis8_mulVec_inv v).symm
      _ = ∑ k, (glue0rAux_inv8.mulVec v) k • Matrix.col (glue0rAux_basis 8 7) k :=
            glue0rAux_mulVec_eq_sum _ _
  rw [hv]
  exact AddSubgroup.sum_mem S (fun k _ => glue0rAux_zmod_smul_mem S (hb k) _)

structure GGFrameModelData (Bs : Subgroup G) (n : ℕ) where
  A : Subgroup (MulAut ↥Bs)
  induced : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs
  ψ : Additive ↥Bs ≃+ FEVec n
  ρ : ↥A →* FEMat n
  act : ∀ (φ : ↥A) (b : ↥Bs),
    (ρ φ).mulVec (ψ (Additive.ofMul b)) = ψ (Additive.ofMul ((φ : MulAut ↥Bs) b))
  simple : ∀ i, ∃ φ : ↥A, ρ φ = feS n i

namespace GGFrameModelData

variable {Bs : Subgroup G} {n : ℕ}

private noncomputable def glue0rAux_simpleAut (M : GGFrameModelData Bs n)
    (i : Fin n) : ↥M.A :=
  Classical.choose (M.simple i)

private theorem glue0rAux_simpleAut_spec (M : GGFrameModelData Bs n) (i : Fin n) :
    M.ρ (glue0rAux_simpleAut M i) = feS n i :=
  Classical.choose_spec (M.simple i)

private noncomputable def glue0rAux_wordAut (M : GGFrameModelData Bs n)
    (l : List (Fin n)) : ↥M.A :=
  (l.map (glue0rAux_simpleAut M)).prod

@[simp] private theorem glue0rAux_wordAut_nil (M : GGFrameModelData Bs n) :
    glue0rAux_wordAut M [] = 1 := rfl

@[simp] private theorem glue0rAux_wordAut_cons (M : GGFrameModelData Bs n)
    (i : Fin n) (l : List (Fin n)) :
    glue0rAux_wordAut M (i :: l) =
      glue0rAux_simpleAut M i * glue0rAux_wordAut M l := rfl

private theorem glue0rAux_wordAut_spec (M : GGFrameModelData Bs n)
    (l : List (Fin n)) : M.ρ (glue0rAux_wordAut M l) = glue0rAux_w n l := by
  induction l with
  | nil => simp [glue0rAux_w]
  | cons i l ih =>
      simp [ih, glue0rAux_simpleAut_spec, glue0rAux_w_cons]

private noncomputable def glue0rAux_wordG (M : GGFrameModelData Bs n)
    (l : List (Fin n)) : G :=
  Classical.choose (M.induced (glue0rAux_wordAut M l) (glue0rAux_wordAut M l).2)

private theorem glue0rAux_wordG_mem (M : GGFrameModelData Bs n) (l : List (Fin n)) :
    glue0rAux_wordG M l ∈ Subgroup.normalizer (Bs : Set G) :=
  (Classical.choose_spec (M.induced (glue0rAux_wordAut M l)
    (glue0rAux_wordAut M l).2)).2.1

private theorem glue0rAux_wordG_conj (M : GGFrameModelData Bs n)
    (l : List (Fin n)) (b : ↥Bs) :
    ((((glue0rAux_wordAut M l : ↥M.A) : MulAut ↥Bs) b : ↥Bs) : G) =
      glue0rAux_wordG M l * b * (glue0rAux_wordG M l)⁻¹ :=
  (Classical.choose_spec (M.induced (glue0rAux_wordAut M l)
    (glue0rAux_wordAut M l).2)).2.2 b

private noncomputable def glue0rAux_conjElem (M : GGFrameModelData Bs n)
    (l : List (Fin n)) (b : ↥Bs) : ↥Bs :=
  ⟨glue0rAux_wordG M l * (b : G) * (glue0rAux_wordG M l)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (glue0rAux_wordG_mem M l) (b : G)).mp b.2⟩

private theorem glue0rAux_word_act (M : GGFrameModelData Bs n)
    (l : List (Fin n)) (b : ↥Bs) :
    M.ψ (Additive.ofMul (glue0rAux_conjElem M l b)) =
      (glue0rAux_w n l).mulVec (M.ψ (Additive.ofMul b)) := by
  have hb : glue0rAux_conjElem M l b =
      ((glue0rAux_wordAut M l : ↥M.A) : MulAut ↥Bs) b := by
    apply Subtype.ext
    exact (glue0rAux_wordG_conj M l b).symm
  rw [hb, ← glue0rAux_wordAut_spec M l]
  exact (M.act (glue0rAux_wordAut M l) b).symm

private noncomputable def glue0rAux_ofVec (M : GGFrameModelData Bs n)
    (v : FEVec n) : ↥Bs :=
  Additive.toMul (M.ψ.symm v)

private theorem glue0rAux_psi_ofVec (M : GGFrameModelData Bs n) (v : FEVec n) :
    M.ψ (Additive.ofMul (glue0rAux_ofVec M v)) = v := by
  simp [glue0rAux_ofVec]

private theorem glue0rAux_psi_inv (M : GGFrameModelData Bs n) {z : G} (hz : z ∈ Bs) :
    M.ψ (Additive.ofMul ⟨z⁻¹, Subgroup.inv_mem Bs hz⟩) =
      -M.ψ (Additive.ofMul ⟨z, hz⟩) := by
  have h : (Additive.ofMul ⟨z⁻¹, Subgroup.inv_mem Bs hz⟩ : Additive ↥Bs) =
      -Additive.ofMul ⟨z, hz⟩ := rfl
  rw [h, map_neg]

@[expose] def IsRoot (M : GGFrameModelData Bs n) (z : G) : Prop :=
  ∃ hz : z ∈ Bs, z ≠ 1 ∧ ∃ t ∈ feT n,
    t.mulVec (M.ψ (Additive.ofMul ⟨z, hz⟩)) = -M.ψ (Additive.ofMul ⟨z, hz⟩)

private theorem glue0rAux_isRoot_ofVec (M : GGFrameModelData Bs n) {v : FEVec n}
    (hv0 : v ≠ 0) {t : FEMat n} (ht : t ∈ feT n) (htv : t.mulVec v = -v) :
    M.IsRoot (glue0rAux_ofVec M v : G) := by
  refine ⟨(glue0rAux_ofVec M v).2, ?_, t, ht, ?_⟩
  · intro hz1
    have hb1 : glue0rAux_ofVec M v = 1 := Subtype.ext (by simpa using hz1)
    apply hv0
    rw [← glue0rAux_psi_ofVec M v, hb1]
    simp
  · rw [glue0rAux_psi_ofVec M v]
    exact htv

private theorem glue0rAux_zmod3_eq_one_or_two {c : ZMod 3} (hc : c ≠ 0) :
    c = 1 ∨ c = 2 := by
  fin_cases c
  · exact (hc rfl).elim
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem glue0rAux_two_smul_neg {n : ℕ} (v : FEVec n) :
    (2 : ZMod 3) • v = -v := by
  ext i
  show (2 : ZMod 3) • v i = -v i
  rw [show (2 : ZMod 3) = -1 by decide, smul_eq_mul]
  exact neg_one_mul (v i)

private theorem glue0rAux_root7_classify (M : GGFrameModelData Bs 7) {z : G}
    (hzBs : z ∈ Bs) (hz : M.IsRoot z) :
    ∃ (l : List (Fin 7)) (ε : ZMod 3), ε ≠ 0 ∧
      M.ψ (Additive.ofMul ⟨z, hzBs⟩) =
        ε • (glue0rAux_w 7 l).mulVec glue0rAux_theta7 := by
  obtain ⟨hzBs', hz1, t, ht, htv⟩ := hz
  have hsub : (⟨z, hzBs'⟩ : ↥Bs) = ⟨z, hzBs⟩ := Subtype.ext rfl
  have hψ : M.ψ (Additive.ofMul (⟨z, hzBs'⟩ : ↥Bs)) =
      M.ψ (Additive.ofMul (⟨z, hzBs⟩ : ↥Bs)) :=
    congrArg (fun b => M.ψ (Additive.ofMul b)) hsub
  have htv' : t.mulVec (M.ψ (Additive.ofMul (⟨z, hzBs⟩ : ↥Bs))) =
      -M.ψ (Additive.ofMul (⟨z, hzBs⟩ : ↥Bs)) := by
    rw [← hψ]
    exact htv
  have hv0 : M.ψ (Additive.ofMul (⟨z, hzBs⟩ : ↥Bs)) ≠ 0 := by
    intro h
    apply hz1
    have hzero : Additive.ofMul (⟨z, hzBs⟩ : ↥Bs) = 0 := by
      apply M.ψ.injective
      simpa using h
    have hb1 : (⟨z, hzBs⟩ : ↥Bs) = 1 := by simpa using hzero
    exact congrArg Subtype.val hb1
  exact glue0rAux_root7_word ht hv0 htv'

private theorem glue0rAux_root8_classify (M : GGFrameModelData Bs 8) {z : G}
    (hzBs : z ∈ Bs) (hz : M.IsRoot z) :
    ∃ (l : List (Fin 8)) (ε : ZMod 3), ε ≠ 0 ∧
      M.ψ (Additive.ofMul ⟨z, hzBs⟩) =
        ε • (glue0rAux_w 8 l).mulVec glue0rAux_theta8 := by
  obtain ⟨hzBs', hz1, t, ht, htv⟩ := hz
  have hsub : (⟨z, hzBs'⟩ : ↥Bs) = ⟨z, hzBs⟩ := Subtype.ext rfl
  have hψ : M.ψ (Additive.ofMul (⟨z, hzBs'⟩ : ↥Bs)) =
      M.ψ (Additive.ofMul (⟨z, hzBs⟩ : ↥Bs)) :=
    congrArg (fun b => M.ψ (Additive.ofMul b)) hsub
  have htv' : t.mulVec (M.ψ (Additive.ofMul (⟨z, hzBs⟩ : ↥Bs))) =
      -M.ψ (Additive.ofMul (⟨z, hzBs⟩ : ↥Bs)) := by
    rw [← hψ]
    exact htv
  have hv0 : M.ψ (Additive.ofMul (⟨z, hzBs⟩ : ↥Bs)) ≠ 0 := by
    intro h
    apply hz1
    have hzero : Additive.ofMul (⟨z, hzBs⟩ : ↥Bs) = 0 := by
      apply M.ψ.injective
      simpa using h
    have hb1 : (⟨z, hzBs⟩ : ↥Bs) = 1 := by simpa using hzero
    exact congrArg Subtype.val hb1
  exact glue0rAux_root8_word ht hv0 htv'

private theorem glue0rAux_word_conj_apply {n : ℕ} {theta : FEVec n}
    {l l' : List (Fin n)} {ε : ZMod 3} :
    (glue0rAux_w n (l' ++ l.reverse)).mulVec
        (ε • (glue0rAux_w n l).mulVec theta) =
      ε • (glue0rAux_w n l').mulVec theta := by
  calc (glue0rAux_w n (l' ++ l.reverse)).mulVec
        (ε • (glue0rAux_w n l).mulVec theta)
      = (glue0rAux_w n l' * glue0rAux_w n l.reverse).mulVec
          (ε • (glue0rAux_w n l).mulVec theta) := by rw [glue0rAux_w_append]
    _ = (glue0rAux_w n l').mulVec ((glue0rAux_w n l.reverse).mulVec
          (ε • (glue0rAux_w n l).mulVec theta)) := by rw [← Matrix.mulVec_mulVec]
    _ = (glue0rAux_w n l').mulVec (ε • (glue0rAux_w n l.reverse).mulVec
          ((glue0rAux_w n l).mulVec theta)) := by rw [Matrix.mulVec_smul]
    _ = ε • (glue0rAux_w n l').mulVec ((glue0rAux_w n l.reverse).mulVec
          ((glue0rAux_w n l).mulVec theta)) := by rw [Matrix.mulVec_smul]
    _ = ε • (glue0rAux_w n l').mulVec ((glue0rAux_w n l.reverse *
          glue0rAux_w n l).mulVec theta) := by rw [← Matrix.mulVec_mulVec]
    _ = ε • (glue0rAux_w n l').mulVec theta := by
          rw [glue0rAux_w_reverse_mul, Matrix.one_mulVec]

private theorem glue0rAux_word_conj_eq (M : GGFrameModelData Bs n)
    (l : List (Fin n)) {z y : G} (hzBs : z ∈ Bs) (hyBs : y ∈ Bs)
    (h : M.ψ (Additive.ofMul ⟨y, hyBs⟩) =
      (glue0rAux_w n l).mulVec (M.ψ (Additive.ofMul ⟨z, hzBs⟩))) :
    glue0rAux_wordG M l * z * (glue0rAux_wordG M l)⁻¹ = y := by
  have hvec := glue0rAux_word_act M l ⟨z, hzBs⟩
  have hpsi : M.ψ (Additive.ofMul (glue0rAux_conjElem M l ⟨z, hzBs⟩)) =
      M.ψ (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) := by
    rw [hvec, h]
  have hb : glue0rAux_conjElem M l ⟨z, hzBs⟩ = ⟨y, hyBs⟩ := by
    apply Additive.ofMul.injective
    apply M.ψ.injective
    exact hpsi
  exact congrArg Subtype.val hb

private theorem glue0rAux_exists_conj_of_word {n : ℕ} {theta : FEVec n} {z z' : G}
    (M : GGFrameModelData Bs n) (hzBs : z ∈ Bs) (hz'Bs : z' ∈ Bs)
    (hψz : ∃ (l : List (Fin n)) (ε : ZMod 3), ε ≠ 0 ∧
      M.ψ (Additive.ofMul ⟨z, hzBs⟩) = ε • (glue0rAux_w n l).mulVec theta)
    (hψz' : ∃ (l : List (Fin n)) (ε : ZMod 3), ε ≠ 0 ∧
      M.ψ (Additive.ofMul ⟨z', hz'Bs⟩) = ε • (glue0rAux_w n l).mulVec theta)
    (negWord : List (Fin n))
    (hneg : (glue0rAux_w n negWord).mulVec theta = -theta) :
    ∃ g ∈ Subgroup.normalizer (Bs : Set G),
      g * z * g⁻¹ = z' ∨ g * z * g⁻¹ = z'⁻¹ := by
  obtain ⟨l, ε, hε0, hψz_eq⟩ := hψz
  obtain ⟨l', ε', hε'0, hψz'_eq⟩ := hψz'
  have hεcases := glue0rAux_zmod3_eq_one_or_two hε0
  have htarget : ∃ t : List (Fin n),
      (glue0rAux_w n t).mulVec theta = M.ψ (Additive.ofMul ⟨z', hz'Bs⟩) := by
    rcases glue0rAux_zmod3_eq_one_or_two hε'0 with hε' | hε'
    · refine ⟨l', ?_⟩
      rw [hε'] at hψz'_eq
      simpa using hψz'_eq.symm
    · refine ⟨l' ++ negWord, ?_⟩
      calc (glue0rAux_w n (l' ++ negWord)).mulVec theta
          = (glue0rAux_w n l').mulVec ((glue0rAux_w n negWord).mulVec theta) := by
              rw [glue0rAux_w_append, ← Matrix.mulVec_mulVec]
        _ = (glue0rAux_w n l').mulVec (-theta) := by rw [hneg]
        _ = -(glue0rAux_w n l').mulVec theta := Matrix.mulVec_neg theta _
        _ = (2 : ZMod 3) • (glue0rAux_w n l').mulVec theta :=
              (glue0rAux_two_smul_neg _).symm
        _ = M.ψ (Additive.ofMul ⟨z', hz'Bs⟩) := by
              rw [hε'] at hψz'_eq
              exact hψz'_eq.symm
  obtain ⟨targetList, htarget⟩ := htarget
  set L : List (Fin n) := targetList ++ l.reverse with hL
  have hW : (glue0rAux_w n L).mulVec (M.ψ (Additive.ofMul ⟨z, hzBs⟩)) =
      ε • M.ψ (Additive.ofMul ⟨z', hz'Bs⟩) := by
    rw [hL, hψz_eq]
    rw [glue0rAux_word_conj_apply, htarget]
  refine ⟨glue0rAux_wordG M L, glue0rAux_wordG_mem M L, ?_⟩
  rcases hεcases with hε | hε
  · left
    have hy : M.ψ (Additive.ofMul ⟨z', hz'Bs⟩) =
        (glue0rAux_w n L).mulVec (M.ψ (Additive.ofMul ⟨z, hzBs⟩)) := by
      rw [hW, hε, one_smul]
    exact glue0rAux_word_conj_eq M L hzBs hz'Bs hy
  · right
    have hy : M.ψ (Additive.ofMul (⟨z'⁻¹, Subgroup.inv_mem Bs hz'Bs⟩ : ↥Bs)) =
        (glue0rAux_w n L).mulVec (M.ψ (Additive.ofMul ⟨z, hzBs⟩)) := by
      rw [glue0rAux_psi_inv M hz'Bs, hW, hε, glue0rAux_two_smul_neg]
    exact glue0rAux_word_conj_eq M L hzBs (Subgroup.inv_mem Bs hz'Bs) hy

private theorem glue0rAux_neg_theta7 :
    (glue0rAux_w 7 (glue0rAux_lTheta7 ++ [0] ++ glue0rAux_lTheta7.reverse)).mulVec
        glue0rAux_theta7 = -glue0rAux_theta7 :=
  glue0rAux_w_neg_theta 0 glue0rAux_theta7_spec

private theorem glue0rAux_neg_theta8 :
    (glue0rAux_w 8 (glue0rAux_lTheta8 ++ [0] ++ glue0rAux_lTheta8.reverse)).mulVec
        glue0rAux_theta8 = -glue0rAux_theta8 :=
  glue0rAux_w_neg_theta 0 glue0rAux_theta8_spec

private theorem glue0rAux_feConjDer_conj_word (n : ℕ) (i : Fin n)
    (l : List (Fin n)) :
    FEConjDer n (glue0rAux_w n l * feS n i * glue0rAux_w n l.reverse) := by
  induction l with
  | nil => simpa using FEConjDer.base i
  | cons j l ih =>
      rw [List.reverse_cons, glue0rAux_w_append]
      simp only [glue0rAux_w_cons, glue0rAux_w_nil, mul_one]
      have h := FEConjDer.conj j ih
      convert h using 1
      noncomm_ring

private theorem glue0rAux_feConjDer_conj_word_append (n : ℕ) (i : Fin n)
    (l : List (Fin n)) :
    FEConjDer n (glue0rAux_w n (l ++ [i] ++ l.reverse)) := by
  rw [glue0rAux_w_append, glue0rAux_w_append]
  simp only [glue0rAux_w_cons, glue0rAux_w_nil, mul_one]
  exact glue0rAux_feConjDer_conj_word n i l

private theorem glue0rAux_feS_theta7 (j : Fin 7) (hj : j ≠ 0) :
    (feS 7 j).mulVec glue0rAux_theta7 = glue0rAux_theta7 := by
  have h : glue0rAux_theta7 j = 0 := by
    simp [glue0rAux_theta7, Pi.single_eq_of_ne hj]
  rw [feS_mulVec, h, zero_smul]
  simp

private theorem glue0rAux_feS_theta8 (j : Fin 8) (hj : j ≠ 7) :
    (feS 8 j).mulVec glue0rAux_theta8 = glue0rAux_theta8 := by
  have h : glue0rAux_theta8 j = 0 := by
    simp [glue0rAux_theta8, Pi.single_eq_of_ne hj]
  rw [feS_mulVec, h, zero_smul]
  simp

private theorem glue0rAux_exists_negWord7 :
    ∃ negWord : List (Fin 7),
      (glue0rAux_w 7 negWord).mulVec glue0rAux_theta7 = -glue0rAux_theta7 :=
  ⟨_, glue0rAux_neg_theta7⟩

private theorem glue0rAux_exists_negWord8 :
    ∃ negWord : List (Fin 8),
      (glue0rAux_w 8 negWord).mulVec glue0rAux_theta8 = -glue0rAux_theta8 :=
  ⟨_, glue0rAux_neg_theta8⟩

private theorem glue0rAux_feConjDer_conj_w (n : ℕ) (l : List (Fin n))
    {t : FEMat n} (ht : FEConjDer n t) :
    FEConjDer n (glue0rAux_w n l * t * glue0rAux_w n l.reverse) := by
  induction l with
  | nil => simpa using ht
  | cons j l ih =>
      rw [List.reverse_cons, glue0rAux_w_append]
      simp only [glue0rAux_w_cons, glue0rAux_w_nil, mul_one]
      have h := FEConjDer.conj j ih
      convert h using 1
      noncomm_ring

private theorem glue0rAux_isRoot_of_word (M : GGFrameModelData Bs n)
    {theta v : FEVec n} (hv0 : v ≠ 0) {l : List (Fin n)} {t : FEMat n}
    (ht : FEConjDer n t) (htθ : t.mulVec theta = -theta)
    (hθ : (glue0rAux_w n l).mulVec theta = v) :
    M.IsRoot (glue0rAux_ofVec M v : G) := by
  have hrev : (glue0rAux_w n l.reverse).mulVec v = theta := by
    rw [← hθ, Matrix.mulVec_mulVec, glue0rAux_w_reverse_mul, Matrix.one_mulVec]
  have htv : (glue0rAux_w n l * t * glue0rAux_w n l.reverse).mulVec v = -v := by
    rw [show glue0rAux_w n l * t * glue0rAux_w n l.reverse =
      glue0rAux_w n l * (t * glue0rAux_w n l.reverse) by noncomm_ring]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [hrev, htθ]
    calc Matrix.mulVec (glue0rAux_w n l) (-theta)
        = -Matrix.mulVec (glue0rAux_w n l) theta :=
          Matrix.mulVec_neg theta (glue0rAux_w n l)
      _ = -v := by rw [hθ]
  exact glue0rAux_isRoot_ofVec M hv0 (glue0rAux_feConjDer_conj_w n l ht) htv

private theorem glue0rAux_feCol_ne_zero7 (i : Fin 7) : feCol 7 i ≠ 0 := by
  have hpoint : feCol 7 i i ≠ 0 := by
    rw [glue0rAux_feCol_entry]
    fin_cases i <;> decide +kernel
  intro h
  exact hpoint (congrFun h i)

private theorem glue0rAux_feCol_ne_zero8 (i : Fin 8) : feCol 8 i ≠ 0 := by
  have hpoint : feCol 8 i i ≠ 0 := by
    rw [glue0rAux_feCol_entry]
    fin_cases i <;> decide +kernel
  intro h
  exact hpoint (congrFun h i)

private theorem glue0rAux_col7_isRoot (M : GGFrameModelData Bs 7) (i : Fin 7) :
    M.IsRoot (glue0rAux_ofVec M (feCol 7 i) : G) := by
  obtain ⟨l, hl⟩ := glue0rAux_col7_from_theta i
  exact glue0rAux_isRoot_of_word M (glue0rAux_feCol_ne_zero7 i)
    (glue0rAux_feConjDer_conj_word_append 7 0 glue0rAux_lTheta7)
    glue0rAux_neg_theta7 hl

private theorem glue0rAux_col8_isRoot (M : GGFrameModelData Bs 8) (i : Fin 8) :
    M.IsRoot (glue0rAux_ofVec M (feCol 8 i) : G) := by
  obtain ⟨l, hl⟩ := glue0rAux_col8_from_theta i
  exact glue0rAux_isRoot_of_word M (glue0rAux_feCol_ne_zero8 i)
    (glue0rAux_feConjDer_conj_word_append 8 0 glue0rAux_lTheta8)
    glue0rAux_neg_theta8 hl

private theorem glue0rAux_isRoot_smul (M : GGFrameModelData Bs n) (j : Fin n)
    {v : FEVec n} (hv : M.IsRoot (glue0rAux_ofVec M v : G)) :
    M.IsRoot (glue0rAux_ofVec M ((feS n j).mulVec v) : G) := by
  obtain ⟨hzBs, hz1, t, ht, htv⟩ := hv
  have hv0 : v ≠ 0 := by
    intro h
    have hzero : Additive.ofMul (glue0rAux_ofVec M v) = 0 := by
      apply M.ψ.injective
      rw [glue0rAux_psi_ofVec, h]
      simp
    have hb1 : glue0rAux_ofVec M v = 1 := by
      have := congrArg Additive.toMul hzero
      simpa using this
    exact hz1 (by simpa using congrArg (fun x : ↥Bs => (x : G)) hb1)
  have hw0 : (feS n j).mulVec v ≠ 0 := by
    intro h
    have hvv : v = 0 := by
      have := congrArg (fun w => (feS n j).mulVec w) h
      rw [Matrix.mulVec_mulVec, feS_mul_self, Matrix.one_mulVec,
        Matrix.mulVec_zero] at this
      exact this
    exact hv0 hvv
  have htv' : t.mulVec v = -v := by
    rw [← glue0rAux_psi_ofVec M v]
    exact htv
  have htv_main : (feS n j * t * feS n j).mulVec ((feS n j).mulVec v) =
      -((feS n j).mulVec v) := by
    rw [show feS n j * t * feS n j = feS n j * (t * feS n j) by noncomm_ring]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [show (feS n j).mulVec ((feS n j).mulVec v) = v by
      rw [Matrix.mulVec_mulVec, feS_mul_self, Matrix.one_mulVec]]
    rw [htv']
    exact Matrix.mulVec_neg v (feS n j)
  exact glue0rAux_isRoot_ofVec M hw0 (FEConjDer.conj j ht) htv_main

private theorem glue0rAux_ofVec_add (M : GGFrameModelData Bs n) (v w : FEVec n) :
    glue0rAux_ofVec M (v + w) = glue0rAux_ofVec M v * glue0rAux_ofVec M w := by
  have h : Additive.ofMul (glue0rAux_ofVec M (v + w)) =
      Additive.ofMul (glue0rAux_ofVec M v) + Additive.ofMul (glue0rAux_ofVec M w) := by
    apply M.ψ.injective
    simp [map_add, glue0rAux_psi_ofVec]
  have h' := congrArg Additive.toMul h
  simpa using h'

private theorem glue0rAux_s2_col0_7 :
    (feS 7 2).mulVec (feCol 7 0) = feCol 7 0 + feCol 7 2 := by
  have h : feCol 7 0 2 = -1 := by
    rw [glue0rAux_feCol_entry]
    decide +kernel
  rw [feS_mulVec, h]
  rw [show (-1 : ZMod 3) • feCol 7 2 = -feCol 7 2 by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact neg_one_mul _]
  abel

private theorem glue0rAux_s3_col2_7 :
    (feS 7 3).mulVec (feCol 7 2) = feCol 7 2 + feCol 7 3 := by
  have h : feCol 7 2 3 = -1 := by
    rw [glue0rAux_feCol_entry]
    decide +kernel
  rw [feS_mulVec, h]
  rw [show (-1 : ZMod 3) • feCol 7 3 = -feCol 7 3 by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact neg_one_mul _]
  abel

private theorem glue0rAux_s3_col02_7 :
    (feS 7 3).mulVec (feCol 7 0 + feCol 7 2) =
      feCol 7 0 + feCol 7 2 + feCol 7 3 := by
  have h0 : feCol 7 0 3 = 0 := by
    rw [glue0rAux_feCol_entry]
    decide +kernel
  have h2 : feCol 7 2 3 = -1 := by
    rw [glue0rAux_feCol_entry]
    decide +kernel
  have h : (feCol 7 0 + feCol 7 2) 3 = -1 := by
    simp [Pi.add_apply, h0, h2]
  rw [feS_mulVec, h]
  rw [show (-1 : ZMod 3) • feCol 7 3 = -feCol 7 3 by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact neg_one_mul _]
  abel

private theorem glue0rAux_s2_col0_8 :
    (feS 8 2).mulVec (feCol 8 0) = feCol 8 0 + feCol 8 2 := by
  have h : feCol 8 0 2 = -1 := by
    rw [glue0rAux_feCol_entry]
    decide +kernel
  rw [feS_mulVec, h]
  rw [show (-1 : ZMod 3) • feCol 8 2 = -feCol 8 2 by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact neg_one_mul _]
  abel

private theorem glue0rAux_s3_col2_8 :
    (feS 8 3).mulVec (feCol 8 2) = feCol 8 2 + feCol 8 3 := by
  have h : feCol 8 2 3 = -1 := by
    rw [glue0rAux_feCol_entry]
    decide +kernel
  rw [feS_mulVec, h]
  rw [show (-1 : ZMod 3) • feCol 8 3 = -feCol 8 3 by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact neg_one_mul _]
  abel

private theorem glue0rAux_s3_col02_8 :
    (feS 8 3).mulVec (feCol 8 0 + feCol 8 2) =
      feCol 8 0 + feCol 8 2 + feCol 8 3 := by
  have h0 : feCol 8 0 3 = 0 := by
    rw [glue0rAux_feCol_entry]
    decide +kernel
  have h2 : feCol 8 2 3 = -1 := by
    rw [glue0rAux_feCol_entry]
    decide +kernel
  have h : (feCol 8 0 + feCol 8 2) 3 = -1 := by
    simp [Pi.add_apply, h0, h2]
  rw [feS_mulVec, h]
  rw [show (-1 : ZMod 3) • feCol 8 3 = -feCol 8 3 by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact neg_one_mul _]
  abel

private theorem glue0rAux_zmod3_no_six (a b c : ZMod 3)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a + b ≠ 0) (hbc : b + c ≠ 0) (habc : a + b + c ≠ 0) : False := by
  revert a b c ha hb hc hab hbc habc
  decide +kernel

private theorem glue0rAux_theta7_isRoot (M : GGFrameModelData Bs 7) :
    M.IsRoot (glue0rAux_ofVec M glue0rAux_theta7 : G) := by
  apply glue0rAux_isRoot_ofVec M ?_ ?_ glue0rAux_neg_theta7
  · intro h
    have := congrFun h 0
    simp [glue0rAux_theta7] at this
  · exact glue0rAux_feConjDer_conj_word_append 7 0 glue0rAux_lTheta7

private theorem glue0rAux_theta8_isRoot (M : GGFrameModelData Bs 8) :
    M.IsRoot (glue0rAux_ofVec M glue0rAux_theta8 : G) := by
  apply glue0rAux_isRoot_ofVec M ?_ ?_ glue0rAux_neg_theta8
  · intro h
    have := congrFun h 7
    simp [glue0rAux_theta8] at this
  · exact glue0rAux_feConjDer_conj_word_append 8 0 glue0rAux_lTheta8

private noncomputable def glue0rAux_imageSub (M : GGFrameModelData Bs n)
    (W : Subgroup G) (_hWB : W ≤ Bs) : AddSubgroup (FEVec n) :=
  AddSubgroup.map M.ψ.toAddMonoidHom (W.subgroupOf Bs).toAddSubgroup

private theorem glue0rAux_mem_imageSub (M : GGFrameModelData Bs n)
    {W : Subgroup G} {_hWB : W ≤ Bs} {y : FEVec n} :
    y ∈ glue0rAux_imageSub M W _hWB ↔
      ((Additive.toMul (M.ψ.symm y) : ↥Bs) : G) ∈ W := by
  rw [glue0rAux_imageSub, AddSubgroup.mem_map_equiv, Additive.mem_toAddSubgroup,
    Subgroup.mem_subgroupOf]

private theorem glue0rAux_coord_ne_zero7 {y : FEVec 7}
    (hy : y ∉ AddSubgroup.zmultiples glue0rAux_theta7) :
    ∃ k : Fin 7, k ≠ 0 ∧ y k ≠ 0 := by
  by_contra h
  apply hy
  have hzero : ∀ k : Fin 7, k ≠ 0 → y k = 0 := by
    intro k hk
    by_contra hk0
    exact h ⟨k, hk, hk0⟩
  have hyeq : y = (y 0).val • glue0rAux_theta7 := by
    ext i
    by_cases hi : i = 0
    · subst hi
      simp [glue0rAux_theta7, Pi.smul_apply]
    · simp [glue0rAux_theta7, hzero i hi, Pi.smul_apply,
        Pi.single_eq_of_ne hi]
  rw [hyeq]
  exact AddSubgroup.nsmul_mem_zmultiples _ _

private theorem glue0rAux_coord_ne_zero8 {y : FEVec 8}
    (hy : y ∉ AddSubgroup.zmultiples glue0rAux_theta8) :
    ∃ k : Fin 8, k ≠ 7 ∧ y k ≠ 0 := by
  by_contra h
  apply hy
  have hzero : ∀ k : Fin 8, k ≠ 7 → y k = 0 := by
    intro k hk
    by_contra hk0
    exact h ⟨k, hk, hk0⟩
  have hyeq : y = (y 7).val • glue0rAux_theta8 := by
    ext i
    by_cases hi : i = 7
    · subst hi
      simp [glue0rAux_theta8, Pi.smul_apply]
    · simp [glue0rAux_theta8, hzero i hi, Pi.smul_apply,
        Pi.single_eq_of_ne hi]
  rw [hyeq]
  exact AddSubgroup.nsmul_mem_zmultiples _ _

private theorem glue0rAux_col_mem_step7 (S : AddSubgroup (FEVec 7))
    (hclosed : ∀ j : Fin 7, j ≠ 0 → ∀ y ∈ S, (feS 7 j).mulVec y ∈ S)
    {a b : Fin 7} (hb : b ≠ 0) (ha : glue0rAux_col 7 a ∈ S)
    (hadj : glue0rAux_col 7 a b = -1) : glue0rAux_col 7 b ∈ S := by
  have hs : (feS 7 b).mulVec (glue0rAux_col 7 a) ∈ S := hclosed b hb _ ha
  rw [feS_mulVec, ← glue0rAux_col_eq_feCol, hadj] at hs
  have hneg : (-1 : ZMod 3) • glue0rAux_col 7 b = -glue0rAux_col 7 b := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact neg_one_mul _
  rw [hneg] at hs
  have hs' : glue0rAux_col 7 a + glue0rAux_col 7 b ∈ S := by
    convert hs using 1
    abel
  have hb' : glue0rAux_col 7 b ∈ S := by
    have := S.sub_mem hs' ha
    convert this using 1
    abel
  exact hb'

private theorem glue0rAux_col_mem_step8 (S : AddSubgroup (FEVec 8))
    (hclosed : ∀ j : Fin 8, j ≠ 7 → ∀ y ∈ S, (feS 8 j).mulVec y ∈ S)
    {a b : Fin 8} (hb : b ≠ 7) (ha : glue0rAux_col 8 a ∈ S)
    (hadj : glue0rAux_col 8 a b = -1) : glue0rAux_col 8 b ∈ S := by
  have hs : (feS 8 b).mulVec (glue0rAux_col 8 a) ∈ S := hclosed b hb _ ha
  rw [feS_mulVec, ← glue0rAux_col_eq_feCol, hadj] at hs
  have hneg : (-1 : ZMod 3) • glue0rAux_col 8 b = -glue0rAux_col 8 b := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact neg_one_mul _
  rw [hneg] at hs
  have hs' : glue0rAux_col 8 a + glue0rAux_col 8 b ∈ S := by
    convert hs using 1
    abel
  have hb' : glue0rAux_col 8 b ∈ S := by
    have := S.sub_mem hs' ha
    convert this using 1
    abel
  exact hb'

private theorem glue0rAux_cols7_from_three (S : AddSubgroup (FEVec 7))
    (hclosed : ∀ j : Fin 7, j ≠ 0 → ∀ y ∈ S, (feS 7 j).mulVec y ∈ S)
    (h3 : glue0rAux_col 7 3 ∈ S) :
    ∀ l : Fin 7, l ≠ 0 → glue0rAux_col 7 l ∈ S := by
  intro l hl
  have h1 : glue0rAux_col 7 1 ∈ S :=
    glue0rAux_col_mem_step7 S hclosed (by decide +kernel) h3 (by decide +kernel)
  have h2 : glue0rAux_col 7 2 ∈ S :=
    glue0rAux_col_mem_step7 S hclosed (by decide +kernel) h3 (by decide +kernel)
  have h4 : glue0rAux_col 7 4 ∈ S :=
    glue0rAux_col_mem_step7 S hclosed (by decide +kernel) h3 (by decide +kernel)
  have h5 : glue0rAux_col 7 5 ∈ S :=
    glue0rAux_col_mem_step7 S hclosed (by decide +kernel) h4 (by decide +kernel)
  have h6 : glue0rAux_col 7 6 ∈ S :=
    glue0rAux_col_mem_step7 S hclosed (by decide +kernel) h5 (by decide +kernel)
  fin_cases l <;> simp_all

private theorem glue0rAux_cols7_of_one (S : AddSubgroup (FEVec 7))
    (hclosed : ∀ j : Fin 7, j ≠ 0 → ∀ y ∈ S, (feS 7 j).mulVec y ∈ S)
    {k : Fin 7} (hk : k ≠ 0) (hCk : glue0rAux_col 7 k ∈ S) :
    ∀ l : Fin 7, l ≠ 0 → glue0rAux_col 7 l ∈ S := by
  intro l hl
  have h3 : glue0rAux_col 7 3 ∈ S := by
    fin_cases k
    · exact (hk rfl).elim
    · exact glue0rAux_col_mem_step7 S hclosed (a := 1) (b := 3)
        (by decide +kernel) hCk (by decide +kernel)
    · exact glue0rAux_col_mem_step7 S hclosed (a := 2) (b := 3)
        (by decide +kernel) hCk (by decide +kernel)
    · exact hCk
    · exact glue0rAux_col_mem_step7 S hclosed (a := 4) (b := 3)
        (by decide +kernel) hCk (by decide +kernel)
    · exact glue0rAux_col_mem_step7 S hclosed (a := 4) (b := 3)
        (by decide +kernel)
        (glue0rAux_col_mem_step7 S hclosed (a := 5) (b := 4)
          (by decide +kernel) hCk (by decide +kernel))
        (by decide +kernel)
    · exact glue0rAux_col_mem_step7 S hclosed (a := 4) (b := 3)
        (by decide +kernel)
        (glue0rAux_col_mem_step7 S hclosed (a := 5) (b := 4)
          (by decide +kernel)
          (glue0rAux_col_mem_step7 S hclosed (a := 6) (b := 5)
            (by decide +kernel) hCk (by decide +kernel))
          (by decide +kernel))
        (by decide +kernel)
  exact glue0rAux_cols7_from_three S hclosed h3 l hl

private theorem glue0rAux_cols8_from_three (S : AddSubgroup (FEVec 8))
    (hclosed : ∀ j : Fin 8, j ≠ 7 → ∀ y ∈ S, (feS 8 j).mulVec y ∈ S)
    (h3 : glue0rAux_col 8 3 ∈ S) :
    ∀ l : Fin 8, l ≠ 7 → glue0rAux_col 8 l ∈ S := by
  intro l hl
  have h2 : glue0rAux_col 8 2 ∈ S :=
    glue0rAux_col_mem_step8 S hclosed (by decide +kernel) h3 (by decide +kernel)
  have h0 : glue0rAux_col 8 0 ∈ S :=
    glue0rAux_col_mem_step8 S hclosed (by decide +kernel) h2 (by decide +kernel)
  have h1 : glue0rAux_col 8 1 ∈ S :=
    glue0rAux_col_mem_step8 S hclosed (by decide +kernel) h3 (by decide +kernel)
  have h4 : glue0rAux_col 8 4 ∈ S :=
    glue0rAux_col_mem_step8 S hclosed (by decide +kernel) h3 (by decide +kernel)
  have h5 : glue0rAux_col 8 5 ∈ S :=
    glue0rAux_col_mem_step8 S hclosed (by decide +kernel) h4 (by decide +kernel)
  have h6 : glue0rAux_col 8 6 ∈ S :=
    glue0rAux_col_mem_step8 S hclosed (by decide +kernel) h5 (by decide +kernel)
  fin_cases l <;> simp_all

private theorem glue0rAux_cols8_of_one (S : AddSubgroup (FEVec 8))
    (hclosed : ∀ j : Fin 8, j ≠ 7 → ∀ y ∈ S, (feS 8 j).mulVec y ∈ S)
    {k : Fin 8} (hk : k ≠ 7) (hCk : glue0rAux_col 8 k ∈ S) :
    ∀ l : Fin 8, l ≠ 7 → glue0rAux_col 8 l ∈ S := by
  intro l hl
  have h3 : glue0rAux_col 8 3 ∈ S := by
    fin_cases k
    · exact glue0rAux_col_mem_step8 S hclosed (a := 2) (b := 3)
        (by decide +kernel)
        (glue0rAux_col_mem_step8 S hclosed (a := 0) (b := 2)
          (by decide +kernel) hCk (by decide +kernel))
        (by decide +kernel)
    · exact glue0rAux_col_mem_step8 S hclosed (a := 1) (b := 3)
        (by decide +kernel) hCk (by decide +kernel)
    · exact glue0rAux_col_mem_step8 S hclosed (a := 2) (b := 3)
        (by decide +kernel) hCk (by decide +kernel)
    · exact hCk
    · exact glue0rAux_col_mem_step8 S hclosed (a := 4) (b := 3)
        (by decide +kernel) hCk (by decide +kernel)
    · exact glue0rAux_col_mem_step8 S hclosed (a := 4) (b := 3)
        (by decide +kernel)
        (glue0rAux_col_mem_step8 S hclosed (a := 5) (b := 4)
          (by decide +kernel) hCk (by decide +kernel))
        (by decide +kernel)
    · exact glue0rAux_col_mem_step8 S hclosed (a := 4) (b := 3)
        (by decide +kernel)
        (glue0rAux_col_mem_step8 S hclosed (a := 5) (b := 4)
          (by decide +kernel)
          (glue0rAux_col_mem_step8 S hclosed (a := 6) (b := 5)
            (by decide +kernel) hCk (by decide +kernel))
          (by decide +kernel))
        (by decide +kernel)
    · exact (hk rfl).elim
  exact glue0rAux_cols8_from_three S hclosed h3 l hl

private theorem glue0rAux_psi_symm_feS (M : GGFrameModelData Bs n)
    (j : Fin n) (b : ↥Bs) :
    M.ψ.symm ((feS n j).mulVec (M.ψ (Additive.ofMul b))) =
      Additive.ofMul (glue0rAux_conjElem M [j] b) := by
  apply M.ψ.injective
  simpa [glue0rAux_w] using (glue0rAux_word_act M [j] b).symm

private theorem glue0rAux_irreducible_theta7 (M : GGFrameModelData Bs 7)
    (W : Subgroup G) (hWB : W ≤ Bs)
    (hθ : (glue0rAux_ofVec M glue0rAux_theta7 : G) ∈ W)
    (hH : ∀ h ∈ Subgroup.normalizer (Bs : Set G) ⊓
        Subgroup.centralizer ({(glue0rAux_ofVec M glue0rAux_theta7 : G)} : Set G),
      ∀ w ∈ W, h * w * h⁻¹ ∈ W) :
    W = Subgroup.zpowers (glue0rAux_ofVec M glue0rAux_theta7 : G) ∨
      W = Bs := by
  let zθ : G := glue0rAux_ofVec M glue0rAux_theta7
  let S : AddSubgroup (FEVec 7) := glue0rAux_imageSub M W hWB
  have hzθBs : zθ ∈ Bs := hWB hθ
  have hthetaS : glue0rAux_theta7 ∈ S := by
    rw [show S = glue0rAux_imageSub M W hWB from rfl, glue0rAux_mem_imageSub]
    have hsymm : M.ψ.symm glue0rAux_theta7 =
        Additive.ofMul (⟨zθ, hzθBs⟩ : ↥Bs) := by
      apply M.ψ.injective
      simp [zθ, glue0rAux_psi_ofVec]
    rw [hsymm]
    simpa [zθ] using hθ
  have hclosed : ∀ j : Fin 7, j ≠ 0 → ∀ y ∈ S, (feS 7 j).mulVec y ∈ S := by
    intro j hj y hy
    rw [show S = glue0rAux_imageSub M W hWB from rfl, glue0rAux_mem_imageSub] at hy ⊢
    let b : Additive ↥Bs := M.ψ.symm y
    let bg : ↥Bs := Additive.toMul b
    have hyb : (bg : G) ∈ W := by simpa [bg, b] using hy
    have hyψ : y = M.ψ b := by simp [b]
    have hmem : glue0rAux_wordG M [j] ∈
        Subgroup.normalizer (Bs : Set G) ⊓
          Subgroup.centralizer ({(glue0rAux_ofVec M glue0rAux_theta7 : G)} : Set G) := by
      rw [Subgroup.mem_inf]
      refine ⟨glue0rAux_wordG_mem M [j], ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hfix : ((glue0rAux_wordAut M [j] : ↥M.A) : MulAut ↥Bs)
          (glue0rAux_ofVec M glue0rAux_theta7) =
          glue0rAux_ofVec M glue0rAux_theta7 := by
        apply_fun fun b : ↥Bs => M.ψ (Additive.ofMul b) using
          fun a b hab => Additive.ofMul.injective (M.ψ.injective hab)
        change M.ψ (Additive.ofMul (((glue0rAux_wordAut M [j] : ↥M.A) : MulAut ↥Bs)
          (glue0rAux_ofVec M glue0rAux_theta7))) =
          M.ψ (Additive.ofMul (glue0rAux_ofVec M glue0rAux_theta7))
        rw [← M.act (glue0rAux_wordAut M [j]) (glue0rAux_ofVec M glue0rAux_theta7)]
        rw [glue0rAux_wordAut_spec]
        simp only [glue0rAux_w_cons, glue0rAux_w_nil, mul_one]
        rw [glue0rAux_psi_ofVec]
        rw [glue0rAux_feS_theta7 j hj]
      have hconj : glue0rAux_wordG M [j] * zθ * (glue0rAux_wordG M [j])⁻¹ = zθ := by
        calc glue0rAux_wordG M [j] * zθ * (glue0rAux_wordG M [j])⁻¹
            = ((((glue0rAux_wordAut M [j] : ↥M.A) : MulAut ↥Bs)
                (⟨zθ, hzθBs⟩ : ↥Bs) : ↥Bs) : G) := by
              rw [glue0rAux_wordG_conj]
          _ = zθ := by
              have := congrArg (fun b : ↥Bs => (b : G)) hfix
              simpa [zθ] using this
      calc glue0rAux_wordG M [j] * zθ
          = (glue0rAux_wordG M [j] * zθ * (glue0rAux_wordG M [j])⁻¹) *
              glue0rAux_wordG M [j] := by group
        _ = zθ * glue0rAux_wordG M [j] := by rw [hconj]
    have hconjW : ((glue0rAux_conjElem M [j] bg : ↥Bs) : G) ∈ W :=
      hH (glue0rAux_wordG M [j]) hmem bg hyb
    have hsymm : M.ψ.symm ((feS 7 j).mulVec y) =
        Additive.ofMul (glue0rAux_conjElem M [j] bg) := by
      rw [hyψ]
      exact glue0rAux_psi_symm_feS M j bg
    rw [hsymm]
    simpa using hconjW
  by_cases hS : S = AddSubgroup.zmultiples glue0rAux_theta7
  · left
    apply le_antisymm ?_ (Subgroup.zpowers_le.mpr hθ)
    intro w hw
    have hwS : M.ψ (Additive.ofMul (⟨w, hWB hw⟩ : ↥Bs)) ∈ S := by
      rw [show S = glue0rAux_imageSub M W hWB from rfl, glue0rAux_mem_imageSub]
      simpa using hw
    rw [hS] at hwS
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hwS
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    have hEq : Additive.ofMul (⟨w, hWB hw⟩ : ↥Bs) =
        n • Additive.ofMul (⟨zθ, hzθBs⟩ : ↥Bs) := by
      apply M.ψ.injective
      rw [map_zsmul]
      have hψθ : M.ψ (Additive.ofMul (⟨zθ, hzθBs⟩ : ↥Bs)) = glue0rAux_theta7 := by
        simp [zθ, glue0rAux_psi_ofVec]
      rw [hψθ]
      exact hn.symm
    have hwpow : w = zθ ^ n := by
      have := congrArg (fun x : ↥Bs => (x : G)) (congrArg Additive.toMul hEq)
      simpa [zθ] using this
    exact hwpow.symm
  · right
    have hzle : AddSubgroup.zmultiples glue0rAux_theta7 ≤ S :=
      AddSubgroup.zmultiples_le.mpr hthetaS
    have hlt : AddSubgroup.zmultiples glue0rAux_theta7 < S :=
      lt_of_le_of_ne hzle (Ne.symm hS)
    obtain ⟨y, hyS, hyz⟩ := Set.exists_of_ssubset hlt
    obtain ⟨k, hk, hyk⟩ := glue0rAux_coord_ne_zero7 hyz
    have hCk : glue0rAux_col 7 k ∈ S := by
      have hs : (feS 7 k).mulVec y ∈ S := hclosed k hk y hyS
      have hdiff : y - (feS 7 k).mulVec y ∈ S := S.sub_mem hyS hs
      rw [feS_mulVec, ← glue0rAux_col_eq_feCol] at hdiff
      have hdiff' : y k • glue0rAux_col 7 k ∈ S := by
        convert hdiff using 1
        abel
      have hmem := glue0rAux_zmod_smul_mem S hdiff' (y k)⁻¹
      have hinv : (y k)⁻¹ • (y k • glue0rAux_col 7 k) = glue0rAux_col 7 k := by
        rw [smul_smul, inv_mul_cancel₀ hyk, one_smul]
      simpa [hinv] using hmem
    have hC : ∀ l : Fin 7, l ≠ 0 → glue0rAux_col 7 l ∈ S :=
      glue0rAux_cols7_of_one S hclosed hk hCk
    have hStop : S = ⊤ := glue0rAux_span7 S hthetaS hC
    have hBW : Bs ≤ W := by
      intro b hb
      have hbS : M.ψ (Additive.ofMul (⟨b, hb⟩ : ↥Bs)) ∈ S := by
        rw [hStop]
        trivial
      rw [show S = glue0rAux_imageSub M W hWB from rfl, glue0rAux_mem_imageSub] at hbS
      simpa using hbS
    exact le_antisymm hWB hBW

private theorem glue0rAux_irreducible_theta8 (M : GGFrameModelData Bs 8)
    (W : Subgroup G) (hWB : W ≤ Bs)
    (hθ : (glue0rAux_ofVec M glue0rAux_theta8 : G) ∈ W)
    (hH : ∀ h ∈ Subgroup.normalizer (Bs : Set G) ⊓
        Subgroup.centralizer ({(glue0rAux_ofVec M glue0rAux_theta8 : G)} : Set G),
      ∀ w ∈ W, h * w * h⁻¹ ∈ W) :
    W = Subgroup.zpowers (glue0rAux_ofVec M glue0rAux_theta8 : G) ∨
      W = Bs := by
  let zθ : G := glue0rAux_ofVec M glue0rAux_theta8
  let S : AddSubgroup (FEVec 8) := glue0rAux_imageSub M W hWB
  have hzθBs : zθ ∈ Bs := hWB hθ
  have hthetaS : glue0rAux_theta8 ∈ S := by
    rw [show S = glue0rAux_imageSub M W hWB from rfl, glue0rAux_mem_imageSub]
    have hsymm : M.ψ.symm glue0rAux_theta8 =
        Additive.ofMul (⟨zθ, hzθBs⟩ : ↥Bs) := by
      apply M.ψ.injective
      simp [zθ, glue0rAux_psi_ofVec]
    rw [hsymm]
    simpa [zθ] using hθ
  have hclosed : ∀ j : Fin 8, j ≠ 7 → ∀ y ∈ S, (feS 8 j).mulVec y ∈ S := by
    intro j hj y hy
    rw [show S = glue0rAux_imageSub M W hWB from rfl, glue0rAux_mem_imageSub] at hy ⊢
    let b : Additive ↥Bs := M.ψ.symm y
    let bg : ↥Bs := Additive.toMul b
    have hyb : (bg : G) ∈ W := by simpa [bg, b] using hy
    have hyψ : y = M.ψ b := by simp [b]
    have hmem : glue0rAux_wordG M [j] ∈
        Subgroup.normalizer (Bs : Set G) ⊓
          Subgroup.centralizer ({(glue0rAux_ofVec M glue0rAux_theta8 : G)} : Set G) := by
      rw [Subgroup.mem_inf]
      refine ⟨glue0rAux_wordG_mem M [j], ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hfix : ((glue0rAux_wordAut M [j] : ↥M.A) : MulAut ↥Bs)
          (glue0rAux_ofVec M glue0rAux_theta8) =
          glue0rAux_ofVec M glue0rAux_theta8 := by
        apply_fun fun b : ↥Bs => M.ψ (Additive.ofMul b) using
          fun a b hab => Additive.ofMul.injective (M.ψ.injective hab)
        change M.ψ (Additive.ofMul (((glue0rAux_wordAut M [j] : ↥M.A) : MulAut ↥Bs)
          (glue0rAux_ofVec M glue0rAux_theta8))) =
          M.ψ (Additive.ofMul (glue0rAux_ofVec M glue0rAux_theta8))
        rw [← M.act (glue0rAux_wordAut M [j]) (glue0rAux_ofVec M glue0rAux_theta8)]
        rw [glue0rAux_wordAut_spec]
        simp only [glue0rAux_w_cons, glue0rAux_w_nil, mul_one]
        rw [glue0rAux_psi_ofVec]
        rw [glue0rAux_feS_theta8 j hj]
      have hconj : glue0rAux_wordG M [j] * zθ * (glue0rAux_wordG M [j])⁻¹ = zθ := by
        calc glue0rAux_wordG M [j] * zθ * (glue0rAux_wordG M [j])⁻¹
            = ((((glue0rAux_wordAut M [j] : ↥M.A) : MulAut ↥Bs)
                (⟨zθ, hzθBs⟩ : ↥Bs) : ↥Bs) : G) := by
              rw [glue0rAux_wordG_conj]
          _ = zθ := by
              have := congrArg (fun b : ↥Bs => (b : G)) hfix
              simpa [zθ] using this
      calc glue0rAux_wordG M [j] * zθ
          = (glue0rAux_wordG M [j] * zθ * (glue0rAux_wordG M [j])⁻¹) *
              glue0rAux_wordG M [j] := by group
        _ = zθ * glue0rAux_wordG M [j] := by rw [hconj]
    have hconjW : ((glue0rAux_conjElem M [j] bg : ↥Bs) : G) ∈ W :=
      hH (glue0rAux_wordG M [j]) hmem bg hyb
    have hsymm : M.ψ.symm ((feS 8 j).mulVec y) =
        Additive.ofMul (glue0rAux_conjElem M [j] bg) := by
      rw [hyψ]
      exact glue0rAux_psi_symm_feS M j bg
    rw [hsymm]
    simpa using hconjW
  by_cases hS : S = AddSubgroup.zmultiples glue0rAux_theta8
  · left
    apply le_antisymm ?_ (Subgroup.zpowers_le.mpr hθ)
    intro w hw
    have hwS : M.ψ (Additive.ofMul (⟨w, hWB hw⟩ : ↥Bs)) ∈ S := by
      rw [show S = glue0rAux_imageSub M W hWB from rfl, glue0rAux_mem_imageSub]
      simpa using hw
    rw [hS] at hwS
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hwS
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    have hEq : Additive.ofMul (⟨w, hWB hw⟩ : ↥Bs) =
        n • Additive.ofMul (⟨zθ, hzθBs⟩ : ↥Bs) := by
      apply M.ψ.injective
      rw [map_zsmul]
      have hψθ : M.ψ (Additive.ofMul (⟨zθ, hzθBs⟩ : ↥Bs)) = glue0rAux_theta8 := by
        simp [zθ, glue0rAux_psi_ofVec]
      rw [hψθ]
      exact hn.symm
    have hwpow : w = zθ ^ n := by
      have := congrArg (fun x : ↥Bs => (x : G)) (congrArg Additive.toMul hEq)
      simpa [zθ] using this
    exact hwpow.symm
  · right
    have hzle : AddSubgroup.zmultiples glue0rAux_theta8 ≤ S :=
      AddSubgroup.zmultiples_le.mpr hthetaS
    have hlt : AddSubgroup.zmultiples glue0rAux_theta8 < S :=
      lt_of_le_of_ne hzle (Ne.symm hS)
    obtain ⟨y, hyS, hyz⟩ := Set.exists_of_ssubset hlt
    obtain ⟨k, hk, hyk⟩ := glue0rAux_coord_ne_zero8 hyz
    have hCk : glue0rAux_col 8 k ∈ S := by
      have hs : (feS 8 k).mulVec y ∈ S := hclosed k hk y hyS
      have hdiff : y - (feS 8 k).mulVec y ∈ S := S.sub_mem hyS hs
      rw [feS_mulVec, ← glue0rAux_col_eq_feCol] at hdiff
      have hdiff' : y k • glue0rAux_col 8 k ∈ S := by
        convert hdiff using 1
        abel
      have hmem := glue0rAux_zmod_smul_mem S hdiff' (y k)⁻¹
      have hinv : (y k)⁻¹ • (y k • glue0rAux_col 8 k) = glue0rAux_col 8 k := by
        rw [smul_smul, inv_mul_cancel₀ hyk, one_smul]
      simpa [hinv] using hmem
    have hC : ∀ l : Fin 8, l ≠ 7 → glue0rAux_col 8 l ∈ S :=
      glue0rAux_cols8_of_one S hclosed hk hCk
    have hStop : S = ⊤ := glue0rAux_span8 S hthetaS hC
    have hBW : Bs ≤ W := by
      intro b hb
      have hbS : M.ψ (Additive.ofMul (⟨b, hb⟩ : ↥Bs)) ∈ S := by
        rw [hStop]
        trivial
      rw [show S = glue0rAux_imageSub M W hWB from rfl, glue0rAux_mem_imageSub] at hbS
      simpa using hbS
    exact le_antisymm hWB hBW

private theorem glue0rAux_zpowers_conjBy (x g : G) :
    (Subgroup.zpowers x).conjBy g = Subgroup.zpowers (g * x * g⁻¹) := by
  simp [Subgroup.conjBy, MulAut.conj_apply]

private theorem glue0rAux_conjBy_eq_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : H.conjBy g = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp hg

private theorem glue0rAux_mem_conjBy {H : Subgroup G} {g x : G} :
    x ∈ H.conjBy g ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.conjBy, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change g⁻¹ * (MulAut.conj g y) * g ∈ H
    rw [MulAut.conj_apply]
    convert hy using 1
    group
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    change MulAut.conj g (g⁻¹ * x * g) = x
    rw [MulAut.conj_apply]
    group

private theorem glue0rAux_conj_mem_normalizer {H : Subgroup G} {g h : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G))
    (hh : h ∈ Subgroup.normalizer (H : Set G)) :
    g * h * g⁻¹ ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hg hh ⊢
  intro x
  have hx1 : x ∈ H ↔ g⁻¹ * x * g ∈ H := by
    have := (hg (g⁻¹ * x * g)).symm
    simpa [mul_assoc] using this
  calc x ∈ H ↔ g⁻¹ * x * g ∈ H := hx1
    _ ↔ h * (g⁻¹ * x * g) * h⁻¹ ∈ H := hh _
    _ ↔ g * (h * (g⁻¹ * x * g) * h⁻¹) * g⁻¹ ∈ H := hg _
    _ ↔ (g * h * g⁻¹) * x * (g * h * g⁻¹)⁻¹ ∈ H := by
        rw [show g * (h * (g⁻¹ * x * g) * h⁻¹) * g⁻¹ =
          (g * h * g⁻¹) * x * (g * h * g⁻¹)⁻¹ by group]

theorem irreducible_of_isRoot (M : GGFrameModelData Bs n) (hn : n = 7 ∨ n = 8)
    (hBs : IsElemAbelian 3 Bs) {z : G} (hz : M.IsRoot z) :
    ∀ V : Subgroup G, V ≤ Bs → z ∈ V →
      (∀ g ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
        ∀ v ∈ V, g * v * g⁻¹ ∈ V) → V = Subgroup.zpowers z ∨ V = Bs := by
  have _ : IsMulCommutative Bs := hBs.1
  rcases hn with rfl | rfl
  · intro V hVB hzV hInv
    let zθ : G := glue0rAux_ofVec M glue0rAux_theta7
    have hzBs : z ∈ Bs := hz.1
    have hzθroot : M.IsRoot zθ := by simpa [zθ] using glue0rAux_theta7_isRoot M
    have hzθBs : zθ ∈ Bs := hzθroot.1
    have hψz := glue0rAux_root7_classify M hzBs hz
    have hψzθ := glue0rAux_root7_classify M hzθBs hzθroot
    obtain ⟨g0, hg0N, hconj⟩ := glue0rAux_exists_conj_of_word M hzBs hzθBs hψz hψzθ
      (glue0rAux_lTheta7 ++ [0] ++ glue0rAux_lTheta7.reverse) glue0rAux_neg_theta7
    set W : Subgroup G := V.conjBy g0 with hWdef
    have hWB : W ≤ Bs := by
      intro x hx
      rw [hWdef, glue0rAux_mem_conjBy] at hx
      have hxBs : g0⁻¹ * x * g0 ∈ Bs := hVB hx
      have := (Subgroup.mem_normalizer_iff.mp hg0N (g0⁻¹ * x * g0)).mp hxBs
      simpa [mul_assoc] using this
    have hzθW : zθ ∈ W := by
      have hzimg : g0 * z * g0⁻¹ ∈ W := by
        rw [hWdef, glue0rAux_mem_conjBy]
        convert hzV using 1
        group
      rcases hconj with h | h
      · rwa [h] at hzimg
      · have hinv : zθ⁻¹ ∈ W := by rwa [h] at hzimg
        simpa using W.inv_mem hinv
    have hH : ∀ h ∈ Subgroup.normalizer (Bs : Set G) ⊓
        Subgroup.centralizer ({zθ} : Set G), ∀ w ∈ W, h * w * h⁻¹ ∈ W := by
      intro h hh w hw
      rw [hWdef, glue0rAux_mem_conjBy] at hw ⊢
      have hhN : h ∈ Subgroup.normalizer (Bs : Set G) := hh.1
      have hhC : h ∈ Subgroup.centralizer ({zθ} : Set G) := hh.2
      have hk : g0⁻¹ * h * g0 ∈
          Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.mem_inf]
        refine ⟨?_, ?_⟩
        · simpa using glue0rAux_conj_mem_normalizer (Subgroup.inv_mem _ hg0N) hhN
        · rw [Subgroup.mem_centralizer_singleton_iff]
          have hhC' := (Subgroup.mem_centralizer_singleton_iff.mp hhC)
          rcases hconj with hz | hz
          · calc g0⁻¹ * h * g0 * z
                = g0⁻¹ * h * (g0 * z * g0⁻¹) * g0 := by group
              _ = g0⁻¹ * (h * zθ) * g0 := by rw [hz]; group
              _ = g0⁻¹ * (zθ * h) * g0 := by rw [hhC']
              _ = g0⁻¹ * zθ * h * g0 := by group
              _ = z * (g0⁻¹ * h * g0) := by
                  rw [show z = g0⁻¹ * zθ * g0 by rw [← hz]; group]
                  group
          · have hhCinv : h * zθ⁻¹ = zθ⁻¹ * h := by
              have hhC'' : h⁻¹ * zθ = zθ * h⁻¹ := by
                calc h⁻¹ * zθ = h⁻¹ * (zθ * h) * h⁻¹ := by group
                  _ = h⁻¹ * (h * zθ) * h⁻¹ := by rw [← hhC']
                  _ = zθ * h⁻¹ := by group
              calc h * zθ⁻¹ = (zθ * h⁻¹)⁻¹ := by group
                _ = (h⁻¹ * zθ)⁻¹ := by rw [← hhC'']
                _ = zθ⁻¹ * h := by group
            calc g0⁻¹ * h * g0 * z
                = g0⁻¹ * h * (g0 * z * g0⁻¹) * g0 := by group
              _ = g0⁻¹ * (h * zθ⁻¹) * g0 := by rw [hz]; group
              _ = g0⁻¹ * (zθ⁻¹ * h) * g0 := by rw [hhCinv]
              _ = g0⁻¹ * zθ⁻¹ * h * g0 := by group
              _ = z * (g0⁻¹ * h * g0) := by
                  rw [show z = g0⁻¹ * zθ⁻¹ * g0 by rw [← hz]; group]
                  group
      have hmem := hInv (g0⁻¹ * h * g0) hk (g0⁻¹ * w * g0) hw
      convert hmem using 1
      group
    have hW := glue0rAux_irreducible_theta7 M W hWB hzθW hH
    rcases hW with hWzp | hWBs
    · left
      calc V = (V.conjBy g0).conjBy g0⁻¹ := (Subgroup.conjBy_inv V g0).symm
        _ = W.conjBy g0⁻¹ := by rw [← hWdef]
        _ = (Subgroup.zpowers zθ).conjBy g0⁻¹ := by rw [hWzp]
        _ = Subgroup.zpowers (g0⁻¹ * zθ * g0) := by
            simpa using glue0rAux_zpowers_conjBy zθ g0⁻¹
        _ = Subgroup.zpowers z := by
            rcases hconj with h | h
            · have hz' : g0⁻¹ * zθ * g0 = z := by
                rw [← h]
                group
              rw [hz']
            · have hz' : g0⁻¹ * zθ * g0 = z⁻¹ := by
                rw [show zθ = (g0 * z * g0⁻¹)⁻¹ by rw [h]; group]
                group
              rw [hz', Subgroup.zpowers_inv]
    · right
      calc V = (V.conjBy g0).conjBy g0⁻¹ := (Subgroup.conjBy_inv V g0).symm
        _ = W.conjBy g0⁻¹ := by rw [← hWdef]
        _ = Bs.conjBy g0⁻¹ := by rw [hWBs]
        _ = Bs := glue0rAux_conjBy_eq_of_mem_normalizer (Subgroup.inv_mem _ hg0N)
  · intro V hVB hzV hInv
    let zθ : G := glue0rAux_ofVec M glue0rAux_theta8
    have hzBs : z ∈ Bs := hz.1
    have hzθroot : M.IsRoot zθ := by simpa [zθ] using glue0rAux_theta8_isRoot M
    have hzθBs : zθ ∈ Bs := hzθroot.1
    have hψz := glue0rAux_root8_classify M hzBs hz
    have hψzθ := glue0rAux_root8_classify M hzθBs hzθroot
    obtain ⟨g0, hg0N, hconj⟩ := glue0rAux_exists_conj_of_word M hzBs hzθBs hψz hψzθ
      (glue0rAux_lTheta8 ++ [0] ++ glue0rAux_lTheta8.reverse) glue0rAux_neg_theta8
    set W : Subgroup G := V.conjBy g0 with hWdef
    have hWB : W ≤ Bs := by
      intro x hx
      rw [hWdef, glue0rAux_mem_conjBy] at hx
      have hxBs : g0⁻¹ * x * g0 ∈ Bs := hVB hx
      have := (Subgroup.mem_normalizer_iff.mp hg0N (g0⁻¹ * x * g0)).mp hxBs
      simpa [mul_assoc] using this
    have hzθW : zθ ∈ W := by
      have hzimg : g0 * z * g0⁻¹ ∈ W := by
        rw [hWdef, glue0rAux_mem_conjBy]
        convert hzV using 1
        group
      rcases hconj with h | h
      · rwa [h] at hzimg
      · have hinv : zθ⁻¹ ∈ W := by rwa [h] at hzimg
        simpa using W.inv_mem hinv
    have hH : ∀ h ∈ Subgroup.normalizer (Bs : Set G) ⊓
        Subgroup.centralizer ({zθ} : Set G), ∀ w ∈ W, h * w * h⁻¹ ∈ W := by
      intro h hh w hw
      rw [hWdef, glue0rAux_mem_conjBy] at hw ⊢
      have hhN : h ∈ Subgroup.normalizer (Bs : Set G) := hh.1
      have hhC : h ∈ Subgroup.centralizer ({zθ} : Set G) := hh.2
      have hk : g0⁻¹ * h * g0 ∈
          Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.mem_inf]
        refine ⟨?_, ?_⟩
        · simpa using glue0rAux_conj_mem_normalizer (Subgroup.inv_mem _ hg0N) hhN
        · rw [Subgroup.mem_centralizer_singleton_iff]
          have hhC' := (Subgroup.mem_centralizer_singleton_iff.mp hhC)
          rcases hconj with hz | hz
          · calc g0⁻¹ * h * g0 * z
                = g0⁻¹ * h * (g0 * z * g0⁻¹) * g0 := by group
              _ = g0⁻¹ * (h * zθ) * g0 := by rw [hz]; group
              _ = g0⁻¹ * (zθ * h) * g0 := by rw [hhC']
              _ = g0⁻¹ * zθ * h * g0 := by group
              _ = z * (g0⁻¹ * h * g0) := by
                  rw [show z = g0⁻¹ * zθ * g0 by rw [← hz]; group]
                  group
          · have hhCinv : h * zθ⁻¹ = zθ⁻¹ * h := by
              have hhC'' : h⁻¹ * zθ = zθ * h⁻¹ := by
                calc h⁻¹ * zθ = h⁻¹ * (zθ * h) * h⁻¹ := by group
                  _ = h⁻¹ * (h * zθ) * h⁻¹ := by rw [← hhC']
                  _ = zθ * h⁻¹ := by group
              calc h * zθ⁻¹ = (zθ * h⁻¹)⁻¹ := by group
                _ = (h⁻¹ * zθ)⁻¹ := by rw [← hhC'']
                _ = zθ⁻¹ * h := by group
            calc g0⁻¹ * h * g0 * z
                = g0⁻¹ * h * (g0 * z * g0⁻¹) * g0 := by group
              _ = g0⁻¹ * (h * zθ⁻¹) * g0 := by rw [hz]; group
              _ = g0⁻¹ * (zθ⁻¹ * h) * g0 := by rw [hhCinv]
              _ = g0⁻¹ * zθ⁻¹ * h * g0 := by group
              _ = z * (g0⁻¹ * h * g0) := by
                  rw [show z = g0⁻¹ * zθ⁻¹ * g0 by rw [← hz]; group]
                  group
      have hmem := hInv (g0⁻¹ * h * g0) hk (g0⁻¹ * w * g0) hw
      convert hmem using 1
      group
    have hW := glue0rAux_irreducible_theta8 M W hWB hzθW hH
    rcases hW with hWzp | hWBs
    · left
      calc V = (V.conjBy g0).conjBy g0⁻¹ := (Subgroup.conjBy_inv V g0).symm
        _ = W.conjBy g0⁻¹ := by rw [← hWdef]
        _ = (Subgroup.zpowers zθ).conjBy g0⁻¹ := by rw [hWzp]
        _ = Subgroup.zpowers (g0⁻¹ * zθ * g0) := by
            simpa using glue0rAux_zpowers_conjBy zθ g0⁻¹
        _ = Subgroup.zpowers z := by
            rcases hconj with h | h
            · have hz' : g0⁻¹ * zθ * g0 = z := by
                rw [← h]
                group
              rw [hz']
            · have hz' : g0⁻¹ * zθ * g0 = z⁻¹ := by
                rw [show zθ = (g0 * z * g0⁻¹)⁻¹ by rw [h]; group]
                group
              rw [hz', Subgroup.zpowers_inv]
    · right
      calc V = (V.conjBy g0).conjBy g0⁻¹ := (Subgroup.conjBy_inv V g0).symm
        _ = W.conjBy g0⁻¹ := by rw [← hWdef]
        _ = Bs.conjBy g0⁻¹ := by rw [hWBs]
        _ = Bs := glue0rAux_conjBy_eq_of_mem_normalizer (Subgroup.inv_mem _ hg0N)

theorem exists_conj_of_isRoot (M : GGFrameModelData Bs n) (hn : n = 7 ∨ n = 8)
    (hBs : IsElemAbelian 3 Bs) {z z' : G} (hz : M.IsRoot z) (hz' : M.IsRoot z') :
    ∃ g ∈ Subgroup.normalizer (Bs : Set G), g * z * g⁻¹ = z' ∨ g * z * g⁻¹ = z'⁻¹ := by
  have _ : IsMulCommutative Bs := hBs.1
  rcases hn with rfl | rfl
  · obtain ⟨negWord, hneg⟩ := glue0rAux_exists_negWord7
    exact glue0rAux_exists_conj_of_word (theta := glue0rAux_theta7) M hz.1 hz'.1
      (glue0rAux_root7_classify M hz.1 hz)
      (glue0rAux_root7_classify M hz'.1 hz') negWord hneg
  · obtain ⟨negWord, hneg⟩ := glue0rAux_exists_negWord8
    exact glue0rAux_exists_conj_of_word (theta := glue0rAux_theta8) M hz.1 hz'.1
      (glue0rAux_root8_classify M hz.1 hz)
      (glue0rAux_root8_classify M hz'.1 hz') negWord hneg

theorem exists_isRoot_mem_of_index_three (M : GGFrameModelData Bs n) (hn : n = 7 ∨ n = 8)
    (hBs : IsElemAbelian 3 Bs) {F : Subgroup G} (hF : F ≤ Bs)
    (hcard : Nat.card Bs = 3 * Nat.card F) : ∃ z ∈ F, M.IsRoot z := by
  rcases hn with rfl | rfl
  · by_contra hno
    have : Finite Bs :=
      Finite.of_injective (fun b : ↥Bs => M.ψ (Additive.ofMul b))
        (fun a b h => Additive.ofMul.injective (M.ψ.injective h))
    have : Finite F :=
      Finite.of_injective (fun x : ↥F => (⟨(x : G), hF x.2⟩ : ↥Bs))
        (fun a b h => Subtype.ext (congrArg (fun x : ↥Bs => (x : G)) h))
    have : IsMulCommutative ↥Bs := hBs.1
    have : (F.subgroupOf Bs).Normal := Subgroup.normal_of_comm _
    have hno' : ∀ z : G, z ∈ F → ¬ M.IsRoot z := by
      intro z hz hzr
      exact hno ⟨z, hz, hzr⟩
    let Q := ↥Bs ⧸ F.subgroupOf Bs
    have hQcard : Nat.card Q = 3 := by
      rw [← Subgroup.index_eq_card (F.subgroupOf Bs)]
      have hmul := Subgroup.index_mul_card (F.subgroupOf Bs)
      have hsub : Nat.card ↥(F.subgroupOf Bs) = Nat.card F :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF).toEquiv
      rw [hsub, hcard] at hmul
      exact Nat.mul_right_cancel (Nat.card_pos (α := F)) hmul
    let q : ↥Bs →* Q := QuotientGroup.mk' (F.subgroupOf Bs)
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hQcard' : Nat.card (Additive Q) = 3 :=
      (Nat.card_congr Additive.ofMul).symm.trans hQcard
    let e : Additive Q ≃+ ZMod 3 :=
      addEquivOfPrimeCardEq (p := 3) hQcard' (Nat.card_zmod 3)
    let z0 : ↥Bs := glue0rAux_ofVec M (feCol 7 0)
    let z2 : ↥Bs := glue0rAux_ofVec M (feCol 7 2)
    let z3 : ↥Bs := glue0rAux_ofVec M (feCol 7 3)
    let z02 : ↥Bs := glue0rAux_ofVec M ((feS 7 2).mulVec (feCol 7 0))
    let z23 : ↥Bs := glue0rAux_ofVec M ((feS 7 3).mulVec (feCol 7 2))
    let z023 : ↥Bs := glue0rAux_ofVec M
      ((feS 7 3).mulVec ((feS 7 2).mulVec (feCol 7 0)))
    have hz0 : M.IsRoot (z0 : G) := by
      simpa [z0] using glue0rAux_col7_isRoot M 0
    have hz2 : M.IsRoot (z2 : G) := by
      simpa [z2] using glue0rAux_col7_isRoot M 2
    have hz3 : M.IsRoot (z3 : G) := by
      simpa [z3] using glue0rAux_col7_isRoot M 3
    have hz02 : M.IsRoot (z02 : G) := by
      simpa [z02] using glue0rAux_isRoot_smul M 2 (glue0rAux_col7_isRoot M 0)
    have hz23 : M.IsRoot (z23 : G) := by
      simpa [z23] using glue0rAux_isRoot_smul M 3 (glue0rAux_col7_isRoot M 2)
    have hz023 : M.IsRoot (z023 : G) := by
      simpa [z023] using glue0rAux_isRoot_smul M 3 hz02
    have hz02_eq : z02 = z0 * z2 := by
      dsimp [z02, z0, z2]
      rw [glue0rAux_s2_col0_7, glue0rAux_ofVec_add]
    have hz23_eq : z23 = z2 * z3 := by
      dsimp [z23, z2, z3]
      rw [glue0rAux_s3_col2_7, glue0rAux_ofVec_add]
    have hz023_eq : z023 = z02 * z3 := by
      dsimp [z023, z02, z3]
      rw [glue0rAux_s2_col0_7, glue0rAux_s3_col02_7, glue0rAux_ofVec_add]
    have hclass : ∀ z : ↥Bs, M.IsRoot (z : G) → q z ≠ 1 := by
      intro z hzr hq
      dsimp [q] at hq
      change (QuotientGroup.mk z : Q) = 1 at hq
      rw [QuotientGroup.eq_one_iff] at hq
      rw [Subgroup.mem_subgroupOf] at hq
      exact hno' (z : G) hq hzr
    have hzero : ∀ z : ↥Bs, M.IsRoot (z : G) →
        e (Additive.ofMul (q z)) ≠ 0 := by
      intro z hzr h
      have h' : Additive.ofMul (q z) = 0 := e.injective (by simpa using h)
      exact hclass z hzr (by simpa using congrArg Additive.toMul h')
    let a : ZMod 3 := e (Additive.ofMul (q z0))
    let b : ZMod 3 := e (Additive.ofMul (q z2))
    let c : ZMod 3 := e (Additive.ofMul (q z3))
    have ha : a ≠ 0 := by simpa [a] using hzero z0 hz0
    have hb : b ≠ 0 := by simpa [b] using hzero z2 hz2
    have hc : c ≠ 0 := by simpa [c] using hzero z3 hz3
    have hq02 : Additive.ofMul (q z02) =
        Additive.ofMul (q z0) + Additive.ofMul (q z2) := by
      rw [hz02_eq, map_mul, ofMul_mul]
    have hq23 : Additive.ofMul (q z23) =
        Additive.ofMul (q z2) + Additive.ofMul (q z3) := by
      rw [hz23_eq, map_mul, ofMul_mul]
    have hq023 : Additive.ofMul (q z023) =
        Additive.ofMul (q z02) + Additive.ofMul (q z3) := by
      rw [hz023_eq, map_mul, ofMul_mul]
    have he02 : e (Additive.ofMul (q z02)) = a + b := by
      rw [hq02]
      simp [a, b]
    have he23 : e (Additive.ofMul (q z23)) = b + c := by
      rw [hq23]
      simp [b, c]
    have he023 : e (Additive.ofMul (q z023)) = a + b + c := by
      rw [hq023, map_add, he02]
    have hab : a + b ≠ 0 := by
      intro h
      have := hzero z02 hz02
      rw [he02] at this
      exact this h
    have hbc : b + c ≠ 0 := by
      intro h
      have := hzero z23 hz23
      rw [he23] at this
      exact this h
    have habc : a + b + c ≠ 0 := by
      intro h
      have := hzero z023 hz023
      rw [he023] at this
      exact this h
    exact glue0rAux_zmod3_no_six a b c ha hb hc hab hbc habc
  · by_contra hno
    have : Finite Bs :=
      Finite.of_injective (fun b : ↥Bs => M.ψ (Additive.ofMul b))
        (fun a b h => Additive.ofMul.injective (M.ψ.injective h))
    have : Finite F :=
      Finite.of_injective (fun x : ↥F => (⟨(x : G), hF x.2⟩ : ↥Bs))
        (fun a b h => Subtype.ext (congrArg (fun x : ↥Bs => (x : G)) h))
    have : IsMulCommutative ↥Bs := hBs.1
    have : (F.subgroupOf Bs).Normal := Subgroup.normal_of_comm _
    have hno' : ∀ z : G, z ∈ F → ¬ M.IsRoot z := by
      intro z hz hzr
      exact hno ⟨z, hz, hzr⟩
    let Q := ↥Bs ⧸ F.subgroupOf Bs
    have hQcard : Nat.card Q = 3 := by
      rw [← Subgroup.index_eq_card (F.subgroupOf Bs)]
      have hmul := Subgroup.index_mul_card (F.subgroupOf Bs)
      have hsub : Nat.card ↥(F.subgroupOf Bs) = Nat.card F :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF).toEquiv
      rw [hsub, hcard] at hmul
      exact Nat.mul_right_cancel (Nat.card_pos (α := F)) hmul
    let q : ↥Bs →* Q := QuotientGroup.mk' (F.subgroupOf Bs)
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hQcard' : Nat.card (Additive Q) = 3 :=
      (Nat.card_congr Additive.ofMul).symm.trans hQcard
    let e : Additive Q ≃+ ZMod 3 :=
      addEquivOfPrimeCardEq (p := 3) hQcard' (Nat.card_zmod 3)
    let z0 : ↥Bs := glue0rAux_ofVec M (feCol 8 0)
    let z2 : ↥Bs := glue0rAux_ofVec M (feCol 8 2)
    let z3 : ↥Bs := glue0rAux_ofVec M (feCol 8 3)
    let z02 : ↥Bs := glue0rAux_ofVec M ((feS 8 2).mulVec (feCol 8 0))
    let z23 : ↥Bs := glue0rAux_ofVec M ((feS 8 3).mulVec (feCol 8 2))
    let z023 : ↥Bs := glue0rAux_ofVec M
      ((feS 8 3).mulVec ((feS 8 2).mulVec (feCol 8 0)))
    have hz0 : M.IsRoot (z0 : G) := by
      simpa [z0] using glue0rAux_col8_isRoot M 0
    have hz2 : M.IsRoot (z2 : G) := by
      simpa [z2] using glue0rAux_col8_isRoot M 2
    have hz3 : M.IsRoot (z3 : G) := by
      simpa [z3] using glue0rAux_col8_isRoot M 3
    have hz02 : M.IsRoot (z02 : G) := by
      simpa [z02] using glue0rAux_isRoot_smul M 2 (glue0rAux_col8_isRoot M 0)
    have hz23 : M.IsRoot (z23 : G) := by
      simpa [z23] using glue0rAux_isRoot_smul M 3 (glue0rAux_col8_isRoot M 2)
    have hz023 : M.IsRoot (z023 : G) := by
      simpa [z023] using glue0rAux_isRoot_smul M 3 hz02
    have hz02_eq : z02 = z0 * z2 := by
      dsimp [z02, z0, z2]
      rw [glue0rAux_s2_col0_8, glue0rAux_ofVec_add]
    have hz23_eq : z23 = z2 * z3 := by
      dsimp [z23, z2, z3]
      rw [glue0rAux_s3_col2_8, glue0rAux_ofVec_add]
    have hz023_eq : z023 = z02 * z3 := by
      dsimp [z023, z02, z3]
      rw [glue0rAux_s2_col0_8, glue0rAux_s3_col02_8, glue0rAux_ofVec_add]
    have hclass : ∀ z : ↥Bs, M.IsRoot (z : G) → q z ≠ 1 := by
      intro z hzr hq
      dsimp [q] at hq
      change (QuotientGroup.mk z : Q) = 1 at hq
      rw [QuotientGroup.eq_one_iff] at hq
      rw [Subgroup.mem_subgroupOf] at hq
      exact hno' (z : G) hq hzr
    have hzero : ∀ z : ↥Bs, M.IsRoot (z : G) →
        e (Additive.ofMul (q z)) ≠ 0 := by
      intro z hzr h
      have h' : Additive.ofMul (q z) = 0 := e.injective (by simpa using h)
      exact hclass z hzr (by simpa using congrArg Additive.toMul h')
    let a : ZMod 3 := e (Additive.ofMul (q z0))
    let b : ZMod 3 := e (Additive.ofMul (q z2))
    let c : ZMod 3 := e (Additive.ofMul (q z3))
    have ha : a ≠ 0 := by simpa [a] using hzero z0 hz0
    have hb : b ≠ 0 := by simpa [b] using hzero z2 hz2
    have hc : c ≠ 0 := by simpa [c] using hzero z3 hz3
    have hq02 : Additive.ofMul (q z02) =
        Additive.ofMul (q z0) + Additive.ofMul (q z2) := by
      rw [hz02_eq, map_mul, ofMul_mul]
    have hq23 : Additive.ofMul (q z23) =
        Additive.ofMul (q z2) + Additive.ofMul (q z3) := by
      rw [hz23_eq, map_mul, ofMul_mul]
    have hq023 : Additive.ofMul (q z023) =
        Additive.ofMul (q z02) + Additive.ofMul (q z3) := by
      rw [hz023_eq, map_mul, ofMul_mul]
    have he02 : e (Additive.ofMul (q z02)) = a + b := by
      rw [hq02]
      simp [a, b]
    have he23 : e (Additive.ofMul (q z23)) = b + c := by
      rw [hq23]
      simp [b, c]
    have he023 : e (Additive.ofMul (q z023)) = a + b + c := by
      rw [hq023, map_add, he02]
    have hab : a + b ≠ 0 := by
      intro h
      have := hzero z02 hz02
      rw [he02] at this
      exact this h
    have hbc : b + c ≠ 0 := by
      intro h
      have := hzero z23 hz23
      rw [he23] at this
      exact this h
    have habc : a + b + c ≠ 0 := by
      intro h
      have := hzero z023 hz023
      rw [he023] at this
      exact this h
    exact glue0rAux_zmod3_no_six a b c ha hb hc hab hbc habc

end GGFrameModelData

end CFSG.StandardType.FrameRoute
