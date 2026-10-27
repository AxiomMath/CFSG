module

public import CFSG.RankThree.PartOne.S13K.Sp6Conj

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.RankThree.PartOne.KFQ
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem dBlk_apply {g : ↥(M10 K)} (hg : g ∈ dBlk K) (v : QV K (Fin 3)) :
    g.1 v 0 = dMat g.1 0 0 * v 0 + dMat g.1 0 1 * v 1 ∧
      g.1 v 1 = dMat g.1 1 0 * v 0 + dMat g.1 1 1 * v 1 ∧ g.1 v 2 = v 2 := by
  set u : QV K (Fin 3) := v - sg 2 (v 2) with hu
  have hu2 : u 2 = 0 := by simp [hu]
  have hv : g.1 v = g.1 u + sg 2 (v 2) := by
    have h1 : v = u + sg 2 (v 2) := by simp [hu]
    conv_lhs => rw [h1]
    rw [map_add, hg.1]
  have hu0 : u 0 = v 0 := by simp [hu]
  have hu1 : u 1 = v 1 := by simp [hu]
  refine ⟨?_, ?_, ?_⟩
  · rw [hv, Pi.add_apply, UPres_apply0 hg.2.1 hu2, hu0, hu1]
    simp
  · rw [hv, Pi.add_apply, UPres_apply1 hg.2.1 hu2, hu0, hu1]
    simp
  · rw [hv, Pi.add_apply, hg.2.1.1 u hu2]
    simp

theorem dMat_shape {g : ↥(M10 K)} (hg : g ∈ dBlk K) :
    frobQ K (dMat g.1 0 0) = dMat g.1 1 1 ∧ frobQ K (dMat g.1 0 1) = dMat g.1 1 0 := by
  have h1 := dMat_transpose_mul g.2 hg.2.1
  have hdet := hg.2.2
  set G := dMat g.1 with hG
  have hdetT : Gᵀ.det = 1 := by rw [Matrix.det_transpose]; exact hdet
  have h2 : G.map (frobQ K) = Gᵀ.adjugate := by
    calc G.map (frobQ K) = (Gᵀ.adjugate * Gᵀ) * G.map (frobQ K) := by
          rw [Matrix.adjugate_mul, hdetT, one_smul, one_mul]
      _ = Gᵀ.adjugate * (Gᵀ * G.map (frobQ K)) := by rw [Matrix.mul_assoc]
      _ = Gᵀ.adjugate := by rw [h1, Matrix.mul_one]
  have e00 := congrFun₂ h2 0 0
  have e01 := congrFun₂ h2 0 1
  simp only [Matrix.map_apply, Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.transpose_apply] at e00 e01
  refine ⟨e00, ?_⟩
  rw [e01, CharTwo.neg_eq]

@[expose] noncomputable def gS1 (K : Type) [Field K] [Finite K] [CharP K 2] : ↥(M10 K) :=
  sg10 1 (fun j => decide (j = 1))

theorem gS1_apply (v : QV K (Fin 3)) :
    (gS1 K).1 v 0 = v 0 ∧ (gS1 K).1 v 1 = frobQ K (v 1) ∧ (gS1 K).1 v 2 = v 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [gS1, sg10_apply]

theorem gS1_mul_self : gS1 K * gS1 K = 1 := by
  apply Subtype.ext
  refine LinearEquiv.ext fun v => ?_
  funext i
  change (gS1 K).1 ((gS1 K).1 v) i = v i
  fin_cases i
  · simp [(gS1_apply _).1]
  · simp [(gS1_apply _).2.1, frobQ_frobQ]
  · simp [(gS1_apply _).2.2]

theorem gS1_inv : (gS1 K)⁻¹ = gS1 K := inv_eq_of_mul_eq_one_right gS1_mul_self

theorem dBlk_comm_twist {d d' : ↥(M10 K)} (hd : d ∈ dBlk K) (hd' : d' ∈ dBlk K) :
    d * (gS1 K * d' * gS1 K) = (gS1 K * d' * gS1 K) * d := by
  apply Subtype.ext
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨hM0, hM1⟩ := dMat_shape hd
  obtain ⟨hN0, hN1⟩ := dMat_shape hd'
  have hh : ∀ w : QV K (Fin 3), (gS1 K * d' * gS1 K).1 w 0 =
      dMat d'.1 0 0 * w 0 + dMat d'.1 0 1 * frobQ K (w 1) ∧
      (gS1 K * d' * gS1 K).1 w 1 = frobQ K (dMat d'.1 1 0) * frobQ K (w 0) +
        frobQ K (dMat d'.1 1 1) * w 1 ∧ (gS1 K * d' * gS1 K).1 w 2 = w 2 := by
    intro w
    have e0 := (gS1_apply w)
    have e1 := dBlk_apply hd' ((gS1 K).1 w)
    have e2 := gS1_apply (d'.1 ((gS1 K).1 w))
    change ((gS1 K).1 (d'.1 ((gS1 K).1 w))) 0 = _ ∧ ((gS1 K).1 (d'.1 ((gS1 K).1 w))) 1 = _ ∧
      ((gS1 K).1 (d'.1 ((gS1 K).1 w))) 2 = _
    refine ⟨?_, ?_, ?_⟩
    · rw [e2.1, e1.1, e0.1, e0.2.1]
    · rw [e2.2.1, e1.2.1, e0.1, e0.2.1, map_add, map_mul, map_mul, frobQ_frobQ]
    · rw [e2.2.2, e1.2.2, e0.2.2]
  have hd1 := dBlk_apply hd v
  funext i
  fin_cases i
  · change d.1 ((gS1 K * d' * gS1 K).1 v) 0 = (gS1 K * d' * gS1 K).1 (d.1 v) 0
    rw [(dBlk_apply hd _).1, (hh v).1, (hh v).2.1, (hh (d.1 v)).1, hd1.1, hd1.2.1]
    simp only [map_add, map_mul]
    rw [← hM0, ← hM1, ← hN0, ← hN1]
    simp only [frobQ_frobQ]
    ring
  · change d.1 ((gS1 K * d' * gS1 K).1 v) 1 = (gS1 K * d' * gS1 K).1 (d.1 v) 1
    rw [(dBlk_apply hd _).2.1, (hh v).1, (hh v).2.1, (hh (d.1 v)).2.1, hd1.1, hd1.2.1]
    simp only [map_add, map_mul]
    rw [← hM0, ← hM1, ← hN0, ← hN1]
    simp only [frobQ_frobQ]
    ring
  · change d.1 ((gS1 K * d' * gS1 K).1 v) 2 = (gS1 K * d' * gS1 K).1 (d.1 v) 2
    rw [(dBlk_apply hd _).2.2, (hh v).2.2, (hh (d.1 v)).2.2, hd1.2.2]

end CFSG.RankThree.PartOne.S13K
