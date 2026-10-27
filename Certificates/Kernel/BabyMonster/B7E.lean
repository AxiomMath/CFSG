module

public import CFSG.Certificates.Kernel.BabyMonster.B7EFact
public import Certificates.Kernel.BabyMonster.SevenLocal

public section

namespace CertificateChecks.KernelBM.B7E

open CFSG.KC.BM CFSG.KC.BM.SevenFacts CertificateChecks.KernelBM.SevenFacts

set_option maxRecDepth 100000

theorem conj_comm {n : ℕ} {A Y T : Matrix (Fin n) (Fin n) (ZMod 2)} (hY : A * Y = Y * A)
    (hT : A * T = T * A) : A * (Y ^ 3 * T * Y ^ 2) = Y ^ 3 * T * Y ^ 2 * A :=
  (((Commute.pow_right hY 3).mul_right hT).mul_right (Commute.pow_right hY 2)).eq

theorem ne_one_of_rank {n : ℕ} {T : Matrix (Fin n) (Fin n) (ZMod 2)} {r : ℕ}
    (h : (T - 1).rank = r) (hr : r ≠ 0) : T ≠ 1 := by
  rintro rfl
  rw [sub_self, Matrix.rank_zero] at h
  exact hr h.symm

theorem conj_ne {n : ℕ} {A Y T : Matrix (Fin n) (Fin n) (ZMod 2)} (hy5 : Y ^ 5 = 1)
    (hAY : A * Y = Y * A) (hTA : T ≠ A) : Y ^ 3 * T * Y ^ 2 ≠ A := by
  intro e
  apply hTA
  have e5 : Y ^ 2 * Y ^ 3 = 1 := by
    rw [← pow_add]
    exact hy5
  calc T = Y ^ 2 * Y ^ 3 * T * (Y ^ 2 * Y ^ 3) := by rw [e5, one_mul, mul_one]
    _ = Y ^ 2 * (Y ^ 3 * T * Y ^ 2) * Y ^ 3 := by simp only [mul_assoc]
    _ = Y ^ 2 * A * Y ^ 3 := by rw [e]
    _ = A * Y ^ 2 * Y ^ 3 := by rw [← (Commute.pow_right hAY 2).eq]
    _ = A := by rw [mul_assoc, e5, mul_one]

theorem sq_ne {n : ℕ} {T E A : Matrix (Fin n) (Fin n) (ZMod 2)} (hT : T * T = 1)
    (hTE : E * T = T * E) (hE3 : E ^ 3 = 1) (hE1 : E ≠ 1) (hA : A * A = 1) :
    T * E * (T * E) ≠ A := by
  intro e
  have hsq : T * E * (T * E) = E * E := by
    calc T * E * (T * E) = T * (E * T) * E := by simp only [mul_assoc]
      _ = T * (T * E) * E := by rw [hTE]
      _ = E * E := by rw [← mul_assoc T T E, hT, one_mul]
  rw [hsq] at e
  apply hE1
  calc E = E ^ 3 * E := by rw [hE3, one_mul]
    _ = E * E * (E * E) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := by rw [e, hA]

theorem ty_ne {n : ℕ} {T Y : Matrix (Fin n) (Fin n) (ZMod 2)} (hT : T * T = 1) (hy5 : Y ^ 5 = 1)
    (h : T * Y * T * Y ^ 4 ≠ 1) : T * Y ≠ Y * T := by
  intro e
  apply h
  have hy : Y * Y ^ 4 = 1 := by
    rw [← pow_succ']
    exact hy5
  calc T * Y * T * Y ^ 4 = Y * T * T * Y ^ 4 := by rw [e]
    _ = Y * Y ^ 4 := by rw [mul_assoc Y T T, hT, mul_one]
    _ = 1 := hy

theorem ty_ne_al {n : ℕ} {T Y A : Matrix (Fin n) (Fin n) (ZMod 2)} (hT : T * T = 1)
    (hy5 : Y ^ 5 = 1) (h : T * Y * T * Y ^ 4 ≠ A) : T * Y ≠ A * Y * T := by
  intro e
  apply h
  have hy : Y * Y ^ 4 = 1 := by
    rw [← pow_succ']
    exact hy5
  calc T * Y * T * Y ^ 4 = A * Y * T * T * Y ^ 4 := by rw [e]
    _ = A * (Y * Y ^ 4) := by rw [mul_assoc (A * Y) T T, hT, mul_one, mul_assoc]
    _ = A := by rw [hy, mul_one]

theorem fact16962 :
    SevenWords ∧ Fact16962Of (stripMat Seven.al) (stripMat Seven.x) (stripMat Seven.y)
      (stripMat Seven.t1) (stripMat Seven.t2) (stripMat Seven.e3) := by
  obtain ⟨hw, h⟩ := fact17101
  obtain ⟨-, -, -, -, -, -, -, hrk, -⟩ := fact17450
  obtain ⟨hA2, hA1, hrA, hAX, hAY, hX7, hX1, hY5, hY1, hXY, hT1, hrT1, hT1X, hT1A, hT1ne, hT2,
    hrT2, hT2X, hT12, hT12ne, hrT12, hE3, hE1, hEX, hET1, hEA, hW6, hW2, hW3, hc1, hcA⟩ := h
  have ht2 := hw.2.2.2
  unfold Fact16962Of
  refine ⟨hw, hA2, hA1, hrA, hAX, hAY, hT1A.symm, ?_, hEA.symm, hX7, hX1, hY5, hY1, hXY, hT1,
    ne_one_of_rank hrT1 (by norm_num), hT2, ne_one_of_rank hrT2 (by norm_num), hT12ne, hT12, hT1X,
    hT2X, hrT1, hrT2, hrT12, hrk, hT1ne, ?_, hE3, hE1, hEX, hET1, hW6, hW3, ?_,
    sq_ne hT1 hET1 hE3 hE1 hA2, ty_ne hT1 hY5 hc1, ty_ne_al hT1 hY5 hcA⟩
  · rw [ht2]
    exact conj_comm hAY hT1A.symm
  · rw [ht2]
    exact conj_ne hY5 hAY hT1ne
  · rw [← sq]
    exact hW2

end CertificateChecks.KernelBM.B7E

end
