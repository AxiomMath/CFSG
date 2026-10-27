module

public import CFSG.Quasithin.Background.F7TwoInvL5TwoGraph

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.GroupTheory.GL52 CFSG.Quasithin.F7Two

private def mul5 (A B : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of fun i j => A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j + A i 3 * B 3 j + A i 4 * B 4 j

private theorem mul5_eq (A B : Matrix (Fin 5) (Fin 5) (ZMod 2)) : mul5 A B = A * B := by
  ext i j
  simp [mul5, Matrix.mul_apply, Fin.sum_univ_five, add_assoc]

private def dot5 (v w : Fin 5 → ZMod 2) : ZMod 2 :=
  v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3 + v 4 * w 4

private theorem dot5_eq (v w : Fin 5 → ZMod 2) : dot5 v w = dotProduct v w := by
  simp [dot5, dotProduct, Fin.sum_univ_five, add_assoc]

private def oddVecs : List (Fin 5 → ZMod 2) :=
  [![0, 0, 0, 0, 1], ![0, 0, 0, 1, 0], ![0, 0, 1, 0, 0], ![0, 0, 1, 1, 1], ![0, 1, 0, 0, 0],
    ![0, 1, 0, 1, 1], ![0, 1, 1, 0, 1], ![0, 1, 1, 1, 0], ![1, 0, 0, 0, 0], ![1, 0, 0, 1, 1],
    ![1, 0, 1, 0, 1], ![1, 0, 1, 1, 0], ![1, 1, 0, 0, 1], ![1, 1, 0, 1, 0], ![1, 1, 1, 0, 0],
    ![1, 1, 1, 1, 1]]

private theorem mem_oddVecs : ∀ v : Fin 5 → ZMod 2, dot5 v v = 1 → v ∈ oddVecs := by
  decide +kernel

private def pm1 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of ![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1],
    ![0, 0, 1, 0, 0]]

private def pm2 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of ![![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 0, 1],
    ![0, 0, 0, 1, 0]]

private def pm3 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of ![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1]]

private theorem pm1_orth : mul5 pm1 pm1.transpose = 1 ∧ mul5 pm1.transpose pm1 = 1 := by
  decide +kernel

private theorem pm2_orth : mul5 pm2 pm2.transpose = 1 ∧ mul5 pm2.transpose pm2 = 1 := by
  decide +kernel

private theorem pm3_orth : mul5 pm3 pm3.transpose = 1 ∧ mul5 pm3.transpose pm3 = 1 := by
  decide +kernel

private def quart (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  mul5 (mul5 M M) (mul5 M M)

private def commM (c M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  mul5 (mul5 c M) (mul5 c.transpose M.transpose)

private def sq5 (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  mul5 M M

private def p8 (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  sq5 (quart M)

private def p16 (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  sq5 (p8 M)

private def p32 (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  sq5 (p16 M)

private def exp60M (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  mul5 (mul5 (p32 M) (p16 M)) (mul5 (p8 M) (quart M))

private def exp60 (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Bool := decide (exp60M M = 1)

private def chk (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Bool :=
  exp60 M && (decide (quart M ≠ 1) || decide (M = 1) ||
    decide (quart (commM pm1 M) ≠ 1) || decide (quart (commM pm2 M) ≠ 1) ||
    decide (quart (commM pm3 M) ≠ 1))

private theorem sq_pow (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) (n : ℕ) :
    M ^ n * M ^ n = M ^ (2 * n) := by
  rw [← pow_add, two_mul]

private theorem quart_eq (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : quart M = M ^ 4 := by
  simp only [quart, mul5_eq]
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]

private theorem exp60_spec {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : exp60 M = true) :
    M ^ 60 = 1 := by
  have h' : exp60M M = 1 := by
    unfold exp60 at h
    exact of_decide_eq_true h
  have e8 : M ^ 4 * M ^ 4 = M ^ 8 := sq_pow M 4
  have e16 : M ^ 8 * M ^ 8 = M ^ 16 := sq_pow M 8
  have e32 : M ^ 16 * M ^ 16 = M ^ 32 := sq_pow M 16
  have e60 : M ^ 32 * M ^ 16 * (M ^ 8 * M ^ 4) = M ^ 60 := by
    rw [← pow_add, ← pow_add, ← pow_add]
  simp only [exp60M, p32, p16, p8, sq5, quart_eq, mul5_eq] at h'
  rw [e8, e16, e32, e60] at h'
  exact h'

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 1000000 in
private theorem orthCheck :
    ∀ r0 ∈ oddVecs, ∀ r1 ∈ oddVecs, dot5 r0 r1 = 0 →
    ∀ r2 ∈ oddVecs, dot5 r0 r2 = 0 → dot5 r1 r2 = 0 →
    ∀ r3 ∈ oddVecs, dot5 r0 r3 = 0 → dot5 r1 r3 = 0 → dot5 r2 r3 = 0 →
    ∀ r4 ∈ oddVecs, dot5 r0 r4 = 0 → dot5 r1 r4 = 0 → dot5 r2 r4 = 0 → dot5 r3 r4 = 0 →
    chk (Matrix.of ![r0, r1, r2, r3, r4]) = true := by
  decide +kernel

private theorem orth_chk (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) (h : M.transpose * M = 1)
    (h' : M * M.transpose = 1) :
    M ^ 60 = 1 ∧ (M ^ 4 = 1 → M ≠ 1 → ∃ c : Matrix (Fin 5) (Fin 5) (ZMod 2),
      c * c.transpose = 1 ∧ c.transpose * c = 1 ∧
      (c * M * c.transpose * M.transpose) ^ 4 ≠ 1) := by
  have hdot : ∀ i j : Fin 5, dot5 (M i) (M j) = (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) i j := by
    intro i j
    rw [dot5_eq, ← h']
    simp [Matrix.mul_apply, dotProduct]
  have hM : M = Matrix.of ![M 0, M 1, M 2, M 3, M 4] := by
    ext i j
    fin_cases i <;> rfl
  have h0 := hdot 0 0
  have h1 := hdot 1 1
  have h2 := hdot 2 2
  have h3 := hdot 3 3
  have h4 := hdot 4 4
  have h01 := hdot 0 1
  have h02 := hdot 0 2
  have h03 := hdot 0 3
  have h04 := hdot 0 4
  have h12 := hdot 1 2
  have h13 := hdot 1 3
  have h14 := hdot 1 4
  have h23 := hdot 2 3
  have h24 := hdot 2 4
  have h34 := hdot 3 4
  simp only [Matrix.one_apply] at h0 h1 h2 h3 h4 h01 h02 h03 h04 h12 h13 h14 h23 h24 h34
  have key := orthCheck (M 0) (mem_oddVecs _ (by simpa using h0)) (M 1)
    (mem_oddVecs _ (by simpa using h1)) (by simpa using h01) (M 2)
    (mem_oddVecs _ (by simpa using h2)) (by simpa using h02) (by simpa using h12) (M 3)
    (mem_oddVecs _ (by simpa using h3)) (by simpa using h03) (by simpa using h13)
    (by simpa using h23) (M 4) (mem_oddVecs _ (by simpa using h4)) (by simpa using h04)
    (by simpa using h14) (by simpa using h24) (by simpa using h34)
  rw [← hM] at key
  simp only [chk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at key
  refine ⟨exp60_spec key.1, fun h4 h1 => ?_⟩
  have fin : ∀ c : Matrix (Fin 5) (Fin 5) (ZMod 2), mul5 c c.transpose = 1 ∧
      mul5 c.transpose c = 1 → quart (commM c M) ≠ 1 →
      ∃ c : Matrix (Fin 5) (Fin 5) (ZMod 2), c * c.transpose = 1 ∧ c.transpose * c = 1 ∧
        (c * M * c.transpose * M.transpose) ^ 4 ≠ 1 := by
    intro c ⟨hc1, hc2⟩ hq
    refine ⟨c, by rwa [mul5_eq] at hc1, by rwa [mul5_eq] at hc2, ?_⟩
    have e : commM c M = c * M * c.transpose * M.transpose := by
      simp only [commM, mul5_eq, mul_assoc]
    rw [← e, ← quart_eq]
    exact hq
  rcases key.2 with ((((hq | hq) | hq) | hq) | hq)
  · exact absurd ((quart_eq M).trans h4) hq
  · exact absurd hq h1
  · exact fin pm1 pm1_orth hq
  · exact fin pm2 pm2_orth hq
  · exact fin pm3 pm3_orth hq

private theorem orth_of_dual {g : G52} (hg : dualG g = g) :
    (g : M5).transpose * (g : M5) = 1 ∧ (g : M5) * (g : M5).transpose = 1 := by
  have hT : (g : M5).transpose = ((g⁻¹ : G52) : M5) := by
    have := congrArg (fun x : G52 => ((x : G52) : M5).transpose) hg
    simpa [coe_dualG, Matrix.transpose_transpose] using this.symm
  refine ⟨?_, ?_⟩
  · rw [hT, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  · rw [hT, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem dual_fixed_pow_sixty {g : G52} (hg : dualG g = g) : g ^ 60 = 1 := by
  obtain ⟨h1, h2⟩ := orth_of_dual hg
  have := (orth_chk (g : M5) h1 h2).1
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, this, Units.val_one])

theorem dual_fixed_comm {A : G52} (hA : dualG A = A) (h4 : A ^ 4 = 1) (h1 : A ≠ 1) :
    ∃ c : G52, dualG c = c ∧ (c * A * c⁻¹ * A⁻¹) ^ 4 ≠ 1 := by
  obtain ⟨hT1, hT2⟩ := orth_of_dual hA
  have hTA : ((A⁻¹ : G52) : M5) = (A : M5).transpose := by
    have := congrArg (fun x : G52 => ((x : G52) : M5).transpose) hA
    simpa [coe_dualG, Matrix.transpose_transpose] using this
  have h4' : (A : M5) ^ 4 = 1 := by rw [← Units.val_pow_eq_pow_val, h4, Units.val_one]
  have h1' : (A : M5) ≠ 1 := fun h => h1 (Units.ext h)
  obtain ⟨c, hc1, hc2, hne⟩ := (orth_chk (A : M5) hT1 hT2).2 h4' h1'
  let C : G52 := ⟨c, c.transpose, hc1, hc2⟩
  refine ⟨C, Units.ext ?_, fun h => hne ?_⟩
  · rw [coe_dualG]
    exact Matrix.transpose_transpose c
  · have := congrArg (fun x : G52 => (x : M5)) h
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_one] at this
    rw [show ((C⁻¹ : G52) : M5) = c.transpose from rfl, hTA] at this
    exact this

end CFSG.RankThree.PartTwo.Sec21.FF79
