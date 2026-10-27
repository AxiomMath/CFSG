module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47CoordDefs
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Notation

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

namespace S16C1G47Two

private def alt4 (a b c d e f : ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, a, b, c; a, 0, d, e; b, d, 0, f; c, e, f, 0]

private theorem alt4_eq (S : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (hS : ∀ y : Fin 4 → ZMod 2, dotProduct (S.mulVec y) y = 0) :
    S = alt4 (S 0 1) (S 0 2) (S 0 3) (S 1 2) (S 1 3) (S 2 3) := by
  have hdiag : ∀ i, S i i = 0 := by
    intro i
    have h := hS (Pi.single i 1)
    simpa [Matrix.mulVec_single_one, dotProduct_single] using h
  have hsym : ∀ i j, S i j = S j i := by
    intro i j
    have h := hS (Pi.single i 1 + Pi.single j 1)
    simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, Matrix.mulVec_single_one,
      dotProduct_single, single_dotProduct] at h
    simp [hdiag] at h
    have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    exact key _ _ h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [alt4, hdiag]
  all_goals exact hsym _ _

private abbrev Mat48 := Matrix (Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)

private def stM (S T : Matrix (Fin 4) (Fin 4) (ZMod 2)) (p : Mat48 × Mat48) : Mat48 × Mat48 :=
  (p.1 + S * (T * p.1 + p.2), T * p.1 + p.2)

private def X0 : Mat48 := Matrix.fromCols 1 0

private def Y0 : Mat48 := Matrix.fromCols 0 1

private theorem rho_mul_fromRows (S T : Matrix (Fin 4) (Fin 4) (ZMod 2)) (X Y : Mat48) :
    (g47Up S * g47Lo T) * Matrix.fromRows X Y =
      Matrix.fromRows (stM S T (X, Y)).1 (stM S T (X, Y)).2 := by
  rw [Matrix.mul_assoc]
  simp [g47Up, g47Lo, Matrix.fromBlocks_mul_fromRows, stM]

private theorem one_eq_fromRows :
    (1 : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) = Matrix.fromRows X0 Y0 := by
  simp [X0, Y0, Matrix.fromBlocks_one]

private theorem rho_pow (S T : Matrix (Fin 4) (Fin 4) (ZMod 2)) (k : ℕ) :
    (g47Up S * g47Lo T) ^ k = Matrix.fromRows ((stM S T)^[k] (X0, Y0)).1
      ((stM S T)^[k] (X0, Y0)).2 := by
  induction k with
  | zero => simpa using one_eq_fromRows
  | succ k ih =>
    rw [pow_succ', ih, rho_mul_fromRows, Function.iterate_succ_apply']

private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem b2z_xor (x y : Bool) : b2z (Bool.xor x y) = b2z x + b2z y := by
  cases x <;> cases y <;> decide

private theorem b2z_and (x y : Bool) : b2z (x && y) = b2z x * b2z y := by
  cases x <;> cases y <;> decide

private abbrev Rows := Nat × Nat × Nat × Nat

private def xorR (r r' : Rows) : Rows :=
  (Nat.xor r.1 r'.1, Nat.xor r.2.1 r'.2.1, Nat.xor r.2.2.1 r'.2.2.1, Nat.xor r.2.2.2 r'.2.2.2)

private def tApp (a b c d e f : Bool) (r : Rows) : Rows :=
  (Nat.xor (Nat.xor (cond a r.2.1 0) (cond b r.2.2.1 0)) (cond c r.2.2.2 0),
   Nat.xor (Nat.xor (cond a r.1 0) (cond d r.2.2.1 0)) (cond e r.2.2.2 0),
   Nat.xor (Nat.xor (cond b r.1 0) (cond d r.2.1 0)) (cond f r.2.2.2 0),
   Nat.xor (Nat.xor (cond c r.1 0) (cond e r.2.1 0)) (cond f r.2.2.1 0))

private def stepR (a b c d e f a' b' c' d' e' f' : Bool) (p : Rows × Rows) : Rows × Rows :=
  let y' := xorR (tApp a' b' c' d' e' f' p.1) p.2
  (xorR p.1 (tApp a b c d e f y'), y')

private def idP : Rows × Rows := ((1, 2, 4, 8), (16, 32, 64, 128))

private def dec (r : Rows) : Mat48 :=
  Matrix.of fun i j => b2z ((![r.1, r.2.1, r.2.2.1, r.2.2.2] i).testBit
    (Sum.elim (fun i : Fin 4 => (i : Nat)) (fun i : Fin 4 => 4 + (i : Nat)) j))

private def decP (p : Rows × Rows) : Mat48 × Mat48 := (dec p.1, dec p.2)

private theorem tb_xor (x y n : Nat) :
    (Nat.xor x y).testBit n = Bool.xor (x.testBit n) (y.testBit n) := Nat.testBit_xor x y n

private theorem tb_ite (a : Bool) (x n : Nat) :
    (if a = true then x else 0).testBit n = (a && x.testBit n) := by
  cases a <;> simp

private theorem dec_xorR (r r' : Rows) : dec (xorR r r') = dec r + dec r' := by
  ext i j
  fin_cases i <;> simp [dec, xorR, tb_xor, b2z_xor]

private theorem dec_tApp (a b c d e f : Bool) (r : Rows) :
    dec (tApp a b c d e f r) = alt4 (b2z a) (b2z b) (b2z c) (b2z d) (b2z e) (b2z f) * dec r := by
  ext i j
  fin_cases i <;> simp [dec, tApp, alt4, Matrix.mul_apply, Fin.sum_univ_four, tb_xor,
    tb_ite, b2z_xor, b2z_and, add_assoc]

private theorem dec_stepR (a b c d e f a' b' c' d' e' f' : Bool) (p : Rows × Rows) :
    decP (stepR a b c d e f a' b' c' d' e' f' p) =
      stM (alt4 (b2z a) (b2z b) (b2z c) (b2z d) (b2z e) (b2z f))
        (alt4 (b2z a') (b2z b') (b2z c') (b2z d') (b2z e') (b2z f')) (decP p) := by
  simp [decP, stepR, stM, dec_xorR, dec_tApp]

private theorem dec_iter (a b c d e f a' b' c' d' e' f' : Bool) (p : Rows × Rows) (k : ℕ) :
    decP ((stepR a b c d e f a' b' c' d' e' f')^[k] p) =
      (stM (alt4 (b2z a) (b2z b) (b2z c) (b2z d) (b2z e) (b2z f))
        (alt4 (b2z a') (b2z b') (b2z c') (b2z d') (b2z e') (b2z f')))^[k] (decP p) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', dec_stepR, ih]

private theorem decP_idP : decP idP = (X0, Y0) := by
  decide +kernel

private def firstReturn (a b c d e f a' b' c' d' e' f' : Bool) : Bool :=
  let st := stepR a b c d e f a' b' c' d' e' f'
  let s1 := st idP
  let s2 := st s1
  let s3 := st s2
  let s4 := st s3
  let s5 := st s4
  let s6 := st s5
  decide (s1 = idP) || decide (s2 = idP) || decide (s3 = idP) || decide (s4 = idP) ||
    decide (s5 = idP) || decide (s6 = idP)

private theorem check_all : ∀ a b c d e f a' b' c' d' e' f' : Bool,
    firstReturn a b c d e f a' b' c' d' e' f' = true := by
  decide +kernel

private theorem exists_return (a b c d e f a' b' c' d' e' f' : Bool) :
    ∃ k, 1 ≤ k ∧ k ≤ 6 ∧ (stepR a b c d e f a' b' c' d' e' f')^[k] idP = idP := by
  have h := check_all a b c d e f a' b' c' d' e' f'
  simp only [firstReturn, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  · exact ⟨1, by omega, by omega, h⟩
  · exact ⟨2, by omega, by omega, h⟩
  · exact ⟨3, by omega, by omega, h⟩
  · exact ⟨4, by omega, by omega, h⟩
  · exact ⟨5, by omega, by omega, h⟩
  · exact ⟨6, by omega, by omega, h⟩

private theorem b2z_surj (x : ZMod 2) : ∃ b : Bool, b2z b = x := by
  fin_cases x
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

end S16C1G47Two

open S16C1G47Two in
theorem s16c1_G47_two (S T : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (hS : ∀ y : Fin 4 → ZMod 2, dotProduct (S.mulVec y) y = 0)
    (hT : ∀ x : Fin 4 → ZMod 2, dotProduct (T.mulVec x) x = 0) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ 6 ∧
      (g47Up S * g47Lo T) ^ k = 1 := by
  obtain ⟨a, ha⟩ := b2z_surj (S 0 1)
  obtain ⟨b, hb⟩ := b2z_surj (S 0 2)
  obtain ⟨c, hc⟩ := b2z_surj (S 0 3)
  obtain ⟨d, hd⟩ := b2z_surj (S 1 2)
  obtain ⟨e, he⟩ := b2z_surj (S 1 3)
  obtain ⟨f, hf⟩ := b2z_surj (S 2 3)
  obtain ⟨a', ha'⟩ := b2z_surj (T 0 1)
  obtain ⟨b', hb'⟩ := b2z_surj (T 0 2)
  obtain ⟨c', hc'⟩ := b2z_surj (T 0 3)
  obtain ⟨d', hd'⟩ := b2z_surj (T 1 2)
  obtain ⟨e', he'⟩ := b2z_surj (T 1 3)
  obtain ⟨f', hf'⟩ := b2z_surj (T 2 3)
  have hSe : S = alt4 (b2z a) (b2z b) (b2z c) (b2z d) (b2z e) (b2z f) := by
    rw [ha, hb, hc, hd, he, hf]
    exact alt4_eq S hS
  have hTe : T = alt4 (b2z a') (b2z b') (b2z c') (b2z d') (b2z e') (b2z f') := by
    rw [ha', hb', hc', hd', he', hf']
    exact alt4_eq T hT
  obtain ⟨k, hk1, hk6, hk⟩ := exists_return a b c d e f a' b' c' d' e' f'
  refine ⟨k, hk1, hk6, ?_⟩
  rw [hSe, hTe, rho_pow, ← decP_idP, ← dec_iter, hk, decP_idP]
  exact one_eq_fromRows.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
