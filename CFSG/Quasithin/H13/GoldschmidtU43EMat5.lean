module

public import CFSG.Quasithin.H13.GoldschmidtU43EMat3

public section

namespace CFSG.Quasithin.H13.U43

@[expose] def zd : Fin 4 → ZMod 3 := ![1, 1, -1, -1]

@[expose] def ud : Fin 4 → ZMod 3 := ![1, -1, 1, -1]

theorem Zmat_eq : Zmat = Matrix.diagonal zd := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Zmat, zd, Matrix.diagonal]

theorem Umat_eq : Umat = Matrix.diagonal ud := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Umat, ud, Matrix.diagonal]

theorem entry_zero {X : Mat3} (h1 : X * Zmat = Umat * X) (h2 : X * Umat = (Zmat * Umat) * X)
    (i j : Fin 4) (hP : ¬ (zd j = ud i ∧ ud j = zd i * ud i)) : X i j = 0 := by
  rw [Zmat_eq, Umat_eq] at h1 h2
  have e1 := congrFun (congrFun h1 i) j
  have e2 := congrFun (congrFun h2 i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at e1
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul] at e2
  by_contra hne
  apply hP
  refine ⟨?_, ?_⟩
  · have h : X i j * (zd j - ud i) = 0 := by
      rw [mul_sub, e1]
      ring
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hne
    · exact sub_eq_zero.mp h
  · have h : X i j * (ud j - zd i * ud i) = 0 := by
      rw [mul_sub, e2]
      ring
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hne
    · exact sub_eq_zero.mp h

theorem shape_A {X : Mat3} (h1 : X * Zmat = Umat * X) (h2 : X * Umat = (Zmat * Umat) * X) :
    X = !![X 0 0, 0, 0, 0; 0, 0, 0, X 1 3; 0, X 2 1, 0, 0; 0, 0, X 3 2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    exact entry_zero h1 h2 _ _ (by unfold zd ud; decide)

theorem card_fix_A_le (a d f g : ZMod 3) :
    Nat.card {v : Fin 4 → ZMod 3 //
      (!![a, 0, 0, 0; 0, 0, 0, d; 0, f, 0, 0; 0, 0, g, 0] : Mat3).mulVec v = v} ≤ 9 := by
  let X : Mat3 := !![a, 0, 0, 0; 0, 0, 0, d; 0, f, 0, 0; 0, 0, g, 0]
  have hinj : Function.Injective
      (fun w : {v : Fin 4 → ZMod 3 // X.mulVec v = v} => ((w.1 0, w.1 1) : ZMod 3 × ZMod 3)) := by
    intro w w' hww
    have h0 : w.1 0 = w'.1 0 := congrArg Prod.fst hww
    have h1 : w.1 1 = w'.1 1 := congrArg Prod.snd hww
    have e1 : f * w.1 1 = w.1 2 := by
      simpa [X, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using congrFun w.2 2
    have e1' : f * w'.1 1 = w'.1 2 := by
      simpa [X, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using congrFun w'.2 2
    have e2 : g * w.1 2 = w.1 3 := by
      simpa [X, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using congrFun w.2 3
    have e2' : g * w'.1 2 = w'.1 3 := by
      simpa [X, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using congrFun w'.2 3
    have h2 : w.1 2 = w'.1 2 := by rw [← e1, ← e1', h1]
    have h3 : w.1 3 = w'.1 3 := by rw [← e2, ← e2', h2]
    apply Subtype.ext
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  calc Nat.card {v : Fin 4 → ZMod 3 // X.mulVec v = v}
      ≤ Nat.card (ZMod 3 × ZMod 3) := Nat.card_le_card_of_injective _ hinj
    _ = 9 := by simp

@[expose] def Pmat : Mat3 := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 2, 2; 0, 0, 2, 1]

@[expose] def Pinv : Mat3 := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 1; 0, 0, 1, -1]

@[expose] def Wmat : Mat3 := Umat * Vmat

theorem Pmat_Pinv : Pmat * Pinv = 1 := by decide

theorem Pinv_Pmat : Pinv * Pmat = 1 := by decide

theorem Pinv_Zmat : Pinv * Zmat = Zmat * Pinv := by decide

theorem Pmat_Zmat : Pmat * Zmat = Zmat * Pmat := by decide

theorem Pinv_Umat : Pinv * Umat = Wmat * Pinv := by decide

theorem Pmat_Wmat : Pmat * Wmat = Umat * Pmat := by decide

theorem card_fix_conj_le {P Q X : Mat3} (hQP : Q * P = 1) :
    Nat.card {v : Fin 4 → ZMod 3 // X.mulVec v = v} ≤
      Nat.card {v : Fin 4 → ZMod 3 // (P * X * Q).mulVec v = v} := by
  have hmap : ∀ w : {v : Fin 4 → ZMod 3 // X.mulVec v = v},
      (P * X * Q).mulVec (P.mulVec w.1) = P.mulVec w.1 := by
    intro w
    calc (P * X * Q).mulVec (P.mulVec w.1) = (P * X * Q * P).mulVec w.1 :=
          Matrix.mulVec_mulVec _ _ _
      _ = (P * X).mulVec w.1 := by rw [Matrix.mul_assoc (P * X) Q P, hQP, Matrix.mul_one]
      _ = P.mulVec (X.mulVec w.1) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = P.mulVec w.1 := by rw [w.2]
  refine Nat.card_le_card_of_injective (fun w => ⟨P.mulVec w.1, hmap w⟩) ?_
  intro w w' h
  have h1 : P.mulVec w.1 = P.mulVec w'.1 := congrArg Subtype.val h
  apply Subtype.ext
  calc w.1 = (Q * P).mulVec w.1 := by rw [hQP, Matrix.one_mulVec]
    _ = Q.mulVec (P.mulVec w.1) := (Matrix.mulVec_mulVec _ _ _).symm
    _ = Q.mulVec (P.mulVec w'.1) := by rw [h1]
    _ = (Q * P).mulVec w'.1 := Matrix.mulVec_mulVec _ _ _
    _ = w'.1 := by rw [hQP, Matrix.one_mulVec]

theorem card_fix_of_A {X : Mat3} (h1 : X * Zmat = Umat * X) (h2 : X * Umat = (Zmat * Umat) * X) :
    Nat.card {v : Fin 4 → ZMod 3 // X.mulVec v = v} ≤ 9 := by
  have := card_fix_A_le (X 0 0) (X 1 3) (X 2 1) (X 3 2)
  rwa [← shape_A h1 h2] at this

theorem conj_shape {X : Mat3} (h1 : X * Zmat = Wmat * X) (h2 : X * Wmat = (Zmat * Wmat) * X) :
    (Pmat * X * Pinv) * Zmat = Umat * (Pmat * X * Pinv) ∧
    (Pmat * X * Pinv) * Umat = (Zmat * Umat) * (Pmat * X * Pinv) := by
  constructor
  · calc (Pmat * X * Pinv) * Zmat = Pmat * X * (Pinv * Zmat) := by
          rw [Matrix.mul_assoc (Pmat * X)]
      _ = Pmat * X * (Zmat * Pinv) := by rw [Pinv_Zmat]
      _ = Pmat * (X * Zmat) * Pinv := by simp only [Matrix.mul_assoc]
      _ = Pmat * (Wmat * X) * Pinv := by rw [h1]
      _ = (Pmat * Wmat) * X * Pinv := by simp only [Matrix.mul_assoc]
      _ = (Umat * Pmat) * X * Pinv := by rw [Pmat_Wmat]
      _ = Umat * (Pmat * X * Pinv) := by simp only [Matrix.mul_assoc]
  · calc (Pmat * X * Pinv) * Umat = Pmat * X * (Pinv * Umat) := by
          rw [Matrix.mul_assoc (Pmat * X)]
      _ = Pmat * X * (Wmat * Pinv) := by rw [Pinv_Umat]
      _ = Pmat * (X * Wmat) * Pinv := by simp only [Matrix.mul_assoc]
      _ = Pmat * ((Zmat * Wmat) * X) * Pinv := by rw [h2]
      _ = (Pmat * Zmat) * Wmat * X * Pinv := by simp only [Matrix.mul_assoc]
      _ = (Zmat * Pmat) * Wmat * X * Pinv := by rw [Pmat_Zmat]
      _ = Zmat * (Pmat * Wmat) * X * Pinv := by simp only [Matrix.mul_assoc]
      _ = Zmat * (Umat * Pmat) * X * Pinv := by rw [Pmat_Wmat]
      _ = (Zmat * Umat) * (Pmat * X * Pinv) := by simp only [Matrix.mul_assoc]

theorem card_fix_of_B {X : Mat3} (h1 : X * Zmat = Wmat * X) (h2 : X * Wmat = (Zmat * Wmat) * X) :
    Nat.card {v : Fin 4 → ZMod 3 // X.mulVec v = v} ≤ 9 :=
  (card_fix_conj_le Pinv_Pmat).trans (card_fix_of_A (conj_shape h1 h2).1 (conj_shape h1 h2).2)

end CFSG.Quasithin.H13.U43
