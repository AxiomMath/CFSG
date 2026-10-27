module

public import CFSG.Monster.B.Intertwiner.ArithSpec
public import Certificates.Data.CFSGNative.MonsterB.IntertwinerCheck
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CFSG.Monster.B

open Bin Matrix

theorem rankCert_P_size (n : ℕ) (M : Mat) : (rankCert n M).2.1.size = n := by
  unfold rankCert
  simp only
  rw [gjGo_size, idMat_size]

theorem foldl_set_size (n : ℕ) (f : ℕ → ℕ) (g : ℕ → Row) :
    ∀ (l : List ℕ) (Q : Mat), (l.foldl (fun Q i => Q.set! (f i) (g i)) Q).size = Q.size
  | [], Q => rfl
  | i :: l, Q => by rw [List.foldl_cons, foldl_set_size n f g l]; simp

theorem rankCert_Q_size (n : ℕ) (M : Mat) : (rankCert n M).2.2.size = n := by
  unfold rankCert
  simp only
  rw [foldl_set_size n _ _ _ _]
  simp

theorem card_lt (n r : ℕ) (hr : r ≤ n) :
    Fintype.card {i : Fin n // (if (i : ℕ) < r then (1 : ZMod 2) else 0) ≠ 0} = r := by
  have : ∀ i : Fin n, ((if (i : ℕ) < r then (1 : ZMod 2) else 0) ≠ 0) ↔ (i : ℕ) < r := by
    intro i; split_ifs with h <;> simp [h]
  simp only [this]
  rw [Fintype.card_subtype, Fin.card_filter_val_lt, min_eq_right hr]

theorem rank_of_rankOK {n : ℕ} {M : Mat} (hM : M.size ≤ n) {r : ℕ} (hr : r ≤ n)
    (h : rankOK n M r = true) : (cmat n M).rank = r := by
  unfold rankOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, hPMQ⟩, hP⟩, hQ⟩ := h
  have hPs := rankCert_P_size n M
  have hQs := rankCert_Q_size n M
  have e1 := cmat_eq_of_beq (n := n) hPMQ
  rw [cmat_mulP _ _ _ hQs.le, cmat_mulP _ _ _ hM, cmat_diagM] at e1
  have e2 := cmat_eq_of_beq (n := n) hP
  rw [cmat_mulP _ _ _ (invM_size n _).le, cmat_idMat] at e2
  have e3 := cmat_eq_of_beq (n := n) hQ
  rw [cmat_mulP _ _ _ (invM_size n _).le, cmat_idMat] at e3
  have uP : IsUnit (cmat n (rankCert n M).2.1).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 ⟨⟨_, _, e2, mul_eq_one_comm.1 e2⟩, rfl⟩
  have uQ : IsUnit (cmat n (rankCert n M).2.2).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 ⟨⟨_, _, e3, mul_eq_one_comm.1 e3⟩, rfl⟩
  have := congrArg Matrix.rank e1
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ uQ, Matrix.rank_mul_eq_right_of_isUnit_det _ _ uP,
    Matrix.rank_diagonal, card_lt n r hr] at this
  exact this

end CFSG.Monster.B

end
