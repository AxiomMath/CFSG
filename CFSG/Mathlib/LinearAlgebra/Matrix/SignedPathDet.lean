module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical

public section

namespace CFSG.MatrixDet

private def det_signedPath_g {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (m : ℕ) : ℤ :=
  if hm : m + 1 < n then G ⟨m, Nat.lt_of_succ_lt hm⟩ ⟨m + 1, hm⟩ else 1

private def det_signedPath_d {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) : ℤ :=
  ∏ m ∈ Finset.range j.val, -det_signedPath_g G m

private theorem det_signedPath_g_sq {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ)
    (hnear : ∀ j k : Fin n, k.val = j.val + 1 → (G j k = 1 ∨ G j k = -1) ∧ G k j = G j k)
    (m : ℕ) : det_signedPath_g G m * det_signedPath_g G m = 1 := by
  by_cases hm : m + 1 < n
  · simp only [det_signedPath_g, dif_pos hm]
    rcases (hnear ⟨m, Nat.lt_of_succ_lt hm⟩ ⟨m + 1, hm⟩ rfl).1 with h | h <;> rw [h] <;> norm_num
  · simp only [det_signedPath_g, dif_neg hm]
    norm_num

private theorem det_signedPath_d_sq {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ)
    (hnear : ∀ j k : Fin n, k.val = j.val + 1 → (G j k = 1 ∨ G j k = -1) ∧ G k j = G j k)
    (j : Fin n) : det_signedPath_d G j * det_signedPath_d G j = 1 := by
  unfold det_signedPath_d
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun m _ => by
    have h := det_signedPath_g_sq G hnear m
    rw [neg_mul_neg]
    exact h

private theorem det_signedPath_d_succ {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (m : ℕ)
    (hm : m + 1 < n) : det_signedPath_d G ⟨m + 1, hm⟩ =
      -det_signedPath_g G m * det_signedPath_d G ⟨m, Nat.lt_of_succ_lt hm⟩ := by
  simp only [det_signedPath_d, Fin.val_mk, Finset.prod_range_succ]
  ring

private theorem det_signedPath_d_succ' {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) {j k : Fin n}
    (h : k.val = j.val + 1) : det_signedPath_d G k = -G j k * det_signedPath_d G j := by
  have hj : j.val + 1 < n := by omega
  have hk : k = ⟨j.val + 1, hj⟩ := Fin.ext h
  rw [hk, det_signedPath_d_succ G j.val hj]
  have hg : det_signedPath_g G j.val = G j ⟨j.val + 1, hj⟩ := by
    simp only [det_signedPath_g, dif_pos hj]
  rw [hg, show (⟨j.val, Nat.lt_of_succ_lt hj⟩ : Fin n) = j from Fin.ext rfl]

private theorem det_signedPath_conj {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hdiag : ∀ j, G j j = 2)
    (hfar : ∀ j k : Fin n, j.val + 2 ≤ k.val ∨ k.val + 2 ≤ j.val → G j k = 0)
    (hnear : ∀ j k : Fin n, k.val = j.val + 1 → (G j k = 1 ∨ G j k = -1) ∧ G k j = G j k) :
    G = Matrix.diagonal (det_signedPath_d G) * CartanMatrix.A n *
        Matrix.diagonal (det_signedPath_d G) := by
  ext j k
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, CartanMatrix.A, Matrix.of_apply]
  split_ifs with hjk hnearA
  · subst hjk
    rw [hdiag j]
    have hsq := det_signedPath_d_sq G hnear j
    calc (2 : ℤ) = 2 * (det_signedPath_d G j * det_signedPath_d G j) := by rw [hsq, mul_one]
      _ = det_signedPath_d G j * 2 * det_signedPath_d G j := by ring
  · rcases hnearA with h | h
    · have hdk := det_signedPath_d_succ' G h.symm
      have hsq := det_signedPath_d_sq G hnear j
      rw [hdk]
      calc G j k = G j k * (det_signedPath_d G j * det_signedPath_d G j) := by
            rw [hsq, mul_one]
        _ = det_signedPath_d G j * (-1) * (-G j k * det_signedPath_d G j) := by ring
    · have hsym := (hnear k j h.symm).2
      have hdk := det_signedPath_d_succ' G (j := k) (k := j) h.symm
      have hsq := det_signedPath_d_sq G hnear k
      rw [hsym, hdk]
      calc G k j = G k j * (det_signedPath_d G k * det_signedPath_d G k) := by
            rw [hsq, mul_one]
        _ = -G k j * det_signedPath_d G k * (-1) * det_signedPath_d G k := by ring
  · have hne : j.val ≠ k.val := fun hv => hjk (Fin.ext hv)
    rw [hfar j k (by omega)]
    ring

theorem det_signedPath {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hdiag : ∀ j, G j j = 2)
    (hfar : ∀ j k : Fin n, j.val + 2 ≤ k.val ∨ k.val + 2 ≤ j.val → G j k = 0)
    (hnear : ∀ j k : Fin n, k.val = j.val + 1 → (G j k = 1 ∨ G j k = -1) ∧ G k j = G j k) :
    G.det = n + 1 := by
  have hG := det_signedPath_conj G hdiag hfar hnear
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, CartanMatrix.A_det]
  have hsq : (∏ j, det_signedPath_d G j) * (∏ j, det_signedPath_d G j) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun j _ => det_signedPath_d_sq G hnear j
  calc (∏ j, det_signedPath_d G j) * (↑n + 1) * (∏ j, det_signedPath_d G j)
      = ((∏ j, det_signedPath_d G j) * (∏ j, det_signedPath_d G j)) * (↑n + 1) := by ring
    _ = ↑n + 1 := by rw [hsq, one_mul]

end CFSG.MatrixDet
