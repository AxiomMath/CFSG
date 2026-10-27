module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBOddLA

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

private theorem zmod2_add_self_nsbkl : ∀ x : ZMod 2, x + x = 0 := by decide

private theorem zmod2_ne_zero_nsbkl : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide

private theorem vec_add_self_nsbkl {n : ℕ} (v : Fin n → ZMod 2) : v + v = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  exact zmod2_add_self_nsbkl (v i)

private theorem char_two_shift_nsbkl {n : ℕ} (P Q Y E : Fin n → ZMod 2) (h : P + Q = Y + E) :
    P = Y + (Q + E) := by
  calc P = P + (Q + Q) := by rw [vec_add_self_nsbkl Q, add_zero]
    _ = (P + Q) + Q := by rw [add_assoc]
    _ = (Y + E) + Q := by rw [h]
    _ = Y + (Q + E) := by abel

private theorem fixes_of_last_zero_nsbkl {n m : ℕ} (hn : n = m + 1) {e : Fin n} (he : e.val = m)
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) (hM : FixesA m M) (v : Fin n → ZMod 2)
    (hv : v e = 0) : M.mulVec v = v := by
  have hsum : v = ∑ b, v b • (Pi.single b (1 : ZMod 2) : Fin n → ZMod 2) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hlin := map_sum (Matrix.mulVecLin M)
    (fun b => v b • (Pi.single b (1 : ZMod 2) : Fin n → ZMod 2)) Finset.univ
  calc M.mulVec v
      = M.mulVec (∑ b, v b • (Pi.single b (1 : ZMod 2) : Fin n → ZMod 2)) := by
        rw [← hsum]
    _ = ∑ b, v b • M.mulVec (Pi.single b (1 : ZMod 2)) := by
        simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_smul] using hlin
    _ = ∑ b, v b • (Pi.single b (1 : ZMod 2) : Fin n → ZMod 2) := by
        apply Finset.sum_congr rfl
        intro b _
        by_cases hb : b.val < m
        · rw [hM b hb]
        · have hbe : b = e := Fin.ext (by have := b.isLt; omega)
          simp [hbe, hv]
    _ = v := hsum.symm

private theorem last_diag_eq_one_nsbkl {n m : ℕ} (hn : n = m + 1) {e : Fin n} (he : e.val = m)
    (M : GL (Fin n) (ZMod 2)) (hM : FixesA m (M : Matrix (Fin n) (Fin n) (ZMod 2))) :
    (M : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (Pi.single e 1) e = 1 := by
  have hinv : ((M⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
      (M : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := Units.inv_mul M
  have hcancel : ∀ w : Fin n → ZMod 2,
      ((M⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
        ((M : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  apply zmod2_ne_zero_nsbkl
  intro hx
  have hfix := fixes_of_last_zero_nsbkl hn he (M : Matrix (Fin n) (Fin n) (ZMod 2)) hM
    ((M : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (Pi.single e 1)) hx
  have h2 : (M : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (Pi.single e 1) = Pi.single e 1 := by
    have h3 := congrArg
      (fun w => ((M⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec w) hfix
    simp only [hcancel] at h3
    exact h3
  rw [h2, Pi.single_eq_same] at hx
  exact one_ne_zero hx

private theorem fixes_shape_nsbkl {n m : ℕ} (hn : n = m + 1) {e : Fin n} (he : e.val = m)
    (M : GL (Fin n) (ZMod 2)) (hM : FixesA m (M : Matrix (Fin n) (Fin n) (ZMod 2))) :
    ∃ a : Fin n → ZMod 2, a e = 0 ∧
      ∀ y : Fin n → ZMod 2, (M : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec y = y + y e • a := by
  have hMe := last_diag_eq_one_nsbkl hn he M hM
  refine ⟨(M : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (Pi.single e 1) + Pi.single e 1, ?_, ?_⟩
  · rw [Pi.add_apply, hMe, Pi.single_eq_same]
    exact zmod2_add_self_nsbkl 1
  · intro y
    have hy' : (y + y e • (Pi.single e (1 : ZMod 2) : Fin n → ZMod 2)) e = 0 := by
      rw [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      exact zmod2_add_self_nsbkl (y e)
    have h1 := fixes_of_last_zero_nsbkl hn he (M : Matrix (Fin n) (Fin n) (ZMod 2)) hM
      (y + y e • (Pi.single e (1 : ZMod 2) : Fin n → ZMod 2)) hy'
    rw [Matrix.mulVec_add, Matrix.mulVec_smul] at h1
    rw [smul_add]
    exact char_two_shift_nsbkl _ _ _ _ h1

theorem fixes_std_succ_form {n m : ℕ} (hn : n = m + 1) (M : GL (Fin n) (ZMod 2))
    (hM : FixesA m (M : Matrix (Fin n) (Fin n) (ZMod 2))) :
    ∃ a : Fin n → ZMod 2, a ⟨m, by omega⟩ = 0 ∧
      ∀ y : Fin n → ZMod 2, (M : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec y =
        y + y ⟨m, by omega⟩ • a :=
  fixes_shape_nsbkl (e := ⟨m, by omega⟩) hn rfl M hM

end CFSG.Quasithin.H13.Ch4.NSB
