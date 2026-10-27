module

public import CFSG.LocalAnalysis.StandardType.FF81.CentAModelDefs

public section

namespace CFSG.StandardType.FF81.CentA

open Matrix RootFusionLin

private theorem caTr_zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

private theorem caTr_jGL_eq_one_add (m : ℕ) :
    (jGL 1 m : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
      1 + Matrix.single (Sum.inl 0) (Sum.inr (Sum.inr 0)) 1 := by
  ext r s
  rcases r with r | r | r <;> rcases s with s | s | s
  all_goals try fin_cases r
  all_goals try fin_cases s
  all_goals simp [jGL, coe_uGL, uMat, blk, Matrix.one_apply, Matrix.add_apply]

theorem eq_zero_or_eq_zero_of_isConj {m : ℕ} {a : Matrix (Fin 1) (Fin m) (ZMod 2)}
    {b : Matrix (Fin m) (Fin 1) (ZMod 2)} {c : Matrix (Fin 1) (Fin 1) (ZMod 2)}
    (h : IsConj (jGL 1 m) (uGL a b c)) : a = 0 ∨ b = 0 := by
  classical
  by_contra hab
  push Not at hab
  obtain ⟨ha, hb⟩ := hab
  obtain ⟨j, hj⟩ : ∃ j : Fin m, a 0 j ≠ 0 := by
    by_contra h'
    push Not at h'
    apply ha
    ext i k
    rw [Subsingleton.elim i 0]
    exact h' k
  obtain ⟨i, hi⟩ : ∃ i : Fin m, b i 0 ≠ 0 := by
    by_contra h'
    push Not at h'
    apply hb
    ext k l
    rw [Subsingleton.elim l 0]
    exact h' k
  have haj : a 0 j = 1 := by
    rcases caTr_zmod2_eq_zero_or_one (a 0 j) with h0 | h1
    · exact absurd h0 hj
    · exact h1
  have hbi : b i 0 = 1 := by
    rcases caTr_zmod2_eq_zero_or_one (b i 0) with h0 | h1
    · exact absurd h0 hi
    · exact h1
  obtain ⟨x, hx⟩ := isConj_iff.mp h
  let E : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2) :=
    Matrix.single (Sum.inl 0) (Sum.inr (Sum.inr 0)) 1
  let X : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2) :=
    (uGL a b c : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) - 1
  let xM : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2) := x
  let xI : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2) := x⁻¹
  have hxx : xM * xI = 1 := by simp [xM, xI]
  have hjGL : (jGL 1 m : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) = 1 + E := by
    simpa [E] using caTr_jGL_eq_one_add m
  have hux : (uGL a b c : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
      xM * (jGL 1 m : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) * xI := by
    have hx' := congrArg (fun g : GL (BlkIdx 1 m) (ZMod 2) =>
      (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2))) hx
    simpa [xM, xI] using hx'.symm
  have hX : X = xM * E * xI := by
    calc X = (uGL a b c : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) - 1 := rfl
      _ = xM * (jGL 1 m : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) * xI - 1 := by
            rw [hux]
      _ = xM * (jGL 1 m : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) * xI -
            xM * 1 * xI := by
            simp only [Matrix.mul_one, hxx]
      _ = xM * ((jGL 1 m : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) - 1) * xI := by
            simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hxx]
      _ = xM * E * xI := by
            rw [hjGL]
            have h1 : (1 : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) + E - 1 = E := by
              abel
            rw [h1]
  have hEME : ∀ N : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2),
      E * N * E = N (Sum.inr (Sum.inr 0)) (Sum.inl 0) • E := by
    intro N
    have hE : E = Matrix.single (Sum.inl 0) (Sum.inr (Sum.inr 0)) (1 : ZMod 2) := rfl
    rw [hE, Matrix.single_mul_mul_single, Matrix.smul_single]
    simp
  have hXMX : ∀ N : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2),
      X * N * X = ((xI * N * xM) (Sum.inr (Sum.inr 0)) (Sum.inl 0)) • X := by
    intro N
    rw [hX]
    calc xM * E * xI * N * (xM * E * xI)
        = xM * (E * (xI * N * xM) * E) * xI := by simp only [Matrix.mul_assoc]
      _ = xM * (((xI * N * xM) (Sum.inr (Sum.inr 0)) (Sum.inl 0)) • E) * xI := by
            rw [hEME]
      _ = ((xI * N * xM) (Sum.inr (Sum.inr 0)) (Sum.inl 0)) • (xM * E * xI) := by
            simp only [Matrix.mul_smul, Matrix.smul_mul]
  have hX_A (k : Fin m) : X (Sum.inl 0) (Sum.inr (Sum.inl k)) = a 0 k := by
    change uMat a b c (Sum.inl 0) (Sum.inr (Sum.inl k))
      - (1 : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2))
          (Sum.inl 0) (Sum.inr (Sum.inl k)) = a 0 k
    simp [uMat, blk, Matrix.one_apply]
  have hX_B (k : Fin m) : X (Sum.inr (Sum.inl k)) (Sum.inr (Sum.inr 0)) = b k 0 := by
    change uMat a b c (Sum.inr (Sum.inl k)) (Sum.inr (Sum.inr 0))
      - (1 : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2))
          (Sum.inr (Sum.inl k)) (Sum.inr (Sum.inr 0)) = b k 0
    simp [uMat, blk, Matrix.one_apply]
  have hX_BB (k l : Fin m) : X (Sum.inr (Sum.inl k)) (Sum.inr (Sum.inl l)) = 0 := by
    change uMat a b c (Sum.inr (Sum.inl k)) (Sum.inr (Sum.inl l))
      - (1 : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2))
          (Sum.inr (Sum.inl k)) (Sum.inr (Sum.inl l)) = 0
    simp [uMat, blk, Matrix.one_apply]
  let M : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2) :=
    Matrix.single (Sum.inr (Sum.inl j)) (Sum.inr (Sum.inl i)) (1 : ZMod 2)
  have hM : M = Matrix.single (Sum.inr (Sum.inl j)) (Sum.inr (Sum.inl i)) (1 : ZMod 2) :=
    rfl
  have hT (r s : BlkIdx 1 m) :
      (X * M * X) r s = X r (Sum.inr (Sum.inl j)) * X (Sum.inr (Sum.inl i)) s := by
    rw [hM, Matrix.mul_apply, Finset.sum_eq_single (Sum.inr (Sum.inl i))]
    · rw [Matrix.mul_single_apply_same, mul_one]
    · intro k _ hk
      rw [Matrix.mul_single_apply_of_ne (i := Sum.inr (Sum.inl j))
        (j := Sum.inr (Sum.inl i)) (a := r) (b := k) (c := 1) (M := X) hk, zero_mul]
    · intro hk
      exact absurd (Finset.mem_univ (Sum.inr (Sum.inl i))) hk
  have hT_AC : (X * M * X) (Sum.inl 0) (Sum.inr (Sum.inr 0)) = 1 := by
    rw [hT, hX_A j, hX_B i, haj, hbi, mul_one]
  have hT_A : (X * M * X) (Sum.inl 0) (Sum.inr (Sum.inl j)) = 0 := by
    rw [hT, hX_A j, hX_BB i j, mul_zero]
  rcases caTr_zmod2_eq_zero_or_one
      ((xI * M * xM) (Sum.inr (Sum.inr 0)) (Sum.inl 0)) with hs | hs
  · have hT0 : X * M * X = 0 := by
      simp only [hXMX, hs, zero_smul]
    rw [hT0] at hT_AC
    simp at hT_AC
  · have hTX : X * M * X = X := by
      simp only [hXMX, hs, one_smul]
    rw [hTX, hX_A j, haj] at hT_A
    exact (one_ne_zero : (1 : ZMod 2) ≠ 0) hT_A

private theorem caTr_zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

theorem isConj_of_mem_uOne {m : ℕ} {u : GL (BlkIdx 1 m) (ZMod 2)} (hu : u ∈ uOne m)
    (h1 : u ≠ 1) : IsConj (jGL 1 m) u := by
  obtain ⟨a, c, rfl⟩ := hu
  have hc : c = 0 ∨ c = 1 := by
    rcases caTr_zmod2_eq_zero_or_one (c 0 0) with h | h
    · left
      ext i j
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
      simpa using h
    · right
      ext i j
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
      simpa using h
  have hOne : IsConj (jGL 1 m) (uGL a 0 1) := by
    let E : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2) :=
      Matrix.single (Sum.inl 0) (Sum.inr (Sum.inr 0)) 1
    let N : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2) :=
      Matrix.of fun i j =>
        match i, j with
        | .inr (.inr _), .inr (.inl k) => a 0 k
        | _, _ => 0
    have hN0 : N + N = 0 := by
      ext i j
      rw [Matrix.add_apply, Matrix.zero_apply]
      exact caTr_zmod2_add_self _
    have hNN : N * N = 0 := by
      ext r s
      rw [Matrix.mul_apply, Matrix.zero_apply]
      rcases r with r | r | r
      · apply Finset.sum_eq_zero
        intro k _
        rw [show N (Sum.inl r) k = 0 from rfl, zero_mul]
      · apply Finset.sum_eq_zero
        intro k _
        rw [show N (Sum.inr (Sum.inl r)) k = 0 from rfl, zero_mul]
      · apply Finset.sum_eq_zero
        intro k _
        rcases k with k | k | k
        · rw [show N (Sum.inr (Sum.inr r)) (Sum.inl k) = 0 from rfl, zero_mul]
        · rw [show N (Sum.inr (Sum.inl k)) s = 0 from rfl, mul_zero]
        · rw [show N (Sum.inr (Sum.inr r)) (Sum.inr (Sum.inr k)) = 0 from rfl, zero_mul]
    have hNE : N * E = 0 := by
      ext r s
      rw [Matrix.mul_apply, Matrix.zero_apply]
      rcases r with r | r | r
      · apply Finset.sum_eq_zero
        intro k _
        rw [show N (Sum.inl r) k = 0 from rfl, zero_mul]
      · apply Finset.sum_eq_zero
        intro k _
        rw [show N (Sum.inr (Sum.inl r)) k = 0 from rfl, zero_mul]
      · apply Finset.sum_eq_zero
        intro k _
        rcases k with k | k | k
        · rw [show N (Sum.inr (Sum.inr r)) (Sum.inl k) = 0 from rfl, zero_mul]
        · rw [show E (Sum.inr (Sum.inl k)) s = 0 from by simp [E],
            mul_zero]
        · rw [show E (Sum.inr (Sum.inr k)) s = 0 from by simp [E],
            mul_zero]
    have hEN : E * N = Matrix.of fun r s =>
        if r = (Sum.inl 0 : BlkIdx 1 m) then N (Sum.inr (Sum.inr 0)) s else 0 := by
      ext r s
      by_cases hr : r = Sum.inl 0
      · rw [hr]
        rw [show E = Matrix.single (Sum.inl 0) (Sum.inr (Sum.inr 0)) (1 : ZMod 2) from rfl,
          Matrix.single_mul_apply_same]
        simp [Matrix.of_apply]
      · rw [show E = Matrix.single (Sum.inl 0) (Sum.inr (Sum.inr 0)) (1 : ZMod 2) from rfl,
          Matrix.single_mul_apply_of_ne (i := Sum.inl 0) (j := Sum.inr (Sum.inr 0))
            (a := r) (b := s) (c := 1) (M := N) hr]
        simp [Matrix.of_apply, hr]
    have hy : 1 + E + E * N = uMat a 0 1 := by
      rw [hEN]
      ext r s
      rcases r with r | r | r
      · fin_cases r
        rcases s with s | s | s
        · fin_cases s
          simp [uMat, blk, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, N, E]
        · simp [uMat, blk, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, N, E]
        · fin_cases s
          simp [uMat, blk, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, N, E]
      · rcases s with s | s | s
        · fin_cases s
          simp [uMat, blk, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, N, E]
        · simp [uMat, blk, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, N, E]
        · fin_cases s
          simp [uMat, blk, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, N, E]
      · fin_cases r
        rcases s with s | s | s
        · fin_cases s
          simp [uMat, blk, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, N, E]
        · simp [uMat, blk, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, N, E]
        · fin_cases s
          simp [uMat, blk, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, N, E]
    have hsq : (1 + N) * (1 + N) = 1 := by
      have hexp : (1 + N) * (1 + N) = 1 + (N + N) + N * N := by noncomm_ring
      rw [hexp, hN0, hNN]
      simp
    have hconj : (1 + N) * (1 + E) * (1 + N) = uMat a 0 1 := by
      have hexp : (1 + N) * (1 + E) * (1 + N) =
          1 + E + (N + N) + N * E + E * N + N * N + N * E * N := by noncomm_ring
      rw [hexp, hN0, hNE, hNN]
      simp only [zero_mul, add_zero]
      exact hy
    let y : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2) := 1 + N
    have hyy : y * y = 1 := hsq
    let x : GL (BlkIdx 1 m) (ZMod 2) := ⟨y, y, hyy, hyy⟩
    refine isConj_iff.mpr ⟨x, ?_⟩
    apply Units.ext
    simp only [Units.val_mul]
    show y * (jGL 1 m : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) * y = uMat a 0 1
    rw [show (jGL 1 m : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) = 1 + E from
      by simpa [E] using caTr_jGL_eq_one_add m]
    exact hconj
  rcases hc with hc0 | hc1
  · rw [hc0] at h1 ⊢
    have ha : a ≠ 0 := by
      intro h0
      exact h1 (by rw [h0, uGL_zero])
    obtain ⟨j, hj⟩ : ∃ j : Fin m, a 0 j ≠ 0 := by
      by_contra h'
      push Not at h'
      apply ha
      ext i k
      rw [Subsingleton.elim i 0]
      exact h' k
    have haj : a 0 j = 1 := by
      rcases caTr_zmod2_eq_zero_or_one (a 0 j) with h0 | h0
      · exact absurd h0 hj
      · exact h0
    let b₀ : Matrix (Fin m) (Fin 1) (ZMod 2) := Matrix.single j (0 : Fin 1) (1 : ZMod 2)
    have hb₀ : b₀ = Matrix.single j (0 : Fin 1) (1 : ZMod 2) := rfl
    have hab : a * b₀ = 1 := by
      rw [hb₀]
      ext i k
      rw [Subsingleton.elim i 0, Subsingleton.elim k 0]
      rw [Matrix.mul_single_apply_same, haj, one_mul]
      simp
    have h3 : a * -b₀ = 1 := by
      calc a * -b₀ = -(a * b₀) := Matrix.mul_neg a b₀
        _ = -(1) := by rw [hab]
        _ = 1 := by
            ext i k
            rw [Subsingleton.elim i 0, Subsingleton.elim k 0]
            exact ZMod.neg_eq_self_mod_two 1
    have hb0 : b₀ + b₀ = 0 := by
      ext i j
      exact caTr_zmod2_add_self (b₀ i j)
    have hvsq : uGL 0 b₀ 0 * uGL 0 b₀ 0 = 1 := by
      rw [uGL_mul]
      have e1 : (0 + 0 : Matrix (Fin 1) (Fin m) (ZMod 2)) = 0 := add_zero 0
      have e2 : (b₀ + b₀ : Matrix (Fin m) (Fin 1) (ZMod 2)) = 0 := hb0
      have e3 : ((0 : Matrix (Fin 1) (Fin 1) (ZMod 2)) +
          (0 : Matrix (Fin 1) (Fin 1) (ZMod 2)) +
          (0 : Matrix (Fin 1) (Fin m) (ZMod 2)) * b₀) = 0 := by
        rw [Matrix.zero_mul, add_zero, add_zero]
      rw [e1, e2, e3]
      exact uGL_zero
    have hvinv : (uGL 0 b₀ 0)⁻¹ = uGL 0 b₀ 0 := inv_eq_of_mul_eq_one_right hvsq
    have hv : uGL 0 b₀ 0 * uGL a 0 0 * (uGL 0 b₀ 0)⁻¹ = uGL a 0 1 := by
      rw [hvinv, mul_assoc]
      have hstep1 : uGL a 0 0 * uGL 0 b₀ 0 = uGL a b₀ 1 := by
        rw [uGL_mul]
        have e1 : (a + 0 : Matrix (Fin 1) (Fin m) (ZMod 2)) = a := add_zero a
        have e2 : (0 + b₀ : Matrix (Fin m) (Fin 1) (ZMod 2)) = b₀ := zero_add b₀
        have e3 : (0 + 0 + a * b₀ : Matrix (Fin 1) (Fin 1) (ZMod 2)) = 1 := by
          rw [zero_add, zero_add, hab]
        rw [e1, e2, e3]
      rw [hstep1]
      have hstep2 : uGL 0 b₀ 0 * uGL a b₀ 1 = uGL a 0 1 := by
        rw [uGL_mul]
        have e1 : (0 + a : Matrix (Fin 1) (Fin m) (ZMod 2)) = a := zero_add a
        have e2 : (b₀ + b₀ : Matrix (Fin m) (Fin 1) (ZMod 2)) = 0 := hb0
        have e3 : ((0 : Matrix (Fin 1) (Fin 1) (ZMod 2)) + 1 +
            (0 : Matrix (Fin 1) (Fin m) (ZMod 2)) * b₀) = 1 := by
          rw [Matrix.zero_mul, add_zero, zero_add]
        rw [e1, e2, e3]
      exact hstep2
    have hv' : IsConj (uGL a 0 0) (uGL a 0 1) := isConj_iff.mpr ⟨uGL 0 b₀ 0, hv⟩
    exact hOne.trans (isConj_comm.mpr hv')
  · rw [hc1]
    exact hOne

theorem isConj_of_mem_uTwo {m : ℕ} {u : GL (BlkIdx 1 m) (ZMod 2)} (hu : u ∈ uTwo m)
    (h1 : u ≠ 1) : IsConj (jGL 1 m) u := by
  have hu' : sigmaStd m u ∈ uOne m := by
    rw [← sigmaStd_map_uTwo]
    exact Subgroup.mem_map_of_mem (sigmaStd m).toMonoidHom hu
  have h1' : sigmaStd m u ≠ 1 := by
    intro h
    exact h1 ((sigmaStd m).injective (by simpa using h))
  obtain ⟨x, hx⟩ := isConj_iff.mp (isConj_of_mem_uOne hu' h1')
  refine isConj_iff.mpr ⟨sigmaStd m x, ?_⟩
  have h := congrArg (sigmaStd m) hx
  simpa only [map_mul, map_inv, sigmaStd_jGL, sigmaStd_sigmaStd] using h

end CFSG.StandardType.FF81.CentA

end
