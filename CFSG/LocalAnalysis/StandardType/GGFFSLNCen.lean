module

public import CFSG.LocalAnalysis.StandardType.GGFFModelNDefs
public import CFSG.LocalAnalysis.StandardType.GGFFSLNDefs

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.GGFF

open scoped MatrixGroups
open CFSG.RankThree.PartTwo.Sec4.RonanK429F
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

private abbrev M6 := Matrix (Fin 6) (Fin 6) (ZMod 2)

private def blkIdx6 : Fin 3 → Fin 2 → Fin 6 := ![![0, 1], ![2, 3], ![4, 5]]

private def blkOf6 : Fin 6 → Fin 3 := ![0, 0, 1, 1, 2, 2]

private def compl6 : Fin 3 → Fin 6 → ZMod 2 :=
  ![![0, 0, 1, 1, 1, 1], ![1, 1, 0, 0, 1, 1], ![1, 1, 1, 1, 0, 0]]

private def tv6 : Fin 3 → M6 := ![W6.t1M, W6.t2M, W6.t3M]

private def candVec6 (i : Fin 3) (a : Fin 4) : Fin 6 → ZMod 2 :=
  fun m => if m = blkIdx6 i 0 then ((a.val % 2 : ℕ) : ZMod 2)
    else if m = blkIdx6 i 1 then ((a.val / 2 : ℕ) : ZMod 2) else 0

private def candM6 (a b c : Fin 4) : M6 :=
  Matrix.of fun m j =>
    if j = blkIdx6 0 0 then candVec6 0 a m
    else if j = blkIdx6 0 1 then (tv6 0).mulVec (candVec6 0 a) m
    else if j = blkIdx6 1 0 then candVec6 1 b m
    else if j = blkIdx6 1 1 then (tv6 1).mulVec (candVec6 1 b) m
    else if j = blkIdx6 2 0 then candVec6 2 c m
    else (tv6 2).mulVec (candVec6 2 c) m

private abbrev mvec6 (v : Fin 3 → ZMod 3) : M6 := ((vecElt W6.T v : SL(6, ZMod 2)) : M6)

private theorem proj6 (i : Fin 3) :
    ((1 : M6) + tv6 i + tv6 i ^ 2) = Matrix.diagonal (compl6 i) := by
  fin_cases i <;> decide +kernel

private theorem compl6_eq (i : Fin 3) (m : Fin 6) :
    compl6 i m = if blkOf6 m = i then 0 else 1 := by
  fin_cases i <;> fin_cases m <;> rfl

private theorem blkOf6_blkIdx6 (i : Fin 3) (a : Fin 2) : blkOf6 (blkIdx6 i a) = i := by
  fin_cases i <;> fin_cases a <;> rfl

private theorem tv6_mulVec (i : Fin 3) :
    (tv6 i).mulVec (Pi.single (blkIdx6 i 0) 1) = (Pi.single (blkIdx6 i 1) 1 : Fin 6 → ZMod 2) := by
  fin_cases i <;> decide +kernel

private theorem cand_exists6 : ∀ (i : Fin 3) (u : Fin 6 → ZMod 2),
    (∀ m, blkOf6 m ≠ i → u m = 0) → ∃ a : Fin 4, u = candVec6 i a := by
  decide +kernel

private theorem cand_check6 : ∀ a b c : Fin 4,
    candVec6 0 a ≠ 0 → candVec6 1 b ≠ 0 → candVec6 2 c ≠ 0 →
      ∃ v : Fin 3 → ZMod 3, candM6 a b c = mvec6 v := by
  decide +kernel

theorem cen_SL6 : ∀ k : SL(6, ZMod 2), (∀ i, k * W6.T i = W6.T i * k) → ∃ v, k = vecElt W6.T v := by
  intro k hk
  set K : M6 := (k : M6) with hK
  have hmat : ∀ i : Fin 3, K * tv6 i = tv6 i * K := by
    intro i
    have h := congrArg (fun z : SL(6, ZMod 2) => (z : M6)) (hk i)
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h
    rw [W6.coe_T i] at h
    simpa [hK, tv6] using h
  have hdiag : ∀ i : Fin 3, Matrix.diagonal (compl6 i) * K = K * Matrix.diagonal (compl6 i) := by
    intro i
    have h2 : K * tv6 i ^ 2 = tv6 i ^ 2 * K := by
      rw [pow_two]
      calc K * (tv6 i * tv6 i) = K * tv6 i * tv6 i := (Matrix.mul_assoc K (tv6 i) (tv6 i)).symm
        _ = tv6 i * K * tv6 i := by rw [hmat i]
        _ = tv6 i * (K * tv6 i) := Matrix.mul_assoc (tv6 i) K (tv6 i)
        _ = tv6 i * (tv6 i * K) := by rw [hmat i]
        _ = tv6 i * tv6 i * K := (Matrix.mul_assoc (tv6 i) (tv6 i) K).symm
    have h : ((1 : M6) + tv6 i + tv6 i ^ 2) * K = K * ((1 : M6) + tv6 i + tv6 i ^ 2) := by
      calc ((1 : M6) + tv6 i + tv6 i ^ 2) * K
          = K + tv6 i * K + tv6 i ^ 2 * K := by
            rw [Matrix.add_mul, Matrix.add_mul, Matrix.one_mul]
        _ = K + K * tv6 i + K * tv6 i ^ 2 := by rw [← hmat i, ← h2]
        _ = K * ((1 : M6) + tv6 i + tv6 i ^ 2) := by
            rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_one]
    rwa [proj6 i] at h
  have hcross : ∀ (i : Fin 3) (m j : Fin 6), blkOf6 j = i → blkOf6 m ≠ i → K m j = 0 := by
    intro i m j hj hm
    have h := congrFun (congrFun (hdiag i) m) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, compl6_eq, compl6_eq, if_pos hj, if_neg hm] at h
    simpa using h
  have hcol : ∀ i : Fin 3, K.col (blkIdx6 i 1) = (tv6 i).mulVec (K.col (blkIdx6 i 0)) := by
    intro i
    have h := congrArg (fun M : M6 => M.mulVec (Pi.single (blkIdx6 i 0) 1)) (hmat i)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h
    rw [tv6_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    exact h
  have hex : ∀ i : Fin 3, ∃ a : Fin 4, K.col (blkIdx6 i 0) = candVec6 i a := fun i =>
    cand_exists6 i _ (fun m hm => hcross i m (blkIdx6 i 0) (blkOf6_blkIdx6 i 0) hm)
  choose ai hai using hex
  have hne : ∀ i : Fin 3, candVec6 i (ai i) ≠ 0 := by
    intro i hzero
    have hcolzero : ∀ m, K m (blkIdx6 i 0) = 0 := by
      intro m
      have h := congrFun (hai i) m
      rw [hzero] at h
      exact h
    have hdet0 : K.det = 0 :=
      Matrix.det_eq_zero_of_column_eq_zero (blkIdx6 i 0) hcolzero
    have hdet1 : K.det = 1 := Matrix.SpecialLinearGroup.det_coe k
    exact one_ne_zero (hdet1 ▸ hdet0)
  have hcol1 : ∀ i : Fin 3, K.col (blkIdx6 i 1) = (tv6 i).mulVec (candVec6 i (ai i)) := by
    intro i
    rw [hcol i, hai i]
  have hKm : K = candM6 (ai 0) (ai 1) (ai 2) := by
    ext m j
    fin_cases j
    · simpa [candM6, blkIdx6, Matrix.of_apply] using congrFun (hai 0) m
    · simpa [candM6, blkIdx6, Matrix.of_apply] using congrFun (hcol1 0) m
    · simpa [candM6, blkIdx6, Matrix.of_apply] using congrFun (hai 1) m
    · simpa [candM6, blkIdx6, Matrix.of_apply] using congrFun (hcol1 1) m
    · simpa [candM6, blkIdx6, Matrix.of_apply] using congrFun (hai 2) m
    · simpa [candM6, blkIdx6, Matrix.of_apply] using congrFun (hcol1 2) m
  obtain ⟨v, hv⟩ := cand_check6 (ai 0) (ai 1) (ai 2) (hne 0) (hne 1) (hne 2)
  exact ⟨v, Subtype.ext (by rw [← hK, hKm, hv])⟩

private theorem T1_inv6 : (W6.T 1)⁻¹ = W6.T 1 ^ 2 :=
  inv_eq_of_mul_eq_one_left (by rw [← pow_succ]; exact W6.pow_T 1)

private theorem pow_mul_pow_mem_rOne {H : Type} [Group H] (z : Fin 3 → H) (pi : H) (a b c : ℕ) :
    (z 0 * (z 1)⁻¹) ^ a * zetaOf z ^ b * pi ^ c ∈ rOne z pi := by
  have h1 : z 0 * (z 1)⁻¹ ∈ rOne z pi := Subgroup.subset_closure (by simp)
  have h2 : zetaOf z ∈ rOne z pi := Subgroup.subset_closure (by simp)
  have h3 : pi ∈ rOne z pi := Subgroup.subset_closure (by simp)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ h1 a) (Subgroup.pow_mem _ h2 b))
    (Subgroup.pow_mem _ h3 c)

private def q0M : M6 :=
  !![1, 0, 0, 1, 0, 1;
     0, 1, 1, 1, 1, 1;
     1, 1, 0, 1, 1, 1;
     1, 0, 1, 1, 1, 0;
     1, 1, 1, 1, 0, 1;
     1, 0, 1, 0, 1, 1]

private def q0Mi : M6 :=
  !![1, 0, 0, 1, 0, 1;
     0, 1, 1, 1, 1, 1;
     1, 1, 1, 1, 0, 1;
     1, 0, 1, 0, 1, 1;
     1, 1, 0, 1, 1, 1;
     1, 0, 1, 1, 1, 0]

private theorem q0M_mul : q0M * q0Mi = 1 := by decide +kernel

private def q0 : SL(6, ZMod 2) := W6.mkSL6 q0M q0Mi q0M_mul

private def q0i : SL(6, ZMod 2) := W6.mkSL6 q0Mi q0M (by decide +kernel)

private theorem q0_check :
    q0 * q0 = N6.x0 * vecElt W6.T 0 ∧
    q0 * (W6.T 0 * W6.T 1 ^ 2) * q0i =
      (W6.T 0 * W6.T 1 ^ 2) ^ 2 * zetaOf W6.T ^ 0 * W6.tw ^ 2 ∧
    q0 * zetaOf W6.T * q0i = (W6.T 0 * W6.T 1 ^ 2) ^ 0 * zetaOf W6.T ^ 1 * W6.tw ^ 0 ∧
    q0 * W6.tw * q0i = (W6.T 0 * W6.T 1 ^ 2) ^ 2 * zetaOf W6.T ^ 0 * W6.tw ^ 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

private theorem q0_inv : q0⁻¹ = q0i :=
  inv_eq_of_mul_eq_one_right (by decide +kernel)

private def q1M : M6 :=
  !![1, 0, 0, 1, 1, 0;
     0, 1, 1, 1, 0, 1;
     1, 1, 0, 1, 0, 1;
     1, 0, 1, 1, 1, 1;
     1, 0, 1, 0, 0, 1;
     0, 1, 0, 1, 1, 1]

private def q1Mi : M6 :=
  !![1, 0, 0, 1, 1, 0;
     0, 1, 1, 1, 0, 1;
     1, 1, 1, 1, 1, 0;
     1, 0, 1, 0, 0, 1;
     1, 0, 1, 1, 1, 1;
     0, 1, 1, 0, 1, 0]

private theorem q1M_mul : q1M * q1Mi = 1 := by decide +kernel

private def q1 : SL(6, ZMod 2) := W6.mkSL6 q1M q1Mi q1M_mul

private def q1i : SL(6, ZMod 2) := W6.mkSL6 q1Mi q1M (by decide +kernel)

private theorem q1_check :
    q1 * q1 = N6.x0 * vecElt W6.T ![0, 1, 2] ∧
    q1 * (W6.T 0 * W6.T 1 ^ 2) * q1i =
      (W6.T 0 * W6.T 1 ^ 2) ^ 1 * zetaOf W6.T ^ 1 * W6.tw ^ 2 ∧
    q1 * zetaOf W6.T * q1i = (W6.T 0 * W6.T 1 ^ 2) ^ 0 * zetaOf W6.T ^ 1 * W6.tw ^ 0 ∧
    q1 * W6.tw * q1i = (W6.T 0 * W6.T 1 ^ 2) ^ 2 * zetaOf W6.T ^ 0 * W6.tw ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

private theorem q1_inv : q1⁻¹ = q1i :=
  inv_eq_of_mul_eq_one_right (by decide +kernel)

private def q2M : M6 :=
  !![1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 0;
     1, 1, 0, 1, 1, 0;
     1, 0, 1, 1, 0, 1;
     0, 1, 0, 1, 0, 1;
     1, 1, 1, 1, 1, 1]

private def q2Mi : M6 :=
  !![1, 0, 0, 1, 1, 1;
     0, 1, 1, 1, 1, 0;
     1, 1, 1, 1, 1, 1;
     1, 0, 1, 0, 1, 0;
     0, 1, 1, 0, 1, 1;
     1, 1, 0, 1, 1, 0]

private theorem q2M_mul : q2M * q2Mi = 1 := by decide +kernel

private def q2 : SL(6, ZMod 2) := W6.mkSL6 q2M q2Mi q2M_mul

private def q2i : SL(6, ZMod 2) := W6.mkSL6 q2Mi q2M (by decide +kernel)

private theorem q2_check :
    q2 * q2 = N6.x0 * vecElt W6.T ![0, 2, 1] ∧
    q2 * (W6.T 0 * W6.T 1 ^ 2) * q2i =
      (W6.T 0 * W6.T 1 ^ 2) ^ 0 * zetaOf W6.T ^ 2 * W6.tw ^ 2 ∧
    q2 * zetaOf W6.T * q2i = (W6.T 0 * W6.T 1 ^ 2) ^ 0 * zetaOf W6.T ^ 1 * W6.tw ^ 0 ∧
    q2 * W6.tw * q2i = (W6.T 0 * W6.T 1 ^ 2) ^ 1 * zetaOf W6.T ^ 0 * W6.tw ^ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

private theorem q2_inv : q2⁻¹ = q2i :=
  inv_eq_of_mul_eq_one_right (by decide +kernel)

private theorem invol6 : ∀ v : Fin 3 → ZMod 3,
    N6.x0 * vecElt W6.T v * (N6.x0 * vecElt W6.T v) = 1 →
      v = 0 ∨ v = ![0, 1, 2] ∨ v = ![0, 2, 1] := by
  decide +kernel

theorem sqrt_SL6 : ∀ v : Fin 3 → ZMod 3,
    N6.x0 * vecElt W6.T v * (N6.x0 * vecElt W6.T v) = 1 →
    (∃ w, N6.x0 * vecElt W6.T v * W6.tw * (N6.x0 * vecElt W6.T v)⁻¹ * W6.tw = vecElt W6.T w) →
    (∃ w : Fin 3 → ZMod 3, w 0 + w 1 + w 2 = 0 ∧
      N6.x0 * vecElt W6.T v * W6.tw * (N6.x0 * vecElt W6.T v)⁻¹ * W6.tw = vecElt W6.T w) ∧
    ∃ q : SL(6, ZMod 2), q * q = N6.x0 * vecElt W6.T v ∧
      ∀ y ∈ ({W6.T 0 * (W6.T 1)⁻¹, zetaOf W6.T, W6.tw} : Set SL(6, ZMod 2)),
        q * y * q⁻¹ ∈ rOne W6.T W6.tw := by
  intro v hx hinv
  have hxinv : (N6.x0 * vecElt W6.T v)⁻¹ = N6.x0 * vecElt W6.T v :=
    inv_eq_of_mul_eq_one_right hx
  rw [hxinv]
  rcases invol6 v hx with rfl | rfl | rfl
  · refine ⟨⟨0, by decide, by decide +kernel⟩, q0, q0_check.1, ?_⟩
    intro y hy
    rw [q0_inv]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · rw [T1_inv6, q0_check.2.1, ← T1_inv6]
      exact pow_mul_pow_mem_rOne W6.T W6.tw 2 0 2
    · rw [q0_check.2.2.1, ← T1_inv6]
      exact pow_mul_pow_mem_rOne W6.T W6.tw 0 1 0
    · rw [q0_check.2.2.2, ← T1_inv6]
      exact pow_mul_pow_mem_rOne W6.T W6.tw 2 0 1
  · refine ⟨⟨![1, 1, 1], by decide, by decide +kernel⟩, q1, q1_check.1, ?_⟩
    intro y hy
    rw [q1_inv]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · rw [T1_inv6, q1_check.2.1, ← T1_inv6]
      exact pow_mul_pow_mem_rOne W6.T W6.tw 1 1 2
    · rw [q1_check.2.2.1, ← T1_inv6]
      exact pow_mul_pow_mem_rOne W6.T W6.tw 0 1 0
    · rw [q1_check.2.2.2, ← T1_inv6]
      exact pow_mul_pow_mem_rOne W6.T W6.tw 2 0 2
  · refine ⟨⟨![2, 2, 2], by decide, by decide +kernel⟩, q2, q2_check.1, ?_⟩
    intro y hy
    rw [q2_inv]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · rw [T1_inv6, q2_check.2.1, ← T1_inv6]
      exact pow_mul_pow_mem_rOne W6.T W6.tw 0 2 2
    · rw [q2_check.2.2.1, ← T1_inv6]
      exact pow_mul_pow_mem_rOne W6.T W6.tw 0 1 0
    · rw [q2_check.2.2.2, ← T1_inv6]
      exact pow_mul_pow_mem_rOne W6.T W6.tw 1 0 0

private abbrev M7 := Matrix (Fin 7) (Fin 7) (ZMod 2)

private def blkIdx7 : Fin 3 → Fin 2 → Fin 7 := ![![0, 1], ![2, 3], ![4, 5]]

private def blkOf7 : Fin 7 → Fin 4 := ![0, 0, 1, 1, 2, 2, 3]

private def compl7 : Fin 3 → Fin 7 → ZMod 2 :=
  ![![0, 0, 1, 1, 1, 1, 1], ![1, 1, 0, 0, 1, 1, 1], ![1, 1, 1, 1, 0, 0, 1]]

private def tv7 : Fin 3 → M7 := ![W7.t1M, W7.t2M, W7.t3M]

private def candVec7 (i : Fin 3) (a : Fin 4) : Fin 7 → ZMod 2 :=
  fun m => if m = blkIdx7 i 0 then ((a.val % 2 : ℕ) : ZMod 2)
    else if m = blkIdx7 i 1 then ((a.val / 2 : ℕ) : ZMod 2) else 0

private def candM7 (a b c : Fin 4) : M7 :=
  Matrix.of fun m j =>
    if j = blkIdx7 0 0 then candVec7 0 a m
    else if j = blkIdx7 0 1 then (tv7 0).mulVec (candVec7 0 a) m
    else if j = blkIdx7 1 0 then candVec7 1 b m
    else if j = blkIdx7 1 1 then (tv7 1).mulVec (candVec7 1 b) m
    else if j = blkIdx7 2 0 then candVec7 2 c m
    else if j = blkIdx7 2 1 then (tv7 2).mulVec (candVec7 2 c) m
    else (Pi.single 6 1 : Fin 7 → ZMod 2) m

private abbrev mvec7 (v : Fin 3 → ZMod 3) : M7 := ((vecElt W7.T v : SL(7, ZMod 2)) : M7)

private theorem eq_one_of_ne_zero : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by
  decide

private theorem proj7 (i : Fin 3) :
    ((1 : M7) + tv7 i + tv7 i ^ 2) = Matrix.diagonal (compl7 i) := by
  fin_cases i <;> decide +kernel

private theorem compl7_eq (i : Fin 3) (m : Fin 7) :
    compl7 i m = if blkOf7 m = Fin.castSucc i then 0 else 1 := by
  fin_cases i <;> fin_cases m <;> rfl

private theorem blkOf7_blkIdx7 (i : Fin 3) (a : Fin 2) : blkOf7 (blkIdx7 i a) = Fin.castSucc i := by
  fin_cases i <;> fin_cases a <;> rfl

private theorem blkOf7_six (i : Fin 3) : blkOf7 (6 : Fin 7) ≠ Fin.castSucc i := by
  fin_cases i <;> decide

private theorem tv7_mulVec (i : Fin 3) :
    (tv7 i).mulVec (Pi.single (blkIdx7 i 0) 1) = (Pi.single (blkIdx7 i 1) 1 : Fin 7 → ZMod 2) := by
  fin_cases i <;> decide +kernel

private theorem cand_exists7 : ∀ (i : Fin 3) (u : Fin 7 → ZMod 2),
    (∀ m, blkOf7 m ≠ Fin.castSucc i → u m = 0) → ∃ a : Fin 4, u = candVec7 i a := by
  decide +kernel

private theorem cand_check7 : ∀ a b c : Fin 4,
    candVec7 0 a ≠ 0 → candVec7 1 b ≠ 0 → candVec7 2 c ≠ 0 →
      ∃ v : Fin 3 → ZMod 3, candM7 a b c = mvec7 v := by
  decide +kernel

theorem cen_SL7 : ∀ k : SL(7, ZMod 2), (∀ i, k * W7.T i = W7.T i * k) → ∃ v, k = vecElt W7.T v := by
  intro k hk
  set K : M7 := (k : M7) with hK
  have hmat : ∀ i : Fin 3, K * tv7 i = tv7 i * K := by
    intro i
    have h := congrArg (fun z : SL(7, ZMod 2) => (z : M7)) (hk i)
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h
    rw [W7.coe_T i] at h
    simpa [hK, tv7] using h
  have hdiag : ∀ i : Fin 3, Matrix.diagonal (compl7 i) * K = K * Matrix.diagonal (compl7 i) := by
    intro i
    have h2 : K * tv7 i ^ 2 = tv7 i ^ 2 * K := by
      rw [pow_two]
      calc K * (tv7 i * tv7 i) = K * tv7 i * tv7 i := (Matrix.mul_assoc K (tv7 i) (tv7 i)).symm
        _ = tv7 i * K * tv7 i := by rw [hmat i]
        _ = tv7 i * (K * tv7 i) := Matrix.mul_assoc (tv7 i) K (tv7 i)
        _ = tv7 i * (tv7 i * K) := by rw [hmat i]
        _ = tv7 i * tv7 i * K := (Matrix.mul_assoc (tv7 i) (tv7 i) K).symm
    have h : ((1 : M7) + tv7 i + tv7 i ^ 2) * K = K * ((1 : M7) + tv7 i + tv7 i ^ 2) := by
      calc ((1 : M7) + tv7 i + tv7 i ^ 2) * K
          = K + tv7 i * K + tv7 i ^ 2 * K := by
            rw [Matrix.add_mul, Matrix.add_mul, Matrix.one_mul]
        _ = K + K * tv7 i + K * tv7 i ^ 2 := by rw [← hmat i, ← h2]
        _ = K * ((1 : M7) + tv7 i + tv7 i ^ 2) := by
            rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_one]
    rwa [proj7 i] at h
  have hcross : ∀ (i : Fin 3) (m j : Fin 7), blkOf7 j = Fin.castSucc i →
      blkOf7 m ≠ Fin.castSucc i → K m j = 0 := by
    intro i m j hj hm
    have h := congrFun (congrFun (hdiag i) m) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, compl7_eq, compl7_eq, if_pos hj, if_neg hm] at h
    simpa using h
  have hcol : ∀ i : Fin 3, K.col (blkIdx7 i 1) = (tv7 i).mulVec (K.col (blkIdx7 i 0)) := by
    intro i
    have h := congrArg (fun M : M7 => M.mulVec (Pi.single (blkIdx7 i 0) 1)) (hmat i)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h
    rw [tv7_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    exact h
  have hz : ∀ (i : Fin 3) (m : Fin 7), blkOf7 m = Fin.castSucc i → K m 6 = 0 := by
    intro i m hm
    have h := congrFun (congrFun (hdiag i) m) 6
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, compl7_eq, compl7_eq, if_pos hm,
      if_neg (blkOf7_six i)] at h
    simpa using h.symm
  have hmem : ∀ m : Fin 7, m ≠ 6 → ∃ i : Fin 3, blkOf7 m = Fin.castSucc i := by
    decide
  have h66 : K 6 6 = 1 := by
    refine eq_one_of_ne_zero _ ?_
    intro h0
    have hcolzero : ∀ m : Fin 7, K m 6 = 0 := by
      intro m
      by_cases hm : m = 6
      · rw [hm]; exact h0
      · obtain ⟨i, hi⟩ := hmem m hm
        exact hz i m hi
    have hdet0 : K.det = 0 := Matrix.det_eq_zero_of_column_eq_zero 6 hcolzero
    have hdet1 : K.det = 1 := Matrix.SpecialLinearGroup.det_coe k
    exact one_ne_zero (hdet1 ▸ hdet0)
  have hcol6 : K.col 6 = (Pi.single 6 1 : Fin 7 → ZMod 2) := by
    funext m
    by_cases hm : m = 6
    · subst hm
      simp [h66]
    · have h0 : K m 6 = 0 := by
        obtain ⟨i, hi⟩ := hmem m hm
        exact hz i m hi
      simp [h0, Pi.single_eq_of_ne, hm]
  have hex : ∀ i : Fin 3, ∃ a : Fin 4, K.col (blkIdx7 i 0) = candVec7 i a := fun i =>
    cand_exists7 i _ (fun m hm => hcross i m (blkIdx7 i 0) (blkOf7_blkIdx7 i 0) hm)
  choose ai hai using hex
  have hne : ∀ i : Fin 3, candVec7 i (ai i) ≠ 0 := by
    intro i hzero
    have hcolzero : ∀ m, K m (blkIdx7 i 0) = 0 := by
      intro m
      have h := congrFun (hai i) m
      rw [hzero] at h
      exact h
    have hdet0 : K.det = 0 :=
      Matrix.det_eq_zero_of_column_eq_zero (blkIdx7 i 0) hcolzero
    have hdet1 : K.det = 1 := Matrix.SpecialLinearGroup.det_coe k
    exact one_ne_zero (hdet1 ▸ hdet0)
  have hcol1 : ∀ i : Fin 3, K.col (blkIdx7 i 1) = (tv7 i).mulVec (candVec7 i (ai i)) := by
    intro i
    rw [hcol i, hai i]
  have hKm : K = candM7 (ai 0) (ai 1) (ai 2) := by
    ext m j
    fin_cases j
    · simpa [candM7, blkIdx7, Matrix.of_apply] using congrFun (hai 0) m
    · simpa [candM7, blkIdx7, Matrix.of_apply] using congrFun (hcol1 0) m
    · simpa [candM7, blkIdx7, Matrix.of_apply] using congrFun (hai 1) m
    · simpa [candM7, blkIdx7, Matrix.of_apply] using congrFun (hcol1 1) m
    · simpa [candM7, blkIdx7, Matrix.of_apply] using congrFun (hai 2) m
    · simpa [candM7, blkIdx7, Matrix.of_apply] using congrFun (hcol1 2) m
    · simpa [candM7, blkIdx7, Matrix.of_apply] using congrFun hcol6 m
  obtain ⟨v, hv⟩ := cand_check7 (ai 0) (ai 1) (ai 2) (hne 0) (hne 1) (hne 2)
  exact ⟨v, Subtype.ext (by rw [← hK, hKm, hv])⟩

private def extM (A : M6) : M7 :=
  Matrix.of fun i j =>
    if h : i.val < 6 then (if h' : j.val < 6 then A ⟨i.val, h⟩ ⟨j.val, h'⟩ else 0)
    else (if j.val < 6 then 0 else 1)

private theorem T1_inv7 : (W7.T 1)⁻¹ = W7.T 1 ^ 2 :=
  inv_eq_of_mul_eq_one_left (by rw [← pow_succ]; exact W7.pow_T 1)

private theorem invol7 : ∀ v : Fin 3 → ZMod 3,
    N7.x0 * vecElt W7.T v * (N7.x0 * vecElt W7.T v) = 1 →
      v = 0 ∨ v = ![0, 1, 2] ∨ v = ![0, 2, 1] := by
  decide +kernel

private def q0' : SL(7, ZMod 2) := W7.mkSL7 (extM q0M) (extM q0Mi) (by decide +kernel)

private def q0i' : SL(7, ZMod 2) := W7.mkSL7 (extM q0Mi) (extM q0M) (by decide +kernel)

private theorem q0'_check :
    q0' * q0' = N7.x0 * vecElt W7.T 0 ∧
    q0' * (W7.T 0 * W7.T 1 ^ 2) * q0i' =
      (W7.T 0 * W7.T 1 ^ 2) ^ 2 * zetaOf W7.T ^ 0 * W7.tw ^ 2 ∧
    q0' * zetaOf W7.T * q0i' = (W7.T 0 * W7.T 1 ^ 2) ^ 0 * zetaOf W7.T ^ 1 * W7.tw ^ 0 ∧
    q0' * W7.tw * q0i' = (W7.T 0 * W7.T 1 ^ 2) ^ 2 * zetaOf W7.T ^ 0 * W7.tw ^ 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

private theorem q0'_inv : q0'⁻¹ = q0i' :=
  inv_eq_of_mul_eq_one_right (by decide +kernel)

private def q1' : SL(7, ZMod 2) := W7.mkSL7 (extM q1M) (extM q1Mi) (by decide +kernel)

private def q1i' : SL(7, ZMod 2) := W7.mkSL7 (extM q1Mi) (extM q1M) (by decide +kernel)

private theorem q1'_check :
    q1' * q1' = N7.x0 * vecElt W7.T ![0, 1, 2] ∧
    q1' * (W7.T 0 * W7.T 1 ^ 2) * q1i' =
      (W7.T 0 * W7.T 1 ^ 2) ^ 1 * zetaOf W7.T ^ 1 * W7.tw ^ 2 ∧
    q1' * zetaOf W7.T * q1i' = (W7.T 0 * W7.T 1 ^ 2) ^ 0 * zetaOf W7.T ^ 1 * W7.tw ^ 0 ∧
    q1' * W7.tw * q1i' = (W7.T 0 * W7.T 1 ^ 2) ^ 2 * zetaOf W7.T ^ 0 * W7.tw ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

private theorem q1'_inv : q1'⁻¹ = q1i' :=
  inv_eq_of_mul_eq_one_right (by decide +kernel)

private def q2' : SL(7, ZMod 2) := W7.mkSL7 (extM q2M) (extM q2Mi) (by decide +kernel)

private def q2i' : SL(7, ZMod 2) := W7.mkSL7 (extM q2Mi) (extM q2M) (by decide +kernel)

private theorem q2'_check :
    q2' * q2' = N7.x0 * vecElt W7.T ![0, 2, 1] ∧
    q2' * (W7.T 0 * W7.T 1 ^ 2) * q2i' =
      (W7.T 0 * W7.T 1 ^ 2) ^ 0 * zetaOf W7.T ^ 2 * W7.tw ^ 2 ∧
    q2' * zetaOf W7.T * q2i' = (W7.T 0 * W7.T 1 ^ 2) ^ 0 * zetaOf W7.T ^ 1 * W7.tw ^ 0 ∧
    q2' * W7.tw * q2i' = (W7.T 0 * W7.T 1 ^ 2) ^ 1 * zetaOf W7.T ^ 0 * W7.tw ^ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

private theorem q2'_inv : q2'⁻¹ = q2i' :=
  inv_eq_of_mul_eq_one_right (by decide +kernel)

theorem sqrt_SL7 : ∀ v : Fin 3 → ZMod 3,
    N7.x0 * vecElt W7.T v * (N7.x0 * vecElt W7.T v) = 1 →
    (∃ w, N7.x0 * vecElt W7.T v * W7.tw * (N7.x0 * vecElt W7.T v)⁻¹ * W7.tw = vecElt W7.T w) →
    (∃ w : Fin 3 → ZMod 3, w 0 + w 1 + w 2 = 0 ∧
      N7.x0 * vecElt W7.T v * W7.tw * (N7.x0 * vecElt W7.T v)⁻¹ * W7.tw = vecElt W7.T w) ∧
    ∃ q : SL(7, ZMod 2), q * q = N7.x0 * vecElt W7.T v ∧
      ∀ y ∈ ({W7.T 0 * (W7.T 1)⁻¹, zetaOf W7.T, W7.tw} : Set SL(7, ZMod 2)),
        q * y * q⁻¹ ∈ rOne W7.T W7.tw := by
  intro v hx hinv
  have hxinv : (N7.x0 * vecElt W7.T v)⁻¹ = N7.x0 * vecElt W7.T v :=
    inv_eq_of_mul_eq_one_right hx
  rw [hxinv]
  rcases invol7 v hx with rfl | rfl | rfl
  · refine ⟨⟨0, by decide, by decide +kernel⟩, q0', q0'_check.1, ?_⟩
    intro y hy
    rw [q0'_inv]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · rw [T1_inv7, q0'_check.2.1, ← T1_inv7]
      exact pow_mul_pow_mem_rOne W7.T W7.tw 2 0 2
    · rw [q0'_check.2.2.1, ← T1_inv7]
      exact pow_mul_pow_mem_rOne W7.T W7.tw 0 1 0
    · rw [q0'_check.2.2.2, ← T1_inv7]
      exact pow_mul_pow_mem_rOne W7.T W7.tw 2 0 1
  · refine ⟨⟨![1, 1, 1], by decide, by decide +kernel⟩, q1', q1'_check.1, ?_⟩
    intro y hy
    rw [q1'_inv]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · rw [T1_inv7, q1'_check.2.1, ← T1_inv7]
      exact pow_mul_pow_mem_rOne W7.T W7.tw 1 1 2
    · rw [q1'_check.2.2.1, ← T1_inv7]
      exact pow_mul_pow_mem_rOne W7.T W7.tw 0 1 0
    · rw [q1'_check.2.2.2, ← T1_inv7]
      exact pow_mul_pow_mem_rOne W7.T W7.tw 2 0 2
  · refine ⟨⟨![2, 2, 2], by decide, by decide +kernel⟩, q2', q2'_check.1, ?_⟩
    intro y hy
    rw [q2'_inv]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · rw [T1_inv7, q2'_check.2.1, ← T1_inv7]
      exact pow_mul_pow_mem_rOne W7.T W7.tw 0 2 2
    · rw [q2'_check.2.2.1, ← T1_inv7]
      exact pow_mul_pow_mem_rOne W7.T W7.tw 0 1 0
    · rw [q2'_check.2.2.2, ← T1_inv7]
      exact pow_mul_pow_mem_rOne W7.T W7.tw 1 0 0

end CFSG.StandardType.GGFF

end
