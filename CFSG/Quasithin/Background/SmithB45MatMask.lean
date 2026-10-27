module

public import CFSG.Quasithin.Background.HMathieuBits
public import Mathlib.Algebra.Field.ZMod
public import CFSG.CharacterTheory.SteinbergBYNortonCriterion

public section

namespace CFSG.Quasithin.B45Mat

open CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.CharacterTheory.SteinbergBY Matrix
open scoped Kronecker

@[expose] def maskMat (m n : ℕ) (cs : List ℕ) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => bvec m (cs.getD j 0) i

theorem maskMat_apply (m n : ℕ) (cs : List ℕ) (i : Fin m) (j : Fin n) :
    maskMat m n cs i j = if (cs.getD j 0).testBit i then 1 else 0 :=
  rfl

@[expose] def mulM (A B : List ℕ) : List ℕ := B.map (actM A)

theorem actM_zero : ∀ A : List ℕ, actM A 0 = 0
  | [] => rfl
  | c :: cs => by
    rw [actM, actM_zero cs]
    simp

theorem getD_mulM (A B : List ℕ) (j : ℕ) : (mulM A B).getD j 0 = actM A (B.getD j 0) := by
  rw [mulM, List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases B[j]? with
  | none => exact (actM_zero A).symm
  | some b => rfl

theorem maskMat_mulM {m k n : ℕ} (A B : List ℕ) (hA : A.length ≤ k) :
    maskMat m n (mulM A B) = maskMat m k A * maskMat k n B := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [maskMat, Matrix.of_apply]
  rw [getD_mulM, bvec_actM, Finset.sum_apply]
  set x := B.getD j 0
  have hR : ∑ l : Fin k, bvec m (A.getD l 0) i * bvec k x l =
      ∑ l ∈ Finset.range k, bvec m (A.getD l 0) i * (if x.testBit l then 1 else 0) :=
    Fin.sum_univ_eq_sum_range (fun l => bvec m (A.getD l 0) i * (if x.testBit l then 1 else 0)) k
  rw [hR, ← Finset.sum_range_add_sum_Ico _ hA]
  have hIco : ∑ l ∈ Finset.Ico A.length k,
      bvec m (A.getD l 0) i * (if x.testBit l then (1 : ZMod 2) else 0) = 0 := by
    refine Finset.sum_eq_zero fun l hl => ?_
    rw [List.getD_eq_default _ _ (Finset.mem_Ico.1 hl).1, bvec_zero]
    simp
  rw [hIco, add_zero]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hx : x.testBit l
  · simp [hx]
  · simp [hx]

@[expose] def idM (n : ℕ) : List ℕ := (List.range n).map (2 ^ ·)

theorem maskMat_idM (n : ℕ) : maskMat n n (idM n) = 1 := by
  ext i j
  rw [maskMat_apply, Matrix.one_apply, idM, List.getD_eq_getElem _ _ (by simp),
    List.getElem_map, List.getElem_range, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h
    simp
  · have : (j : ℕ) ≠ i := fun h' => h (Fin.ext h'.symm)
    simp [h, this]

@[expose] def shifts (m n c : ℕ) : List ℕ := (List.range m).map fun i => c <<< (n * i)

theorem length_shifts (m n c : ℕ) : (shifts m n c).length = m := by
  simp [shifts]

theorem getD_shifts {m n c i : ℕ} (h : i < m) : (shifts m n c).getD i 0 = c <<< (n * i) := by
  rw [shifts, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, List.getElem_range]

@[expose] def kronM (m n : ℕ) (A C : List ℕ) : List ℕ :=
  (List.range (m * n)).map fun c => actM (shifts m n (C.getD (c % n) 0)) (A.getD (c / n) 0)

theorem testBit_shift_block {n c i' k' l : ℕ} (hc : c < 2 ^ n) (hk : k' < n) :
    (c <<< (n * l)).testBit (k' + n * i') = (decide (l = i') && c.testBit k') := by
  rw [Nat.testBit_shiftLeft]
  rcases lt_trichotomy l i' with h | h | h
  · have h1 : n * l ≤ k' + n * i' := by
      have := Nat.mul_le_mul_left n h.le
      omega
    have h2 : n ≤ k' + n * i' - n * l := by
      have : n * l + n ≤ n * i' := by
        have := Nat.mul_le_mul_left n (Nat.succ_le_of_lt h)
        rw [Nat.mul_succ] at this
        exact this
      omega
    have h3 : c.testBit (k' + n * i' - n * l) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) h2))
    simp [h1, h3, Nat.ne_of_lt h]
  · subst h
    simp
  · have h1 : ¬ n * l ≤ k' + n * i' := by
      have : n * i' + n ≤ n * l := by
        have := Nat.mul_le_mul_left n (Nat.succ_le_of_lt h)
        rw [Nat.mul_succ] at this
        exact this
      omega
    simp [h1, (Nat.ne_of_lt h).symm]

theorem maskMat_kronM {m n : ℕ} (A C : List ℕ) (hC : ∀ c ∈ C, c < 2 ^ n) :
    maskMat (m * n) (m * n) (kronM m n A C) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (maskMat m m A ⊗ₖ maskMat n n C) := by
  ext p q
  obtain ⟨⟨i', k'⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, Matrix.kroneckerMap_apply]
  have hq : ((finProdFinEquiv (i, k) : Fin (m * n)) : ℕ) = k + n * i :=
    finProdFinEquiv_apply_val _
  have hp : ((finProdFinEquiv (i', k') : Fin (m * n)) : ℕ) = k' + n * i' :=
    finProdFinEquiv_apply_val _
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => by
    have := k.2
    omega
  have hmod : (k + n * i : ℕ) % n = k := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt k.2]
  have hdiv : (k + n * i : ℕ) / n = i := by
    rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt k.2, zero_add]
  have hck : C.getD k 0 < 2 ^ n := by
    by_cases hlt : (k : ℕ) < C.length
    · rw [List.getD_eq_getElem _ _ hlt]
      exact hC _ (List.getElem_mem hlt)
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hlt)]
      exact Nat.two_pow_pos n
  simp only [maskMat, Matrix.of_apply]
  have hget : (kronM m n A C).getD ((finProdFinEquiv (i, k) : Fin (m * n)) : ℕ) 0 =
      actM (shifts m n (C.getD k 0)) (A.getD i 0) := by
    rw [kronM, List.getD_eq_getElem _ _ (by simpa using (finProdFinEquiv (i, k)).2),
      List.getElem_map, List.getElem_range, hq, hmod, hdiv]
  rw [hget, bvec_actM, Finset.sum_apply, bvec_apply, bvec_apply, length_shifts]
  rw [Finset.sum_eq_single (i' : ℕ)]
  · rw [getD_shifts i'.2]
    have hb : ((C.getD k 0) <<< (n * i')).testBit (k' + n * i') = (C.getD k 0).testBit k' := by
      rw [testBit_shift_block hck k'.2]
      simp
    rw [ite_apply, bvec_apply, hp, hb, Pi.zero_apply]
    by_cases h1 : (A.getD i 0).testBit i' <;> by_cases h2 : (C.getD k 0).testBit k' <;>
      simp only [h1, h2, ite_true, ite_false, Bool.false_eq_true, mul_one, mul_zero]
  · intro l hl hli
    rw [getD_shifts (Finset.mem_range.1 hl)]
    have hb : ((C.getD k 0) <<< (n * l)).testBit (k' + n * i') = false := by
      rw [testBit_shift_block hck k'.2]
      simp [hli]
    rw [ite_apply, bvec_apply, hp, hb, Pi.zero_apply]
    simp
  · intro h
    exact absurd (Finset.mem_range.2 i'.2) h

@[expose] def subOKM (m d : ℕ) (Ka Kb B P : List ℕ) : Bool :=
  (decide (Ka.length ≤ m) && decide (Kb.length ≤ m) && decide (B.length ≤ d) &&
    decide (P.length ≤ m)) &&
  decide (maskMat d d (mulM P B) = 1) && [Ka, Kb].all fun K =>
    let KB := mulM K B
    decide (maskMat m d KB = maskMat m d (mulM B (mulM P KB)))

@[expose] def quotOKM (m d : ℕ) (Ka Kb B P : List ℕ) : Bool :=
  (decide (Ka.length ≤ m) && decide (Kb.length ≤ m) && decide (B.length ≤ d) &&
    decide (P.length ≤ m)) &&
  decide (maskMat d d (mulM P B) = 1) && [Ka, Kb].all fun K =>
    let PK := mulM P K
    decide (maskMat d m PK = maskMat d m (mulM (mulM PK B) P))

theorem subOKM_spec {m d : ℕ} {Ka Kb B P : List ℕ} (h : subOKM m d Ka Kb B P = true) :
    maskMat d m P * maskMat m d B = 1 ∧ ∀ K ∈ [Ka, Kb],
      maskMat m m K * maskMat m d B =
        maskMat m d B * (maskMat d m P * maskMat m m K * maskMat m d B) := by
  simp only [subOKM, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hKa, hKb⟩, hB⟩, hP⟩, hPB⟩, hK⟩ := h
  refine ⟨by rwa [maskMat_mulM P B hP] at hPB, fun K hK' => ?_⟩
  have hKl : K.length ≤ m := by
    rcases List.mem_pair.1 hK' with rfl | rfl
    · exact hKa
    · exact hKb
  have h1 := hK K hK'
  rw [maskMat_mulM (m := m) (k := d) (n := d) B _ hB,
    maskMat_mulM (m := d) (k := m) (n := d) P _ hP,
    maskMat_mulM (m := m) (k := m) (n := d) K B hKl] at h1
  rw [h1, Matrix.mul_assoc (maskMat d m P)]

theorem quotOKM_spec {m d : ℕ} {Ka Kb B P : List ℕ} (h : quotOKM m d Ka Kb B P = true) :
    maskMat d m P * maskMat m d B = 1 ∧ ∀ K ∈ [Ka, Kb],
      maskMat d m P * maskMat m m K =
        maskMat d m P * maskMat m m K * maskMat m d B * maskMat d m P := by
  simp only [quotOKM, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hKa, hKb⟩, hB⟩, hP⟩, hPB⟩, hK⟩ := h
  refine ⟨by rwa [maskMat_mulM P B hP] at hPB, fun K hK' => ?_⟩
  have hKl : K.length ≤ m := by
    rcases List.mem_pair.1 hK' with rfl | rfl
    · exact hKa
    · exact hKb
  have hPKl : (mulM P K).length ≤ m := by
    rw [mulM, List.length_map]
    exact hKl
  have hPKBl : (mulM (mulM P K) B).length ≤ d := by
    rw [mulM, List.length_map]
    exact hB
  have h1 := hK K hK'
  rw [maskMat_mulM (m := d) (k := d) (n := m) (mulM (mulM P K) B) P hPKBl,
    maskMat_mulM (m := d) (k := m) (n := d) (mulM P K) B hPKl,
    maskMat_mulM (m := d) (k := m) (n := m) P K hP] at h1
  exact h1

end CFSG.Quasithin.B45Mat
