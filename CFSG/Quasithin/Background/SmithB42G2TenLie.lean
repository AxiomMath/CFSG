module

public import CFSG.Quasithin.Background.SmithB42G2TenNorm
public import CFSG.Quasithin.Background.SmithB42G2TenMat

public noncomputable section

namespace CFSG.Quasithin.B42G2Ten

open Matrix CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.Ch11.G2Q8
open scoped Kronecker

@[expose] def rk : Ix3 → ℕ
  | .inl i => i
  | .inr i => i + 3

abbrev LIdx : Type := Fin 14

@[expose] def lP : LIdx → Ix3 × Ix3 :=
  ![(.inl 0, .inl 1), (.inl 0, .inl 2), (.inl 0, .inr 0), (.inl 0, .inr 1), (.inl 0, .inr 2),
    (.inl 1, .inl 2), (.inl 1, .inr 0), (.inl 1, .inr 1), (.inl 1, .inr 2), (.inl 2, .inr 0),
    (.inl 2, .inr 1), (.inr 0, .inr 1), (.inr 0, .inr 2), (.inr 1, .inr 2)]

theorem lP_injective : Function.Injective lP := by decide

theorem rk_lP : ∀ p : LIdx, rk (lP p).1 < rk (lP p).2 := by decide

@[expose] def hwL : LIdx := 4

@[expose] def lowL : LIdx := 9

@[expose] def secB (q : Ix3 × Ix3) (p : LIdx) : Bool :=
  decide (q = lP p) || decide (q.swap = lP p) ||
    ((decide (q = (.inl 2, .inr 2)) || decide (q = (.inr 2, .inl 2))) &&
      (decide (p = 2) || decide (p = 7)))

theorem secB_coord : ∀ p p' : LIdx, secB (lP p) p' = decide (p = p') := by decide

theorem secB_swap : ∀ (q : Ix3 × Ix3) (p : LIdx), secB q.swap p = secB q p := by decide

theorem secB_diag : ∀ (i : Ix3) (p : LIdx), secB (i, i) p = false := by decide

theorem secB_con : ∀ p : LIdx, (secB (.inl 0, .inr 0) p ^^ secB (.inl 1, .inr 1) p) =
    secB (.inl 2, .inr 2) p := by decide

theorem pair_cases : ∀ q : Ix3 × Ix3, (∃ p, lP p = q) ∨ (∃ p, lP p = q.swap) ∨ q.1 = q.2 ∨
    q = (.inl 2, .inr 2) ∨ q = (.inr 2, .inl 2) := by decide

section Pair

variable {F : Type} [Field F] {ι : Type*} [Fintype ι]

@[expose] def pairM (X A : Matrix ι ι F) : F := ∑ i, ∑ j, X i j * A i j

theorem pairM_eq_trace (X A : Matrix ι ι F) : pairM X A = (Xᵀ * A).trace := by
  simp only [pairM, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

theorem pairM_conj (M X A : Matrix ι ι F) : pairM (M * X * Mᵀ) A = pairM X (Mᵀ * A * M) := by
  rw [pairM_eq_trace, pairM_eq_trace, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm,
    Matrix.mul_assoc, Matrix.mul_assoc]

variable [CharP F 2]

@[expose] def IsAltM (X : Matrix ι ι F) : Prop := (∀ i j, X i j = X j i) ∧ ∀ i, X i i = 0

theorem pairM_eq_of_add {X A A' : Matrix ι ι F} (hX : IsAltM X) (hA : A + Aᵀ = A' + A'ᵀ) :
    pairM X A = pairM X A' := by
  have h : ∑ p : ι × ι, X p.1 p.2 * (A p.1 p.2 - A' p.1 p.2) = 0 := by
    refine sum_symm_eq_zero _ (fun a b => ?_) (fun a => by rw [hX.2 a, zero_mul])
    have e := congrFun (congrFun hA a) b
    simp only [Matrix.add_apply, Matrix.transpose_apply] at e
    rw [hX.1 a b]
    congr 1
    linear_combination e + (A' b a - A b a) * CharTwo.two_eq_zero (R := F)
  rw [Fintype.sum_prod_type] at h
  simp only [mul_sub, Finset.sum_sub_distrib] at h
  exact sub_eq_zero.mp h

end Pair

section Lie

variable {F : Type} [Field F]

@[expose] def secL (F : Type) [Field F] : Matrix (Ix3 × Ix3) LIdx F :=
  Matrix.of fun q p => if secB q p then 1 else 0

@[expose] def lieSub (F : Type) [Field F] : Submodule F (Ix3 × Ix3 → F) where
  carrier := {T | (∀ i j, T (i, j) = T (j, i)) ∧ (∀ i, T (i, i) = 0) ∧
    T (.inl 0, .inr 0) + T (.inl 1, .inr 1) + T (.inl 2, .inr 2) = 0}
  add_mem' {T T'} hT hT' := by
    refine ⟨fun i j => ?_, fun i => ?_, ?_⟩
    · simp only [Pi.add_apply, hT.1 i j, hT'.1 i j]
    · simp only [Pi.add_apply, hT.2.1 i, hT'.2.1 i, add_zero]
    · simp only [Pi.add_apply]
      linear_combination hT.2.2 + hT'.2.2
  zero_mem' := ⟨fun _ _ => rfl, fun _ => rfl, by simp⟩
  smul_mem' c T hT := by
    refine ⟨fun i j => ?_, fun i => ?_, ?_⟩
    · simp only [Pi.smul_apply, hT.1 i j]
    · simp only [Pi.smul_apply, hT.2.1 i, smul_zero]
    · simp only [Pi.smul_apply, smul_eq_mul]
      linear_combination c * hT.2.2

@[expose] def toM (T : Ix3 × Ix3 → F) : Matrix Ix3 Ix3 F := Matrix.of fun i j => T (i, j)

omit [Field F] in
theorem toM_apply (T : Ix3 × Ix3 → F) (i j : Ix3) : toM T i j = T (i, j) := rfl

variable [CharP F 2]

@[expose] def rep2 : ↥(cayleyGroup F) →* Matrix (Ix3 × Ix3) (Ix3 × Ix3) F := kron2Rep repQ repQ

theorem toM_rep2 (g : ↥(cayleyGroup F)) (T : Ix3 × Ix3 → F) :
    toM ((rep2 g).mulVec T) = repQ g * toM T * (repQ g)ᵀ := by
  ext i j
  simp only [toM_apply, rep2, kron2Rep_apply, Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

omit [CharP F 2] in
theorem toM_mem_lieSub {T : Ix3 × Ix3 → F} (hT : T ∈ lieSub F) : IsAltM (toM T) :=
  ⟨fun i j => hT.1 i j, fun i => hT.2.1 i⟩

@[expose] def halfQ (F : Type) [Field F] : Matrix Ix3 Ix3 F :=
  Matrix.of fun i j => if j = i.swap ∧ rk i < rk j then 1 else 0

omit [CharP F 2] in
theorem halfQ_add : halfQ F + (halfQ F)ᵀ = formQ F := by
  ext i j
  simp only [Matrix.add_apply, Matrix.transpose_apply, halfQ, formQ_apply, Matrix.of_apply]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rk]

omit [CharP F 2] in
theorem pairM_halfQ (T : Ix3 × Ix3 → F) :
    pairM (toM T) (halfQ F) = T (.inl 0, .inr 0) + T (.inl 1, .inr 1) + T (.inl 2, .inr 2) := by
  simp only [pairM, toM_apply, halfQ, Matrix.of_apply, Fintype.sum_sum_type, Fin.sum_univ_three]
  simp [rk]

theorem halfQ_conj (g : ↥(cayleyGroup F)) :
    (repQ g)ᵀ * halfQ F * repQ g + ((repQ g)ᵀ * halfQ F * repQ g)ᵀ = halfQ F + (halfQ F)ᵀ := by
  rw [halfQ_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc ((repQ g)ᵀ) (halfQ F) (repQ g), ← Matrix.mul_add, ← Matrix.add_mul, halfQ_add,
    ← Matrix.mul_assoc, repQ_transpose_formQ]

theorem rep2_mem_lieSub (g : ↥(cayleyGroup F)) {T : Ix3 × Ix3 → F} (hT : T ∈ lieSub F) :
    (rep2 g).mulVec T ∈ lieSub F := by
  have hX := toM_mem_lieSub hT
  have key : toM ((rep2 g).mulVec T) = repQ g * toM T * (repQ g)ᵀ := toM_rep2 g T
  refine ⟨fun i j => ?_, fun i => ?_, ?_⟩
  · change toM ((rep2 g).mulVec T) i j = toM ((rep2 g).mulVec T) j i
    rw [key]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [show toM T b a = toM T a b from hX.1 b a]
    ring
  · change toM ((rep2 g).mulVec T) i i = 0
    rw [key]
    have h := sum_symm_eq_zero
      (fun p : Ix3 × Ix3 => repQ g i p.1 * toM T p.1 p.2 * repQ g i p.2)
      (fun a b => by simp only; rw [hX.1 a b]; ring) (fun a => by simp only [hX.2 a]; ring)
    rw [Fintype.sum_prod_type] at h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact h
  · rw [← pairM_halfQ, key, pairM_conj, pairM_eq_of_add hX (halfQ_conj g), pairM_halfQ]
    exact hT.2.2

omit [CharP F 2] in
theorem secL_apply (q : Ix3 × Ix3) (p : LIdx) :
    secL F q p = if secB q p then 1 else 0 := rfl

omit [CharP F 2] in
theorem secL_submatrix : (secL F).submatrix lP id = 1 := by
  ext p p'
  rw [Matrix.submatrix_apply, id, secL_apply, secB_coord, Matrix.one_apply]
  simp only [decide_eq_true_eq]

theorem ite_add_ite_xor (a b : Bool) :
    ((if a then 1 else 0 : F) + (if b then 1 else 0) + (if (a ^^ b) then 1 else 0)) = 0 := by
  cases a <;> cases b <;> simp [CharTwo.add_self_eq_zero]

theorem secL_mulVec_mem (x : LIdx → F) : (secL F).mulVec x ∈ lieSub F := by
  refine ⟨fun i j => ?_, fun i => ?_, ?_⟩
  · simp only [Matrix.mulVec, dotProduct, secL_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Prod.swap_prod_mk, secB_swap]
  · simp only [Matrix.mulVec, dotProduct, secL_apply, secB_diag]
    simp
  · simp only [Matrix.mulVec, dotProduct, ← Finset.sum_add_distrib, ← add_mul]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [secL_apply, secL_apply, secL_apply, ← secB_con, ite_add_ite_xor, zero_mul]

omit [CharP F 2] in
theorem eq_zero_of_lP {z : Ix3 × Ix3 → F} (hz : z ∈ lieSub F) (h0 : ∀ p, z (lP p) = 0) :
    z = 0 := by
  have h22 : z (.inl 2, .inr 2) = 0 := by
    have h := hz.2.2
    rw [show z (.inl 0, .inr 0) = 0 from h0 2, show z (.inl 1, .inr 1) = 0 from h0 7] at h
    simpa using h
  funext q
  rcases pair_cases q with ⟨p, rfl⟩ | ⟨p, hp⟩ | hq | rfl | rfl
  · exact h0 p
  · obtain ⟨i, j⟩ := q
    rw [hz.1 i j, Pi.zero_apply]
    have e : (j, i) = lP p := by rw [hp]; rfl
    rw [e]
    exact h0 p
  · obtain ⟨i, j⟩ := q
    simp only at hq
    subst hq
    exact hz.2.1 i
  · exact h22
  · rw [hz.1, Pi.zero_apply]
    exact h22

theorem isPivot_lie : IsPivot (rep2 (F := F)) lP (secL F) :=
  IsPivot.of_subspace' (lieSub F) (fun g _ hw => rep2_mem_lieSub g hw) secL_mulVec_mem
    secL_submatrix fun _ hz h0 => eq_zero_of_lP hz h0

@[expose] def repLie : ↥(cayleyGroup F) →* Matrix LIdx LIdx F := pivotRep isPivot_lie

theorem repLie_mulVec (g : ↥(cayleyGroup F)) (x : LIdx → F) (p : LIdx) :
    (repLie g).mulVec x p = (rep2 g).mulVec ((secL F).mulVec x) (lP p) :=
  pivotRep_mulVec isPivot_lie g x p

@[expose] def wedgeT (a b : Ix3) : Ix3 × Ix3 → F :=
  fun q => (if q = (a, b) then 1 else 0) + (if q = (b, a) then 1 else 0)

omit [CharP F 2] in
theorem wedgeT_apply (a b : Ix3) (q : Ix3 × Ix3) :
    wedgeT a b q = (if q = (a, b) then (1 : F) else 0) + (if q = (b, a) then 1 else 0) := rfl

theorem rep2_mulVec_wedgeT (g : ↥(cayleyGroup F)) (a b : Ix3) (q : Ix3 × Ix3) :
    (rep2 g).mulVec (wedgeT a b) q =
      repQ g q.1 a * repQ g q.2 b + repQ g q.1 b * repQ g q.2 a := by
  simp only [Matrix.mulVec, dotProduct, rep2, kron2Rep_apply, Matrix.kroneckerMap_apply,
    wedgeT_apply, mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [CharP F 2] in
theorem secL_mulVec_hwL : (secL F).mulVec (Pi.single hwL 1) = wedgeT (.inl 0) (.inr 2) := by
  have h : ∀ q : Ix3 × Ix3, secB q hwL = (decide (q = (.inl 0, .inr 2)) ||
      decide (q = (.inr 2, .inl 0))) := by decide
  funext q
  rw [Matrix.mulVec_single_one, Matrix.col_apply, secL_apply, h, wedgeT_apply]
  by_cases h1 : q = (.inl 0, .inr 2)
  · subst h1
    simp
  · by_cases h2 : q = (.inr 2, .inl 0)
    · subst h2
      simp
    · simp [h1, h2]

omit [CharP F 2] in
theorem secL_mulVec_lowL : (secL F).mulVec (Pi.single lowL 1) = wedgeT (.inl 2) (.inr 0) := by
  have h : ∀ q : Ix3 × Ix3, secB q lowL = (decide (q = (.inl 2, .inr 0)) ||
      decide (q = (.inr 0, .inl 2))) := by decide
  funext q
  rw [Matrix.mulVec_single_one, Matrix.col_apply, secL_apply, h, wedgeT_apply]
  by_cases h1 : q = (.inl 2, .inr 0)
  · subst h1
    simp
  · by_cases h2 : q = (.inr 0, .inl 2)
    · subst h2
      simp
    · simp [h1, h2]

theorem repLie_single_hwL (g : ↥(cayleyGroup F)) (p : LIdx) :
    (repLie g).mulVec (Pi.single hwL 1) p =
      repQ g (lP p).1 (.inl 0) * repQ g (lP p).2 (.inr 2) +
        repQ g (lP p).1 (.inr 2) * repQ g (lP p).2 (.inl 0) := by
  rw [repLie_mulVec, secL_mulVec_hwL, rep2_mulVec_wedgeT]

theorem repLie_single_lowL (g : ↥(cayleyGroup F)) (p : LIdx) :
    (repLie g).mulVec (Pi.single lowL 1) p =
      repQ g (lP p).1 (.inl 2) * repQ g (lP p).2 (.inr 0) +
        repQ g (lP p).1 (.inr 0) * repQ g (lP p).2 (.inl 2) := by
  rw [repLie_mulVec, secL_mulVec_lowL, rep2_mulVec_wedgeT]

theorem lP_snd_ne : ∀ p : LIdx, (lP p).2 ≠ .inl 0 := by decide

theorem ht_lP_snd : ∀ p : LIdx, ht (.inr 2) ≤ ht (lP p).2 := by decide

theorem repLie_U0_hw {u : ↥(cayleyGroup F)} (hu : u ∈ U0 F) :
    (repLie u).mulVec (Pi.single hwL 1) = Pi.single hwL 1 := by
  funext p
  rw [repLie_single_hwL, repQ_U0_apply hu (i := (lP p).1) (j := .inl 0) (Nat.zero_le _),
    repQ_U0_apply hu (i := (lP p).2) (j := .inr 2) (ht_lP_snd p),
    repQ_U0_apply hu (i := (lP p).2) (j := .inl 0) (Nat.zero_le _)]
  fin_cases p <;> simp [lP, hwL]

theorem repLie_g2Sw_hw :
    (repLie (g2Sw : ↥(cayleyGroup F))).mulVec (Pi.single hwL 1) = Pi.single lowL 1 := by
  funext p
  rw [repLie_single_hwL, repQ_g2Sw, formQ_apply, formQ_apply, formQ_apply, formQ_apply]
  fin_cases p <;> simp [lP, lowL]

theorem repLie_U0_low {u : ↥(cayleyGroup F)} (hu : u ∈ U0 F) :
    (repLie u).mulVec (Pi.single lowL 1) lowL = 1 ∧
      (repLie u).mulVec (Pi.single lowL 1) hwL = cG u := by
  refine ⟨?_, ?_⟩
  · rw [repLie_single_lowL]
    change repQ u (.inl 2) (.inl 2) * repQ u (.inr 0) (.inr 0) +
      repQ u (.inl 2) (.inr 0) * repQ u (.inr 0) (.inl 2) = 1
    rw [repQ_U0_apply hu (le_refl _), repQ_U0_apply hu (le_refl _),
      repQ_U0_apply hu (i := .inr 0) (j := .inl 2) (by decide)]
    simp
  · rw [repLie_single_lowL, cG]
    change repQ u (.inl 0) (.inl 2) * repQ u (.inr 2) (.inr 0) +
      repQ u (.inl 0) (.inr 0) * repQ u (.inr 2) (.inl 2) = _
    ring

theorem rk_injective : Function.Injective rk := by decide

omit [CharP F 2] in
theorem formQ_symm : (formQ F)ᵀ = formQ F := by
  ext i j
  simp only [Matrix.transpose_apply, formQ_apply]
  exact if_congr ⟨fun h => by rw [h, Sum.swap_swap], fun h => by rw [h, Sum.swap_swap]⟩ rfl rfl

omit [CharP F 2] in
theorem formQ_conj_apply (Y : Matrix Ix3 Ix3 F) (i j : Ix3) :
    (formQ F * Y * formQ F) i j = Y i.swap j.swap := by
  rw [formQ_mul, Matrix.mul_apply, Finset.sum_eq_single j.swap]
  · simp [formQ_apply]
  · intro k _ hk
    rw [formQ_apply, ite_eq_right fun h => hk (by rw [h, Sum.swap_swap]), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

@[expose] def upperM (Y : Matrix Ix3 Ix3 F) : Matrix Ix3 Ix3 F :=
  Matrix.of fun i j => if rk i < rk j then Y i j else 0

omit [CharP F 2] in
theorem upperM_add {Y : Matrix Ix3 Ix3 F} (hY : IsAltM Y) : upperM Y + (upperM Y)ᵀ = Y := by
  ext i j
  simp only [Matrix.add_apply, Matrix.transpose_apply, upperM, Matrix.of_apply]
  rcases lt_trichotomy (rk i) (rk j) with h | h | h
  · rw [ite_eq_left h, ite_eq_right (lt_asymm h), add_zero]
  · have hij := rk_injective h
    subst hij
    rw [ite_eq_right (lt_irrefl _), add_zero, hY.2]
  · rw [ite_eq_right (lt_asymm h), ite_eq_left h, zero_add, hY.1]

omit [CharP F 2] in
theorem isAltM_formQ_conj {Y : Matrix Ix3 Ix3 F} (hY : IsAltM Y) :
    IsAltM (formQ F * Y * formQ F) :=
  ⟨fun i j => by rw [formQ_conj_apply, formQ_conj_apply, hY.1],
    fun i => by rw [formQ_conj_apply, hY.2]⟩

theorem isAltM_conj (M : Matrix Ix3 Ix3 F) {X : Matrix Ix3 Ix3 F} (hX : IsAltM X) :
    IsAltM (M * X * Mᵀ) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hX.1 b a]
    ring
  · have h := sum_symm_eq_zero (fun p : Ix3 × Ix3 => M i p.1 * X p.1 p.2 * M i p.2)
      (fun a b => by simp only; rw [hX.1 a b]; ring) (fun a => by simp only [hX.2 a]; ring)
    rw [Fintype.sum_prod_type] at h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact h

@[expose] def formB (X Y : Matrix Ix3 Ix3 F) : F := pairM X (upperM (formQ F * Y * formQ F))

theorem formB_conj (g : ↥(cayleyGroup F)) {X Y : Matrix Ix3 Ix3 F} (hX : IsAltM X)
    (hY : IsAltM Y) :
    formB (repQ g * X * (repQ g)ᵀ) (repQ g * Y * (repQ g)ᵀ) = formB X Y := by
  set M := repQ g with hM
  set N := repQ g⁻¹ with hN
  have h1 : formQ F * M = Nᵀ * formQ F := formQ_mul_repQ g
  have h2 : Mᵀ * formQ F = formQ F * N := by
    have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, formQ_symm, Matrix.transpose_transpose]
      at this
  have hNM : N * M = 1 := by rw [hN, hM, ← map_mul, inv_mul_cancel, map_one]
  set H := upperM (formQ F * Y * formQ F)
  have hH : H + Hᵀ = formQ F * Y * formQ F := upperM_add (isAltM_formQ_conj hY)
  have e1 : formQ F * (M * Y * Mᵀ) * formQ F = Nᵀ * (formQ F * Y * formQ F) * N :=
    calc formQ F * (M * Y * Mᵀ) * formQ F = (formQ F * M) * Y * (Mᵀ * formQ F) := by
          simp only [Matrix.mul_assoc]
      _ = (Nᵀ * formQ F) * Y * (formQ F * N) := by rw [h1, h2]
      _ = Nᵀ * (formQ F * Y * formQ F) * N := by simp only [Matrix.mul_assoc]
  have e2 : upperM (formQ F * (M * Y * Mᵀ) * formQ F) +
      (upperM (formQ F * (M * Y * Mᵀ) * formQ F))ᵀ = Nᵀ * H * N + (Nᵀ * H * N)ᵀ := by
    rw [upperM_add (isAltM_formQ_conj (isAltM_conj M hY)), e1, ← hH, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_assoc Nᵀ Hᵀ N]
  have e3 : Mᵀ * (Nᵀ * H * N) * M = H :=
    calc Mᵀ * (Nᵀ * H * N) * M = (N * M)ᵀ * H * (N * M) := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = H := by rw [hNM, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  rw [formB, pairM_eq_of_add (isAltM_conj M hX) e2, pairM_conj, e3, formB]

@[expose] def dualL : LIdx → LIdx := ![11, 12, 7, 6, 9, 13, 3, 2, 10, 4, 8, 0, 1, 5]

theorem dualL_dualL : ∀ p : LIdx, dualL (dualL p) = p := by decide

@[expose] def gramL (F : Type) [Field F] : Matrix LIdx LIdx F :=
  Matrix.of fun p p' => if p' = dualL p then 1 else 0

omit [CharP F 2] in
theorem gramL_mul_self : gramL F * gramL F = 1 := by
  ext p p''
  rw [Matrix.mul_apply]
  simp only [gramL, Matrix.of_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, dualL_dualL, Matrix.one_apply]
  exact if_congr eq_comm rfl rfl

theorem formB_secL (x y : LIdx → F) :
    formB (toM ((secL F).mulVec x)) (toM ((secL F).mulVec y)) = x ⬝ᵥ (gramL F).mulVec y := by
  simp only [formB, pairM, upperM, formQ_conj_apply, toM_apply, Matrix.of_apply, gramL,
    Matrix.mulVec, dotProduct, secL_apply, Fintype.sum_sum_type, Fin.sum_univ_succ,
    Fin.sum_univ_zero, rk, secB, lP, dualL]
  simp
  ring_nf
  reduce_mod_char!

theorem isAltM_toM_secL (x : LIdx → F) : IsAltM (toM ((secL F).mulVec x)) :=
  toM_mem_lieSub (secL_mulVec_mem x)

theorem secL_repLie (g : ↥(cayleyGroup F)) (x : LIdx → F) :
    (secL F).mulVec ((repLie g).mulVec x) = (rep2 g).mulVec ((secL F).mulVec x) :=
  sec_mulVec_pivotRep isPivot_lie g x

theorem repLie_transpose_gramL (g : ↥(cayleyGroup F)) :
    (repLie g)ᵀ * gramL F * repLie g = gramL F := by
  refine transpose_mul_mul_of_dotProduct fun x y => ?_
  rw [← formB_secL, ← formB_secL, secL_repLie, secL_repLie, toM_rep2, toM_rep2,
    formB_conj g (isAltM_toM_secL x) (isAltM_toM_secL y)]

theorem gramL_mul_repLie (g : ↥(cayleyGroup F)) :
    gramL F * repLie g = (repLie g⁻¹)ᵀ * gramL F :=
  gram_mul_rep repLie (gramL F) repLie_transpose_gramL g

theorem dualL_hwL : dualL hwL = lowL := by decide

end Lie

end CFSG.Quasithin.B42G2Ten
