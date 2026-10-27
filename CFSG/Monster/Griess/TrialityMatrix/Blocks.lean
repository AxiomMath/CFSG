module

public import CFSG.Monster.Griess.TrialityBasis
import Mathlib.Tactic.NoncommRing

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster Matrix Module
open scoped Kronecker

section Diag2

variable {m n : Type*}

@[expose] def diag2 (A : Matrix m m ℚ) (D : Matrix n n ℚ) : Matrix (m ⊕ n) (m ⊕ n) ℚ :=
  fromBlocks A 0 0 D

theorem diag2_apply_inl_inl (A : Matrix m m ℚ) (D : Matrix n n ℚ) (i j : m) :
    diag2 A D (.inl i) (.inl j) = A i j := rfl

theorem diag2_apply_inl_inr (A : Matrix m m ℚ) (D : Matrix n n ℚ) (i : m) (j : n) :
    diag2 A D (.inl i) (.inr j) = 0 := rfl

theorem diag2_apply_inr_inl (A : Matrix m m ℚ) (D : Matrix n n ℚ) (i : n) (j : m) :
    diag2 A D (.inr i) (.inl j) = 0 := rfl

theorem diag2_apply_inr_inr (A : Matrix m m ℚ) (D : Matrix n n ℚ) (i j : n) :
    diag2 A D (.inr i) (.inr j) = D i j := rfl

theorem diag2_mul [Fintype m] [Fintype n] (A A' : Matrix m m ℚ) (D D' : Matrix n n ℚ) :
    diag2 A D * diag2 A' D' = diag2 (A * A') (D * D') := by
  simp only [diag2, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem diag2_transpose (A : Matrix m m ℚ) (D : Matrix n n ℚ) :
    (diag2 A D)ᵀ = diag2 Aᵀ Dᵀ := by
  simp only [diag2, fromBlocks_transpose, transpose_zero]

theorem diag2_one [DecidableEq m] [DecidableEq n] :
    diag2 (1 : Matrix m m ℚ) (1 : Matrix n n ℚ) = 1 :=
  fromBlocks_one

theorem diag2_pow [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℚ) (D : Matrix n n ℚ) (k : ℕ) : diag2 A D ^ k = diag2 (A ^ k) (D ^ k) := by
  induction k with
  | zero => simp only [pow_zero, diag2_one]
  | succ k ih => rw [pow_succ, ih, diag2_mul, ← pow_succ, ← pow_succ]

theorem trace_diag2 [Fintype m] [Fintype n] (A : Matrix m m ℚ) (D : Matrix n n ℚ) :
    trace (diag2 A D) = trace A + trace D := by
  simp only [trace, diag, Fintype.sum_sum_type]
  rfl

theorem diag2_diagonal [DecidableEq m] [DecidableEq n] (a : m → ℚ) (b : n → ℚ) :
    diag2 (diagonal a) (diagonal b) = diagonal (Sum.elim a b) :=
  fromBlocks_diagonal a b

theorem diag2_mem_dyadic {A : Matrix m m ℚ} {D : Matrix n n ℚ} (hA : ∀ i j, A i j ∈ dyadic)
    (hD : ∀ i j, D i j ∈ dyadic) : ∀ x y, diag2 A D x y ∈ dyadic
  | .inl i, .inl j => hA i j
  | .inl _, .inr _ => dyadic.zero_mem
  | .inr _, .inl _ => dyadic.zero_mem
  | .inr i, .inr j => hD i j

end Diag2

section Kron1

variable {n : Type*} (ι : Type*) [DecidableEq ι]

@[expose] def kron1 (A : Matrix n n ℚ) : Matrix (ι × n) (ι × n) ℚ := (1 : Matrix ι ι ℚ) ⊗ₖ A

theorem kron1_apply (A : Matrix n n ℚ) (i j : ι) (k l : n) :
    kron1 ι A (i, k) (j, l) = (1 : Matrix ι ι ℚ) i j * A k l := rfl

theorem kron1_mul [Fintype ι] [Fintype n] (A B : Matrix n n ℚ) :
    kron1 ι A * kron1 ι B = kron1 ι (A * B) := by
  rw [kron1, kron1, kron1, ← mul_kronecker_mul, Matrix.one_mul]

theorem kron1_transpose (A : Matrix n n ℚ) : (kron1 ι A)ᵀ = kron1 ι Aᵀ := by
  rw [kron1, kron1, ← kroneckerMap_transpose, transpose_one]

theorem kron1_one [DecidableEq n] : kron1 ι (1 : Matrix n n ℚ) = 1 := one_kronecker_one

theorem kron1_pow [Fintype ι] [Fintype n] [DecidableEq n] (A : Matrix n n ℚ) (k : ℕ) :
    kron1 ι A ^ k = kron1 ι (A ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, kron1_one]
  | succ k ih => rw [pow_succ, ih, kron1_mul, ← pow_succ]

theorem trace_kron1 [Fintype ι] [Fintype n] (A : Matrix n n ℚ) :
    trace (kron1 ι A) = Fintype.card ι * trace A := by
  rw [kron1, trace_kronecker, trace_one]

theorem kron1_diagonal [DecidableEq n] (s : n → ℚ) :
    kron1 ι (diagonal s) = diagonal fun p : ι × n => s p.2 := by
  rw [kron1, ← diagonal_one, diagonal_kronecker_diagonal]
  simp only [one_mul]

theorem one_apply_mem_dyadic {m : Type*} [DecidableEq m] (i j : m) :
    (1 : Matrix m m ℚ) i j ∈ dyadic := by
  rw [one_apply]
  split_ifs
  · exact dyadic.one_mem
  · exact dyadic.zero_mem

theorem kron1_mem_dyadic {A : Matrix n n ℚ} (hA : ∀ k l, A k l ∈ dyadic) :
    ∀ x y, kron1 ι A x y ∈ dyadic
  | (i, k), (j, l) => dyadic.mul_mem (one_apply_mem_dyadic i j) (hA k l)

end Kron1

@[expose] def cyc3 : Matrix (Fin 3) (Fin 3) ℚ := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

theorem cyc3_apply (k l : Fin 3) : cyc3 k l = if l = k + 1 then 1 else 0 := by
  fin_cases k <;> fin_cases l <;> simp [cyc3]

theorem cyc3_mul_transpose : cyc3 * cyc3ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc3, Matrix.mul_apply, Fin.sum_univ_three]

theorem cyc3_transpose_mul : cyc3ᵀ * cyc3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc3, Matrix.mul_apply, Fin.sum_univ_three]

theorem cyc3_pow_three : cyc3 ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, cyc3, Matrix.mul_apply, Fin.sum_univ_three]

theorem trace_cyc3 : trace cyc3 = 0 := by
  simp [trace, cyc3, Fin.sum_univ_three]

theorem cyc3_mem_dyadic (k l : Fin 3) : cyc3 k l ∈ dyadic := by
  rw [cyc3_apply]
  split_ifs
  · exact dyadic.one_mem
  · exact dyadic.zero_mem

theorem cyc3_conj_diagonal (s : Fin 3 → ℚ) :
    cyc3ᵀ * diagonal s * cyc3 = diagonal ![s 2, s 0, s 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyc3, Matrix.mul_apply, Fin.sum_univ_three, diagonal_apply]

@[expose] noncomputable def octH (d : OctadWord) :
    Matrix (Octad.EvenQuot (octSupp d)) (Octad.EvenQuot (octSupp d)) ℚ :=
  fourierMatrix (QuadraticMap.polarBilin (Octad.quadForm (octSupp d))) 3

@[expose] noncomputable def octD (d : OctadWord) :
    Matrix (Octad.EvenQuot (octSupp d)) (Octad.EvenQuot (octSupp d)) ℚ :=
  signMatrix (Octad.quadForm (octSupp d))

@[expose] noncomputable def octHD (d : OctadWord) :
    Matrix (Octad.EvenQuot (octSupp d)) (Octad.EvenQuot (octSupp d)) ℚ :=
  octH d * octD d

theorem octH_mul_transpose (d : OctadWord) : octH d * (octH d)ᵀ = 1 :=
  (Octad.eight_point_even_subset_quadratic_space (octSupp d) (card_octSupp d)).2.2.2.2.2.1

theorem octD_mul_transpose (d : OctadWord) : octD d * (octD d)ᵀ = 1 :=
  (Octad.eight_point_even_subset_quadratic_space (octSupp d) (card_octSupp d)).2.2.2.2.2.2.2.1

theorem orderOf_octHD (d : OctadWord) : orderOf (octHD d) = 3 :=
  (Octad.eight_point_even_subset_quadratic_space (octSupp d) (card_octSupp d)).2.2.2.2.2.2.2.2.2.1

theorem trace_octHD (d : OctadWord) : trace (octHD d) = 1 :=
  (Octad.eight_point_even_subset_quadratic_space (octSupp d)
    (card_octSupp d)).2.2.2.2.2.2.2.2.2.2.1

theorem octHD_pow_three (d : OctadWord) : octHD d ^ 3 = 1 := by
  rw [← orderOf_octHD d]
  exact pow_orderOf_eq_one _

theorem octHD_mul_transpose (d : OctadWord) : octHD d * (octHD d)ᵀ = 1 := by
  rw [octHD, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (octD d), octD_mul_transpose,
    Matrix.one_mul, octH_mul_transpose]

theorem octHD_transpose_mul (d : OctadWord) : (octHD d)ᵀ * octHD d = 1 :=
  mul_eq_one_comm.1 (octHD_mul_transpose d)

theorem octHD_mem_dyadic (d : OctadWord) (u v : Octad.EvenQuot (octSupp d)) :
    octHD d u v ∈ dyadic :=
  mul_mem_dyadic (fourierMatrix_mem_dyadic _ 3) (signMatrix_mem_dyadic _) u v

theorem octHD_cls (d : OctadWord) {δ ε : Finset (Fin 24)} (hδ : δ ⊆ octSupp d)
    (hδe : Even δ.card) (hε : ε ⊆ octSupp d) (hεe : Even ε.card) :
    octHD d (Octad.cls (octSupp d) δ) (Octad.cls (octSupp d) ε) =
      (8 : ℚ)⁻¹ * (-1) ^ ((δ ∩ ε).card + ε.card / 2) := by
  have h4 : 4 ∣ (octSupp d).card := by rw [card_octSupp]; norm_num
  rw [octHD, octD, signMatrix, mul_diagonal, octH, fourierMatrix,
    Octad.polarBilin_quadForm_cls h4 hδ hδe hε hεe, Octad.quadForm_cls h4 hε hεe,
    Octad.sgn_natCast, Octad.sgn_natCast, pow_add]
  norm_num
  ring

theorem sq_eq_transpose_of_pow_three {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℚ} (h3 : A ^ 3 = 1) (ho : A * Aᵀ = 1) : A ^ 2 = Aᵀ := by
  calc A ^ 2 = A ^ 2 * (A * Aᵀ) := by rw [ho, Matrix.mul_one]
    _ = A ^ 3 * Aᵀ := by rw [← Matrix.mul_assoc, ← pow_succ]
    _ = Aᵀ := by rw [h3, Matrix.one_mul]

theorem three_mul_finrank_ker_sub_one {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (T : Module.End ℚ V) (hT : T ^ 3 = 1) :
    3 * (finrank ℚ (LinearMap.ker (T - 1)) : ℚ) =
      finrank ℚ V + LinearMap.trace ℚ V T + LinearMap.trace ℚ V (T ^ 2) := by
  set P : Module.End ℚ V := (3 : ℚ)⁻¹ • (1 + T + T ^ 2) with hP
  have hT4 : T ^ 4 = T := by rw [pow_succ, hT, one_mul]
  have hPidem : IsIdempotentElem P := by
    show P * P = P
    rw [hP, smul_mul_smul_comm]
    have : (1 + T + T ^ 2) * (1 + T + T ^ 2) = (3 : ℚ) • (1 + T + T ^ 2) := by
      have e : (1 + T + T ^ 2) * (1 + T + T ^ 2) = 1 + 2 • T + 3 • T ^ 2 + 2 • T ^ 3 + T ^ 4 := by
        noncomm_ring
      rw [e, hT, hT4, ← Nat.cast_smul_eq_nsmul ℚ 2, ← Nat.cast_smul_eq_nsmul ℚ 3]
      module
    rw [this, smul_smul]
    norm_num
  have hrange : LinearMap.range P = LinearMap.ker (T - 1) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      show (T * P) y = P y
      rw [hP, mul_smul_comm]
      congr 1
      have e : T * (1 + T + T ^ 2) = T + T ^ 2 + T ^ 3 := by noncomm_ring
      rw [e, hT]
      abel_nf
    · intro hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
      refine ⟨x, ?_⟩
      have hx2 : (T ^ 2) x = x := by rw [pow_two, Module.End.mul_apply, hx, hx]
      rw [hP, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply,
        hx, hx2]
      module
  have htrace : LinearMap.trace ℚ V P = finrank ℚ (LinearMap.range P) :=
    LinearMap.IsProj.trace (LinearMap.IsIdempotentElem.isProj_range P hPidem)
  rw [← hrange, ← htrace, hP, map_smul, map_add, map_add, LinearMap.trace_one, smul_eq_mul]
  ring

theorem bform_toLin_of_gram {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℚ SpaceB)
    {N : ι → ℚ} (hb : ∀ x y, bform (b x) (b y) = if x = y then N x else 0)
    {M : Matrix ι ι ℚ} (hM : M * diagonal N * Mᵀ = diagonal N) (u v : SpaceB) :
    bform (toLin b b Mᵀ u) (toLin b b Mᵀ v) = bform u v := by
  have hG : LinearMap.toMatrix₂ b b bform = diagonal N := by
    ext x y
    rw [LinearMap.toMatrix₂_apply, hb, diagonal_apply]
  have key : LinearMap.toMatrix₂ b b (bform.compl₁₂ (toLin b b Mᵀ) (toLin b b Mᵀ)) =
      LinearMap.toMatrix₂ b b bform := by
    rw [LinearMap.toMatrix₂_compl₁₂ b b, LinearMap.toMatrix_toLin, transpose_transpose, hG, hM]
  exact LinearMap.congr_fun₂ ((LinearMap.toMatrix₂ b b).injective key) u v

theorem map_toLin_BR_le {M : Matrix TIdx TIdx ℚ} (hM : ∀ x y, M x y ∈ dyadic) :
    BR.map ((toLin tbasis tbasis M).restrictScalars dyadic) ≤ BR := by
  rw [← span_tbasis, Submodule.map_span_le]
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.restrictScalars_apply, toLin_self]
  refine Submodule.sum_mem _ fun y _ => ?_
  exact (Submodule.span dyadic (Set.range tbasis)).smul_mem (⟨M y x, hM y x⟩ : dyadic)
    (Submodule.subset_span ⟨y, rfl⟩)

theorem toLin_mem_BR {M : Matrix TIdx TIdx ℚ} (hM : ∀ x y, M x y ∈ dyadic) {u : SpaceB}
    (hu : u ∈ BR) : toLin tbasis tbasis M u ∈ BR :=
  map_toLin_BR_le hM ⟨u, hu, rfl⟩

theorem sum_ite_smul_tbasis (x : TIdx) :
    ∑ y : TIdx, (if y = x then (1 : ℚ) else 0) • tbasis y = tbasis x := by
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem toLin_diagonal_self {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℚ SpaceB)
    (s : ι → ℚ) (x : ι) : toLin b b (diagonal s) (b x) = s x • b x := by
  rw [toLin_self, Finset.sum_eq_single x (fun y _ hy => by rw [diagonal_apply_ne _ hy, zero_smul])
    (fun h => absurd (Finset.mem_univ x) h), diagonal_apply_eq]

end CFSG.Monster.Griess
