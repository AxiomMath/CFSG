module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.LinearCombination

public noncomputable section

namespace CFSG.Monster.Jordan

open Matrix

variable {ι : Type*}

@[expose] def symMat (ι : Type*) : Submodule ℝ (Matrix ι ι ℝ) where
  carrier := {A | Aᵀ = A}
  add_mem' {A B} hA hB := by
    change (A + B)ᵀ = A + B
    rw [transpose_add, show Aᵀ = A from hA, show Bᵀ = B from hB]
  zero_mem' := transpose_zero
  smul_mem' c A hA := by
    change (c • A)ᵀ = c • A
    rw [transpose_smul, show Aᵀ = A from hA]

theorem mem_symMat {A : Matrix ι ι ℝ} : A ∈ symMat ι ↔ Aᵀ = A := Iff.rfl

theorem transpose_coe (A : symMat ι) : (A : Matrix ι ι ℝ)ᵀ = A := A.2

section Units

variable [DecidableEq ι]

@[expose] def diagUnit (i : ι) : symMat ι := ⟨single i i 1, transpose_single i i 1⟩

@[expose] def pairUnit (i j : ι) : symMat ι :=
  ⟨single i j 1 + single j i 1, by
    rw [mem_symMat, transpose_add, transpose_single, transpose_single, add_comm]⟩

theorem coe_diagUnit (i : ι) : (diagUnit i : Matrix ι ι ℝ) = single i i 1 := rfl

theorem coe_pairUnit (i j : ι) :
    (pairUnit i j : Matrix ι ι ℝ) = single i j 1 + single j i 1 := rfl

theorem pairUnit_comm (i j : ι) : pairUnit i j = pairUnit j i :=
  Subtype.ext (add_comm _ _)

end Units

variable [Fintype ι]

@[expose] def jordanMul (A B : symMat ι) : symMat ι :=
  ⟨(1 / 2 : ℝ) • ((A : Matrix ι ι ℝ) * B + B * A), by
    rw [mem_symMat, transpose_smul, transpose_add, transpose_mul, transpose_mul, transpose_coe,
      transpose_coe, add_comm]⟩

theorem coe_jordanMul (A B : symMat ι) :
    (jordanMul A B : Matrix ι ι ℝ) = (1 / 2 : ℝ) • ((A : Matrix ι ι ℝ) * B + B * A) := rfl

theorem coe_jordanMul_self (A : symMat ι) :
    (jordanMul A A : Matrix ι ι ℝ) = (A : Matrix ι ι ℝ) * A := by
  rw [coe_jordanMul, ← two_smul ℝ ((A : Matrix ι ι ℝ) * A), smul_smul]
  norm_num

theorem trace_mul_self_of_symm {Q : Matrix ι ι ℝ} (hQ : Qᵀ = Q) :
    trace (Q * Q) = ∑ x, ∑ y, Q x y ^ 2 := by
  simp only [trace, diag, mul_apply, sq]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [← transpose_apply Q x y, hQ]

omit [Fintype ι] in
theorem eq_zero_of_sum_sq_eq_zero [Fintype ι] {Q : Matrix ι ι ℝ}
    (h : ∑ x, ∑ y, Q x y ^ 2 = 0) : Q = 0 := by
  ext x y
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun x _ =>
    Finset.sum_nonneg fun y _ => sq_nonneg (Q x y)).1 h x (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => sq_nonneg (Q x y)).1 h1 y
    (Finset.mem_univ _)
  simpa using h2

theorem exists_eq_vecMulVec {P : Matrix ι ι ℝ} (hs : Pᵀ = P) (hi : P * P = P)
    (ht : trace P = 1) : ∃ v : ι → ℝ, v ⬝ᵥ v = 1 ∧ P = vecMulVec v v := by
  have hsymm : ∀ x y, P y x = P x y := fun x y => by rw [← transpose_apply P x y, hs]
  have hPP : ∀ x y, ∑ b, P x b * P b y = P x y := fun x y => by rw [← mul_apply, hi]
  have hdiag : ∀ a, P a a = ∑ b, P b a ^ 2 := fun a => by
    rw [← hPP a a]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [sq, hsymm b a]
  obtain ⟨a, ha⟩ : ∃ a, 0 < P a a := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have : trace P ≤ 0 := Finset.sum_nonpos fun a _ => h a
    linarith
  have hsq : Real.sqrt (P a a) ^ 2 = P a a := Real.sq_sqrt ha.le
  have hs0 : Real.sqrt (P a a) ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  set v : ι → ℝ := fun b => P b a / Real.sqrt (P a a) with hv
  have hvv : v ⬝ᵥ v = 1 := by
    simp only [dotProduct, hv]
    rw [Finset.sum_congr rfl fun b _ => by rw [div_mul_div_comm, ← sq, ← sq, hsq],
      ← Finset.sum_div, ← hdiag, div_self ha.ne']
  have hPv : P *ᵥ v = v := by
    funext x
    simp only [mulVec, dotProduct, hv, mul_div_assoc']
    rw [← Finset.sum_div, hPP x a]
  have hvP : v ᵥ* P = v := by rw [← mulVec_transpose, hs, hPv]
  refine ⟨v, hvv, ?_⟩
  have h1 : P * vecMulVec v v = vecMulVec v v := by rw [mul_vecMulVec, hPv]
  have h2 : vecMulVec v v * P = vecMulVec v v := by rw [vecMulVec_mul, hvP]
  have h3 : vecMulVec v v * vecMulVec v v = vecMulVec v v := by
    rw [vecMulVec_mul_vecMulVec, hvv, one_smul]
  set Q := P - vecMulVec v v with hQ
  have hQs : Qᵀ = Q := by rw [hQ, transpose_sub, hs, transpose_vecMulVec]
  have hQi : Q * Q = Q := by
    rw [hQ, sub_mul, mul_sub, mul_sub, hi, h1, h2, h3]
    abel
  have hQt : trace Q = 0 := by rw [hQ, trace_sub, ht, trace_vecMulVec, hvv, sub_self]
  have h0 : Q = 0 := eq_zero_of_sum_sq_eq_zero (by rw [← trace_mul_self_of_symm hQs, hQi, hQt])
  exact sub_eq_zero.1 h0

variable [DecidableEq ι]

theorem single_mul_apply_eq (a : ι) (X : Matrix ι ι ℝ) (x y : ι) :
    (single a a (1 : ℝ) * X) x y = if x = a then X a y else 0 := by
  by_cases h : x = a
  · subst h; simp
  · simp [h]

theorem mul_single_apply_eq (a : ι) (X : Matrix ι ι ℝ) (x y : ι) :
    (X * single a a (1 : ℝ)) x y = if y = a then X x a else 0 := by
  by_cases h : y = a
  · subst h; simp
  · simp [h]

theorem eq_smul_of_jordan_relations {X : Matrix ι ι ℝ} (hX : Xᵀ = X) {a b : ι} (hab : a ≠ b)
    (ha : single a a 1 * X + X * single a a 1 = X)
    (hb : single b b 1 * X + X * single b b 1 = X) :
    X = X a b • (single a b 1 + single b a 1) := by
  have ea : ∀ x y, (if x = a then X a y else 0) + (if y = a then X x a else 0) = X x y :=
    fun x y => by
      rw [← single_mul_apply_eq, ← mul_single_apply_eq, ← Matrix.add_apply, ha]
  have eb : ∀ x y, (if x = b then X b y else 0) + (if y = b then X x b else 0) = X x y :=
    fun x y => by
      rw [← single_mul_apply_eq, ← mul_single_apply_eq, ← Matrix.add_apply, hb]
  have hsymm : X b a = X a b := by rw [← transpose_apply X a b, hX]
  ext x y
  simp only [Matrix.smul_apply, Matrix.add_apply, single_apply, smul_eq_mul]
  by_cases h1 : x = a ∧ y = b
  · obtain ⟨rfl, rfl⟩ := h1
    simp [hab]
  by_cases h2 : x = b ∧ y = a
  · obtain ⟨rfl, rfl⟩ := h2
    simp [hab, hsymm]
  rw [ite_eq_right fun h => h1 ⟨h.1.symm, h.2.symm⟩,
    ite_eq_right fun h => h2 ⟨h.1.symm, h.2.symm⟩, add_zero, mul_zero]
  by_cases h3 : x ≠ a ∧ y ≠ a
  · have := ea x y
    rw [ite_eq_right h3.1, ite_eq_right h3.2, add_zero] at this
    exact this.symm
  · have h4 : x ≠ b ∧ y ≠ b := by
      constructor
      · rintro rfl
        exact h2 ⟨rfl, by_contra fun hy => h3 ⟨hab.symm, hy⟩⟩
      · rintro rfl
        exact h1 ⟨by_contra fun hx => h3 ⟨hx, hab.symm⟩, rfl⟩
    have := eb x y
    rw [ite_eq_right h4.1, ite_eq_right h4.2, add_zero] at this
    exact this.symm

omit [Fintype ι] in
theorem pair_apply {a b : ι} (hab : a ≠ b) :
    (single a b (1 : ℝ) + single b a 1 : Matrix ι ι ℝ) a b = 1 := by
  simp [hab.symm]

theorem diag_mul_pair {a b : ι} (hab : a ≠ b) :
    single a a (1 : ℝ) * (single a b 1 + single b a 1) +
      (single a b 1 + single b a 1) * single a a 1 = single a b 1 + single b a 1 := by
  simp [Matrix.mul_add, Matrix.add_mul, hab, hab.symm]

theorem pair_mul_pair {a b c : ι} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (single a b (1 : ℝ) + single b a 1) * (single b c 1 + single c b 1) +
      (single b c 1 + single c b 1) * (single a b 1 + single b a 1) =
      single a c 1 + single c a 1 := by
  simp [Matrix.mul_add, Matrix.add_mul, hab, hbc, hac, hab.symm, hbc.symm, hac.symm]

theorem trace_pair_mul_pair {a b : ι} (hab : a ≠ b) :
    trace ((single a b (1 : ℝ) + single b a 1) * (single a b 1 + single b a 1)) = 2 := by
  simp [Matrix.mul_add, Matrix.add_mul, hab, hab.symm]
  norm_num

theorem jordanMul_diagUnit_pairUnit {a b : ι} (hab : a ≠ b) :
    jordanMul (diagUnit a) (pairUnit a b) = (1 / 2 : ℝ) • pairUnit a b :=
  Subtype.ext (by rw [coe_jordanMul, Submodule.coe_smul, coe_diagUnit, coe_pairUnit,
    diag_mul_pair hab])

theorem jordanMul_pairUnit_pairUnit {a b c : ι} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    jordanMul (pairUnit a b) (pairUnit b c) = (1 / 2 : ℝ) • pairUnit a c :=
  Subtype.ext (by rw [coe_jordanMul, Submodule.coe_smul, coe_pairUnit, coe_pairUnit,
    coe_pairUnit, pair_mul_pair hab hbc hac])

section Existence

variable (f : symMat ι →ₗ[ℝ] symMat ι)
  (hJ : ∀ A B, f (jordanMul A B) = jordanMul (f A) (f B))
    (hT : ∀ A B, trace ((f A : Matrix ι ι ℝ) * (f B : Matrix ι ι ℝ)) =
      trace ((A : Matrix ι ι ℝ) * (B : Matrix ι ι ℝ)))

include hJ hT in
theorem exists_orthonormal_vecMulVec : ∃ v : ι → ι → ℝ,
    (∀ i j, v i ⬝ᵥ v j = if i = j then 1 else 0) ∧
      ∀ i, (f (diagUnit i) : Matrix ι ι ℝ) = vecMulVec (v i) (v i) := by
  have hidem : ∀ i, (f (diagUnit i) : Matrix ι ι ℝ) * f (diagUnit i) = f (diagUnit i) := by
    intro i
    have h1 : jordanMul (diagUnit i) (diagUnit i) = diagUnit i :=
      Subtype.ext (by rw [coe_jordanMul_self, coe_diagUnit, single_mul_single_same, mul_one])
    rw [← coe_jordanMul_self, ← hJ, h1]
  have htr : ∀ i j, trace ((f (diagUnit i) : Matrix ι ι ℝ) * (f (diagUnit j) : Matrix ι ι ℝ)) =
      if i = j then 1 else 0 := by
    intro i j
    rw [hT, coe_diagUnit, coe_diagUnit]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  have : ∀ i, ∃ w : ι → ℝ, w ⬝ᵥ w = 1 ∧ (f (diagUnit i) : Matrix ι ι ℝ) = vecMulVec w w :=
    fun i => exists_eq_vecMulVec (transpose_coe _) (hidem i)
      (by rw [← hidem i, htr, ite_eq_left rfl])
  choose v hv1 hv2 using this
  refine ⟨v, fun i j => ?_, hv2⟩
  by_cases h : i = j
  · subst h; rw [hv1, ite_eq_left rfl]
  · rw [ite_eq_right h]
    have := htr i j
    rw [ite_eq_right h, hv2, hv2, vecMulVec_mul_vecMulVec, trace_vecMulVec, dotProduct_smul,
      smul_eq_mul] at this
    exact mul_self_eq_zero.1 this

include hJ hT in
theorem exists_orthogonal_eq_conj :
    ∃ g ∈ Matrix.orthogonalGroup ι ℝ,
      ∀ A : symMat ι, (f A : Matrix ι ι ℝ) = gᵀ * (A : Matrix ι ι ℝ) * g := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨o⟩⟩
  · exact ⟨1, (mem_orthogonalGroup_iff _ _).2 (Subsingleton.elim _ _),
      fun A => Subsingleton.elim _ _⟩
  obtain ⟨v, hv1, hv2⟩ := exists_orthonormal_vecMulVec f hJ hT
  set g : Matrix ι ι ℝ := Matrix.of fun i a => v i a with hgdef
  have hggt : g * gᵀ = 1 := by
    ext i j
    rw [mul_apply, one_apply, ← hv1 i j]
    rfl
  have hgtg : gᵀ * g = 1 := mul_eq_one_comm.1 hggt
  have hgtg' : ∀ X : Matrix ι ι ℝ, gᵀ * (g * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hgtg, Matrix.one_mul]
  have hggt' : ∀ X : Matrix ι ι ℝ, g * (gᵀ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hggt, Matrix.one_mul]
  have hconj : ∀ i, (f (diagUnit i) : Matrix ι ι ℝ) = gᵀ * single i i 1 * g := by
    intro i
    rw [hv2 i]
    ext a b
    rw [vecMulVec_apply, mul_apply]
    simp only [mul_single_apply_eq, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    rfl
  obtain ⟨F, hF⟩ : ∃ F : symMat ι → Matrix ι ι ℝ, ∀ A, F A = g * (f A : Matrix ι ι ℝ) * gᵀ :=
    ⟨_, fun _ => rfl⟩
  have hfF : ∀ A, (f A : Matrix ι ι ℝ) = gᵀ * F A * g := fun A => by
    simp only [hF, Matrix.mul_assoc, hgtg', hgtg, Matrix.mul_one]
  have hF_smul : ∀ (c : ℝ) A, F (c • A) = c • F A := fun c A => by
    rw [hF, hF, map_smul, Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hF_diag : ∀ i, F (diagUnit i) = single i i 1 := fun i => by
    rw [hF, hconj i]
    simp only [Matrix.mul_assoc, hggt, Matrix.mul_one, hggt']
  have hFF : ∀ A B, F A * F B = g * ((f A : Matrix ι ι ℝ) * f B) * gᵀ := fun A B => by
    simp only [hF, Matrix.mul_assoc, hgtg']
  have hF_jordan : ∀ A B, F (jordanMul A B) = (1 / 2 : ℝ) • (F A * F B + F B * F A) :=
    fun A B => by
      rw [hFF, hFF, hF, hJ, coe_jordanMul]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]
  have hF_trace : ∀ A B, trace (F A * F B) = trace ((A : Matrix ι ι ℝ) * (B : Matrix ι ι ℝ)) :=
    fun A B => by
      rw [hFF, trace_mul_comm, ← Matrix.mul_assoc, hgtg, Matrix.one_mul, hT]
  have hF_symm : ∀ A, (F A)ᵀ = F A := fun A => by
    rw [hF, transpose_mul, transpose_mul, transpose_transpose, transpose_coe, Matrix.mul_assoc]
  have hrel : ∀ a b, a ≠ b →
      single a a 1 * F (pairUnit a b) + F (pairUnit a b) * single a a 1 = F (pairUnit a b) := by
    intro a b hab
    have h := hF_jordan (diagUnit a) (pairUnit a b)
    rw [jordanMul_diagUnit_pairUnit hab, hF_smul, hF_diag] at h
    exact (smul_right_injective (Matrix ι ι ℝ) (by norm_num : (1 / 2 : ℝ) ≠ 0) h).symm
  obtain ⟨ε, hε⟩ : ∃ ε : ι → ι → ℝ, ∀ a b, a ≠ b →
      F (pairUnit a b) = ε a b • (single a b 1 + single b a 1) :=
    ⟨fun a b => F (pairUnit a b) a b, fun a b hab =>
      eq_smul_of_jordan_relations (hF_symm _) hab (hrel a b hab)
        (by rw [pairUnit_comm a b]; exact hrel b a hab.symm)⟩
  have hε2 : ∀ a b, a ≠ b → ε a b * ε a b = 1 := by
    intro a b hab
    have h := hF_trace (pairUnit a b) (pairUnit a b)
    rw [hε a b hab, coe_pairUnit, Matrix.smul_mul, Matrix.mul_smul, trace_smul, trace_smul,
      trace_pair_mul_pair hab, smul_eq_mul, smul_eq_mul] at h
    linear_combination h / 2
  have hεsymm : ∀ a b, a ≠ b → ε b a = ε a b := by
    intro a b hab
    have h := hε b a hab.symm
    rw [← pairUnit_comm a b, hε a b hab] at h
    have h2 := congrFun (congrFun h a) b
    simp [hab, hab.symm] at h2
    exact h2.symm
  have hcocycle : ∀ a b c, a ≠ b → b ≠ c → a ≠ c → ε a c = ε a b * ε b c := by
    intro a b c hab hbc hac
    have h := hF_jordan (pairUnit a b) (pairUnit b c)
    rw [jordanMul_pairUnit_pairUnit hab hbc hac, hF_smul, hε a c hac, hε a b hab, hε b c hbc,
      smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (ε b c), ← smul_add,
      pair_mul_pair hab hbc hac] at h
    have h2 := congrFun (congrFun
      (smul_right_injective (Matrix ι ι ℝ) (by norm_num : (1 / 2 : ℝ) ≠ 0) h) a) c
    simp only [Matrix.smul_apply, pair_apply hac, smul_eq_mul, mul_one] at h2
    exact h2
  set d : ι → ℝ := fun x => if x = o then 1 else ε o x with hd
  have hdd : ∀ x, d x * d x = 1 := fun x => by
    by_cases hx : x = o
    · simp [hd, hx]
    · simp only [hd, ite_eq_right hx]
      exact hε2 o x (Ne.symm hx)
  have hεd : ∀ x y, x ≠ y → ε x y = d x * d y := by
    intro x y hxy
    by_cases hx : x = o
    · subst hx
      simp [hd, Ne.symm hxy]
    · by_cases hy : y = o
      · subst hy
        simp only [hd, ite_eq_right hx, ite_eq_left rfl, mul_one]
        exact hεsymm _ _ (Ne.symm hx)
      · simp only [hd, ite_eq_right hx, ite_eq_right hy]
        rw [hcocycle x o y hx (Ne.symm hy) hxy, hεsymm o x (Ne.symm hx)]
  have hFpair : ∀ x y, F (pairUnit x y) = (d x * d y) • (single x y 1 + single y x 1) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      have h2 : pairUnit x x = (2 : ℝ) • diagUnit x :=
        Subtype.ext (by rw [coe_pairUnit, Submodule.coe_smul, coe_diagUnit, two_smul])
      rw [h2, hF_smul, hF_diag, hdd, one_smul, two_smul]
    · rw [hε x y hxy, hεd x y hxy]
  have hFA : ∀ A : symMat ι, F A = diagonal d * (A : Matrix ι ι ℝ) * diagonal d := by
    intro A
    ext x y
    have h := hF_trace A (pairUnit x y)
    rw [hFpair x y, Matrix.mul_smul, trace_smul, coe_pairUnit, Matrix.mul_add, Matrix.mul_add,
      trace_add, trace_add, trace_mul_single, trace_mul_single, trace_mul_single,
      trace_mul_single] at h
    simp only [MulOpposite.op_one, one_smul, smul_eq_mul] at h
    have hs1 : F A y x = F A x y := by rw [← transpose_apply (F A) x y, hF_symm]
    have hs2 : (A : Matrix ι ι ℝ) y x = (A : Matrix ι ι ℝ) x y := by
      rw [← transpose_apply (A : Matrix ι ι ℝ) x y, transpose_coe]
    rw [hs1, hs2] at h
    rw [mul_diagonal, diagonal_mul]
    linear_combination (d x * d y / 2) * h - F A x y * hdd x - F A x y * d x * d x * hdd y
  refine ⟨diagonal d * g, ?_, fun A => ?_⟩
  · rw [mem_orthogonalGroup_iff]
    simp only [transpose_mul, diagonal_transpose, Matrix.mul_assoc]
    rw [hggt', diagonal_mul_diagonal, show (fun x => d x * d x) = fun _ => (1 : ℝ) from funext hdd,
      diagonal_one]
  · rw [hfF A, hFA A, transpose_mul, diagonal_transpose]
    simp only [Matrix.mul_assoc]

end Existence

theorem eq_or_eq_neg_of_conj_eq {g g' : Matrix ι ι ℝ} (hg : g ∈ Matrix.orthogonalGroup ι ℝ)
    (hg' : g' ∈ Matrix.orthogonalGroup ι ℝ)
    (h : ∀ A : symMat ι, gᵀ * (A : Matrix ι ι ℝ) * g = g'ᵀ * (A : Matrix ι ι ℝ) * g') :
    g' = g ∨ g' = -g := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨o⟩⟩
  · exact Or.inl (Subsingleton.elim _ _)
  have hgg : g * gᵀ = 1 := (mem_orthogonalGroup_iff _ _).1 hg
  have hgtg : gᵀ * g = 1 := (mem_orthogonalGroup_iff' _ _).1 hg
  have hg'g' : g' * g'ᵀ = 1 := (mem_orthogonalGroup_iff _ _).1 hg'
  obtain ⟨k, hk⟩ : ∃ k : Matrix ι ι ℝ, k = g' * gᵀ := ⟨_, rfl⟩
  have hkk : k * kᵀ = 1 := by
    rw [hk, transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc gᵀ, hgtg,
      Matrix.one_mul, hg'g']
  have hconj : ∀ A : symMat ι, kᵀ * (A : Matrix ι ι ℝ) * k = A := by
    intro A
    rw [hk, transpose_mul, transpose_transpose]
    calc g * g'ᵀ * (A : Matrix ι ι ℝ) * (g' * gᵀ) = g * (g'ᵀ * A * g') * gᵀ := by
          simp only [Matrix.mul_assoc]
      _ = g * (gᵀ * A * g) * gᵀ := by rw [h A]
      _ = A := by
          simp only [Matrix.mul_assoc, hgg, Matrix.mul_one]
          rw [← Matrix.mul_assoc, hgg, Matrix.one_mul]
  have hcomm : ∀ A : symMat ι, Commute (A : Matrix ι ι ℝ) k := by
    intro A
    change (A : Matrix ι ι ℝ) * k = k * A
    calc (A : Matrix ι ι ℝ) * k = k * kᵀ * A * k := by rw [hkk, Matrix.one_mul]
      _ = k * (kᵀ * A * k) := by simp only [Matrix.mul_assoc]
      _ = k * A := by rw [hconj A]
  have hsingle : Pairwise fun x y => Commute (single x y (1 : ℝ)) k := by
    intro x y hxy
    have e : single x y (1 : ℝ) = single x x 1 * (single x y 1 + single y x 1) := by
      simp [Matrix.mul_add, hxy]
    rw [e]
    exact (hcomm (diagUnit x)).mul_left (hcomm (pairUnit x y))
  obtain ⟨c, hc⟩ := mem_range_scalar_of_commute_single hsingle
  have hc2 : c * c = 1 := by
    rw [← hc, scalar_apply, diagonal_transpose, diagonal_mul_diagonal] at hkk
    simpa using congrFun (congrFun hkk o) o
  have hg'k : g' = k * g := by rw [hk, Matrix.mul_assoc, hgtg, Matrix.mul_one]
  rcases mul_self_eq_one_iff.1 hc2 with rfl | rfl
  · left
    rw [hg'k, ← hc, map_one, Matrix.one_mul]
  · right
    rw [hg'k, ← hc, map_neg, map_one, Matrix.neg_mul, Matrix.one_mul]

theorem symmetric_matrix_isometric_jordan_automorphisms {n : ℕ}
    (f : symMat (Fin n) ≃ₗ[ℝ] symMat (Fin n))
    (hJ : ∀ A B, f (jordanMul A B) = jordanMul (f A) (f B))
    (hT : ∀ A B, trace ((f A : Matrix (Fin n) (Fin n) ℝ) * (f B : Matrix (Fin n) (Fin n) ℝ)) =
      trace ((A : Matrix (Fin n) (Fin n) ℝ) * (B : Matrix (Fin n) (Fin n) ℝ))) :
    ∃ g ∈ Matrix.orthogonalGroup (Fin n) ℝ,
      (∀ A : symMat (Fin n),
        (f A : Matrix (Fin n) (Fin n) ℝ) = gᵀ * (A : Matrix (Fin n) (Fin n) ℝ) * g) ∧
      ∀ g' ∈ Matrix.orthogonalGroup (Fin n) ℝ,
        (∀ A : symMat (Fin n),
          (f A : Matrix (Fin n) (Fin n) ℝ) = g'ᵀ * (A : Matrix (Fin n) (Fin n) ℝ) * g') →
          g' = g ∨ g' = -g := by
  obtain ⟨g, hg, hfg⟩ := exists_orthogonal_eq_conj f.toLinearMap hJ hT
  refine ⟨g, hg, hfg, fun g' hg' hfg' => eq_or_eq_neg_of_conj_eq hg hg' fun A => ?_⟩
  rw [← hfg A, ← hfg' A]
  rfl

end CFSG.Monster.Jordan
