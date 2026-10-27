module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxSL2

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TwoConjL2

open Matrix CFSG.RankThree.PartOne.CTP

section Traces

variable {F : Type} [Field F]

theorem trace_root [CharP F 2] (x μ : F) :
    Matrix.trace ((u2 x * l2 (μ * x) : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = μ * x ^ 2 := by
  rw [trace_u2_mul_l2]
  ring

theorem trace_root_pair [CharP F 2] (x y μ : F) :
    Matrix.trace ((u2 x * l2 (μ * x) * (u2 y * l2 (μ * y)) : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = μ * x ^ 2 + μ * y ^ 2 + μ ^ 2 * x ^ 2 * y ^ 2 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, u2_coe, l2_coe]
  rw [Matrix.trace_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (1 + μ * x * y) * (CharTwo.two_eq_zero : (2 : F) = 0)

theorem normalizedTrace_root_pair [CharP F 2] {x y μ : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hμ : μ ≠ 0) :
    Matrix.trace ((u2 x * l2 (μ * x) * (u2 y * l2 (μ * y)) : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) /
      (Matrix.trace ((u2 x * l2 (μ * x) : SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) *
        Matrix.trace ((u2 y * l2 (μ * y) : SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F)) =
      1 + (μ * x ^ 2)⁻¹ * (1 + (x / y) ^ 2) := by
  rw [trace_root_pair, trace_root, trace_root]
  field_simp
  ring

private theorem coe_mul_self [CharP F 2] (g : SpecialLinearGroup (Fin 2) F) :
    (g : Matrix (Fin 2) (Fin 2) F) * g =
      Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) • (g : Matrix (Fin 2) (Fin 2) F) + 1 := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) F).det = 1 := g.2
  rw [Matrix.det_fin_two] at hdet
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two]
  all_goals first | ring1 | linear_combination (-1 : F) * hdet - h2

private theorem coe_pow_three [CharP F 2] (g : SpecialLinearGroup (Fin 2) F) :
    (g : Matrix (Fin 2) (Fin 2) F) ^ 3 =
      (Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) ^ 2 + 1) • (g : Matrix (Fin 2) (Fin 2) F) +
        Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have hG2 := coe_mul_self g
  set G := (g : Matrix (Fin 2) (Fin 2) F)
  set t := Matrix.trace G
  have e : G ^ 3 = (G * G) * G := by rw [pow_succ, pow_two]
  rw [e, hG2, add_mul, smul_mul_assoc, one_mul, hG2]
  module

private theorem coe_pow_five [CharP F 2] (g : SpecialLinearGroup (Fin 2) F) :
    (g : Matrix (Fin 2) (Fin 2) F) ^ 5 =
      (Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) ^ 4 +
          Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) ^ 2 + 1) • (g : Matrix (Fin 2) (Fin 2) F) +
        Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) ^ 3 • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have hG2 := coe_mul_self g
  have hG3 := coe_pow_three g
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  set G := (g : Matrix (Fin 2) (Fin 2) F)
  set t := Matrix.trace G
  have hG4 : G ^ 4 = t ^ 3 • G + (t ^ 2 + 1) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [pow_succ, hG3, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, hG2]
    match_scalars <;> first | ring1 | linear_combination t * h2
  rw [pow_succ, hG4, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, hG2]
  match_scalars <;> first | ring1 | linear_combination t * h2

private theorem eq_one_of_smul_add_eq_zero [CharP F 2] {g : SpecialLinearGroup (Fin 2) F}
    {a b : F} (ha : a ≠ 0)
    (h : a • (g : Matrix (Fin 2) (Fin 2) F) + b • (1 : Matrix (Fin 2) (Fin 2) F) = 0) :
    g = 1 := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) F).det = 1 := g.2
  rw [Matrix.det_fin_two] at hdet
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp at e00 e01 e10 e11
  have g01 : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by simpa [ha] using e01
  have g10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by simpa [ha] using e10
  have h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = (g : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    have : a * ((g : Matrix (Fin 2) (Fin 2) F) 0 0 - (g : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
      linear_combination e00 - e11
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha)
  have hl : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have h' : ((g : Matrix (Fin 2) (Fin 2) F) 0 0 + 1) *
        ((g : Matrix (Fin 2) (Fin 2) F) 0 0 + 1) = 0 := by
      rw [g01, g10, ← h00] at hdet
      linear_combination hdet + h2 * (g : Matrix (Fin 2) (Fin 2) F) 0 0 + h2
    have := mul_self_eq_zero.mp h'
    linear_combination this - h2
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g01, g10, hl, ← h00]

theorem trace_eq_zero_of_pow_two_eq_one [CharP F 2] {g : SpecialLinearGroup (Fin 2) F}
    (h : g ^ 2 = 1) : Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) = 0 := by
  have h1 : (g : Matrix (Fin 2) (Fin 2) F) * g = 1 := by
    have := congrArg (fun z : SpecialLinearGroup (Fin 2) F => (z : Matrix (Fin 2) (Fin 2) F)) h
    simpa [pow_two] using this
  rw [coe_mul_self] at h1
  have e00 := congrFun (congrFun h1 0) 0
  have e11 := congrFun (congrFun h1 1) 1
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    add_eq_right] at e00 e11
  have : Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) *
      Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) = 0 := by
    rw [Matrix.trace_fin_two] at e00 e11 ⊢
    linear_combination e00 + e11
  exact mul_self_eq_zero.mp this

theorem trace_eq_one_of_pow_three_eq_one [CharP F 2] {g : SpecialLinearGroup (Fin 2) F}
    (h : g ^ 3 = 1) (hg : g ≠ 1) : Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) = 1 := by
  have h3 : (g : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1 := by
    have := congrArg (fun z : SpecialLinearGroup (Fin 2) F => (z : Matrix (Fin 2) (Fin 2) F)) h
    simpa using this
  rw [coe_pow_three] at h3
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  set G := (g : Matrix (Fin 2) (Fin 2) F)
  set t := Matrix.trace G
  by_cases ht : t ^ 2 + 1 = 0
  · have h' : (t + 1) * (t + 1) = 0 := by linear_combination ht + t * h2
    have := mul_self_eq_zero.mp h'
    linear_combination this - h2
  · exfalso
    apply hg
    refine eq_one_of_smul_add_eq_zero ht (b := t - 1) ?_
    calc (t ^ 2 + 1) • G + (t - 1) • (1 : Matrix (Fin 2) (Fin 2) F)
        = ((t ^ 2 + 1) • G + t • (1 : Matrix (Fin 2) (Fin 2) F)) - 1 := by module
      _ = 0 := by rw [h3, sub_self]

theorem trace_sq_add_trace_add_one_of_pow_five_eq_one [CharP F 2]
    {g : SpecialLinearGroup (Fin 2) F} (h : g ^ 5 = 1) (hg : g ≠ 1) :
    Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) ^ 2 + Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) +
      1 = 0 := by
  have h5 : (g : Matrix (Fin 2) (Fin 2) F) ^ 5 = 1 := by
    have := congrArg (fun z : SpecialLinearGroup (Fin 2) F => (z : Matrix (Fin 2) (Fin 2) F)) h
    simpa using this
  rw [coe_pow_five] at h5
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  set G := (g : Matrix (Fin 2) (Fin 2) F)
  set t := Matrix.trace G
  by_cases ht : t ^ 4 + t ^ 2 + 1 = 0
  · have h' : (t ^ 2 + t + 1) * (t ^ 2 + t + 1) = 0 := by
      linear_combination ht + (t ^ 3 + t ^ 2 + t) * h2
    exact mul_self_eq_zero.mp h'
  · exfalso
    apply hg
    refine eq_one_of_smul_add_eq_zero ht (b := t ^ 3 - 1) ?_
    calc (t ^ 4 + t ^ 2 + 1) • G + (t ^ 3 - 1) • (1 : Matrix (Fin 2) (Fin 2) F)
        = ((t ^ 4 + t ^ 2 + 1) • G + t ^ 3 • (1 : Matrix (Fin 2) (Fin 2) F)) - 1 := by module
      _ = 0 := by rw [h5, sub_self]

end Traces

theorem alternatingFive_pow_cases (g : alternatingGroup (Fin 5)) :
    g ^ 2 = 1 ∨ g ^ 3 = 1 ∨ g ^ 5 = 1 := by
  revert g
  decide +kernel

section Fields

variable {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] def frobFixed (F : Type) [Field F] [CharP F 2] (n : ℕ) : Subfield F :=
  { carrier := {z | z ^ (2 ^ n) = z}
    zero_mem' := by simp
    one_mem' := by simp
    add_mem' := by
      intro a b ha hb
      simp only [Set.mem_setOf_eq] at *
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [add_pow_char_pow, ha, hb]
    mul_mem' := by
      intro a b ha hb
      simp only [Set.mem_setOf_eq] at *
      rw [mul_pow, ha, hb]
    neg_mem' := by
      intro a ha
      simp only [Set.mem_setOf_eq] at *
      rw [CharTwo.neg_eq]
      exact ha
    inv_mem' := by
      intro a ha
      simp only [Set.mem_setOf_eq] at *
      rw [inv_pow, ha] }

theorem mem_frobFixed {n : ℕ} {z : F} : z ∈ frobFixed F n ↔ z ^ (2 ^ n) = z := Iff.rfl

theorem ne_zero_and_ne_one_of_forall_subfield {ν x y : F}
    (hν : ∀ k : Subfield F, ν ∈ k → k = ⊤) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    ν ≠ 0 ∧ ν ≠ 1 := by
  have key : (ν = 0 ∨ ν = 1) → False := by
    intro hν01
    have hmem : ν ∈ frobFixed F 1 := by
      rw [mem_frobFixed]
      rcases hν01 with rfl | rfl <;> simp
    have htop := hν _ hmem
    have hx' : x ∈ frobFixed F 1 := by rw [htop]; exact Subfield.mem_top x
    have hy' : y ∈ frobFixed F 1 := by rw [htop]; exact Subfield.mem_top y
    rw [mem_frobFixed] at hx' hy'
    simp only [pow_one] at hx' hy'
    have hx1 : x = 1 := by
      have : x * (x - 1) = 0 := by linear_combination hx'
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hx
      · exact sub_eq_zero.mp h
    have hy1 : y = 1 := by
      have : y * (y - 1) = 0 := by linear_combination hy'
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hy
      · exact sub_eq_zero.mp h
    exact hxy (hx1.trans hy1.symm)
  exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩

theorem card_le_four_of_forall_subfield {ν : F} (hν : ∀ k : Subfield F, ν ∈ k → k = ⊤)
    (h : ν ^ 2 + ν + 1 = 0) : Nat.card F ≤ 4 := by
  have hmem : ν ∈ frobFixed F 2 := by
    rw [mem_frobFixed]
    linear_combination (ν ^ 2 - ν) * h
  have htop := hν _ hmem
  have hall : ∀ z : F, z ^ 4 = z := by
    intro z
    have hz : z ∈ frobFixed F 2 := by rw [htop]; exact Subfield.mem_top z
    simpa [mem_frobFixed] using hz
  haveI : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  have hdeg : (Polynomial.X ^ 4 - Polynomial.X : Polynomial F).natDegree = 4 := by
    compute_degree!
  have hne : (Polynomial.X ^ 4 - Polynomial.X : Polynomial F) ≠ 0 := by
    intro h0
    rw [h0] at hdeg
    simp at hdeg
  have hsub : (Finset.univ : Finset F).val ⊆
      (Polynomial.X ^ 4 - Polynomial.X : Polynomial F).roots := by
    intro z _
    rw [Polynomial.mem_roots hne]
    simp [Polynomial.IsRoot, hall z]
  have := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hdeg] at this
  simpa using this

theorem one_add_div_sq_ne_zero {x y : F} (hy : y ≠ 0) (hxy : x ≠ y) : 1 + (x / y) ^ 2 ≠ 0 := by
  intro h
  apply hxy
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h1 : (x / y + 1) * (x / y + 1) = 0 := by linear_combination h + (x / y) * h2
  have h' := mul_self_eq_zero.mp h1
  have h3 : x / y = 1 := by linear_combination h' - h2
  rwa [div_eq_one_iff_eq hy] at h3

omit [CharP F 2] in
theorem card_sl2 : Nat.card (SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have h := Matrix.card_SL_field (𝔽 := F) 2
  rw [Fin.prod_univ_two] at h
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
  rw [h, Nat.card_eq_fintype_card (α := F)]
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  apply Nat.div_eq_of_eq_mul_left (by omega)
  have e1 : Fintype.card F ^ 2 - Fintype.card F = Fintype.card F * (Fintype.card F - 1) := by
    rw [Nat.mul_sub_one, sq]
  rw [e1]
  ring

end Fields

end CFSG.LocalAnalysis.WeakClosure81.TwoConjL2
