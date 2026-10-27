module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof

open Matrix

variable {F : Type*} [Field F]

theorem linearIndependent_of_sq_mulVec_ne_zero {N : Matrix (Fin 3) (Fin 3) F}
    (hN3 : N ^ 3 = 0) {v : Fin 3 → F} (hv : (N ^ 2) *ᵥ v ≠ 0) :
    LinearIndependent F ![v, N *ᵥ v, (N ^ 2) *ᵥ v] := by
  have hN4 : N ^ 4 = 0 := pow_eq_zero_of_le (by norm_num) hN3
  have e2 : ∀ w : Fin 3 → F, N *ᵥ (N *ᵥ w) = (N ^ 2) *ᵥ w := fun w => by
    rw [Matrix.mulVec_mulVec, sq]
  have e3 : ∀ w : Fin 3 → F, N *ᵥ ((N ^ 2) *ᵥ w) = 0 := fun w => by
    rw [Matrix.mulVec_mulVec, ← pow_succ', hN3, Matrix.zero_mulVec]
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
  have h0 : g 0 = 0 := by
    have h := congrArg (fun w => N *ᵥ (N *ᵥ w)) hg
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, e2, e3, Matrix.mulVec_zero,
      smul_zero, add_zero] at h
    exact (smul_eq_zero.mp h).resolve_right hv
  have h1 : g 1 = 0 := by
    have h := congrArg (fun w => N *ᵥ w) hg
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, e2, e3, Matrix.mulVec_zero,
      smul_zero, add_zero, h0, zero_smul, zero_add] at h
    exact (smul_eq_zero.mp h).resolve_right hv
  have h2 : g 2 = 0 := by
    simp only [h0, h1, zero_smul, zero_add] at hg
    exact (smul_eq_zero.mp hg).resolve_right hv
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem span_eq_top_of_sq_mulVec_ne_zero {N : Matrix (Fin 3) (Fin 3) F}
    (hN3 : N ^ 3 = 0) {v : Fin 3 → F} (hv : (N ^ 2) *ᵥ v ≠ 0) :
    Submodule.span F (Set.range ![v, N *ᵥ v, (N ^ 2) *ᵥ v]) = ⊤ :=
  (linearIndependent_of_sq_mulVec_ne_zero hN3 hv).span_eq_top_of_card_eq_finrank (by simp)

theorem eq_smul_one_of_commute_nilpotent [CharP F 2] {N g : Matrix (Fin 3) (Fin 3) F}
    (hN3 : N ^ 3 = 0) (hN2 : N ^ 2 ≠ 0) (hgN : g * N = N * g) {c : F} (hc : c ≠ 0)
    (hg3 : g ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) F)) :
    ∃ α : F, g = α • (1 : Matrix (Fin 3) (Fin 3) F) := by
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → F, (N ^ 2) *ᵥ v ≠ 0 := by
    by_contra h
    push Not at h
    apply hN2
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  have hspan := span_eq_top_of_sq_mulVec_ne_zero hN3 hv
  have hind := linearIndependent_of_sq_mulVec_ne_zero hN3 hv
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp
    (hspan ▸ Submodule.mem_top : g *ᵥ v ∈ Submodule.span F (Set.range ![v, N *ᵥ v,
      (N ^ 2) *ᵥ v]))
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at ht
  set α := t 0
  set β := t 1
  set γ := t 2
  have h2F : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have e2 : ∀ w : Fin 3 → F, N *ᵥ (N *ᵥ w) = (N ^ 2) *ᵥ w := fun w => by
    rw [Matrix.mulVec_mulVec, sq]
  have e3 : ∀ w : Fin 3 → F, N *ᵥ ((N ^ 2) *ᵥ w) = 0 := fun w => by
    rw [Matrix.mulVec_mulVec, ← pow_succ', hN3, Matrix.zero_mulVec]
  have hcomm : ∀ w : Fin 3 → F, g *ᵥ (N *ᵥ w) = N *ᵥ (g *ᵥ w) := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hgN]
  have hgv : g *ᵥ v = α • v + β • N *ᵥ v + γ • (N ^ 2) *ᵥ v := ht.symm
  have hgNv : g *ᵥ (N *ᵥ v) = α • N *ᵥ v + β • (N ^ 2) *ᵥ v := by
    rw [hcomm, hgv]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, e2, e3, smul_zero, add_zero]
  have hgN2v : g *ᵥ ((N ^ 2) *ᵥ v) = α • (N ^ 2) *ᵥ v := by
    rw [← e2, hcomm, hgNv]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, e2, e3, smul_zero, add_zero]
  have hg2v : (g ^ 2) *ᵥ v = (α * α) • v + (β * β) • (N ^ 2) *ᵥ v := by
    rw [sq, ← Matrix.mulVec_mulVec, hgv]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hgNv, hgN2v, hgv]
    have hab : (α * β + β * α) = 0 := by
      rw [mul_comm β α, ← two_mul, h2F, zero_mul]
    have hag : (α * γ + β * β + γ * α) = β * β := by
      rw [mul_comm γ α]
      linear_combination (α * γ) * h2F
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (N *ᵥ v) i * hab + ((N ^ 2) *ᵥ v) i * hag
  have hg3v : (g ^ 3) *ᵥ v = (α * α * α) • v + (α * α * β) • N *ᵥ v +
      (α * α * γ + α * β * β) • (N ^ 2) *ᵥ v := by
    rw [pow_succ', ← Matrix.mulVec_mulVec, hg2v]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hgv, hgN2v]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hcv : (g ^ 3) *ᵥ v = c • v := by
    rw [hg3, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hcv] at hg3v
  have hcoord := (Fintype.linearIndependent_iff.mp hind)
    ![α * α * α - c, α * α * β, α * α * γ + α * β * β] (by
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [sub_smul, sub_add_eq_add_sub, sub_add_eq_add_sub, sub_eq_zero, ← hg3v])
  have hc0 : α * α * α - c = 0 := hcoord 0
  have hc1 : α * α * β = 0 := hcoord 1
  have hc2 : α * α * γ + α * β * β = 0 := hcoord 2
  have hα : α ≠ 0 := by
    rintro hα0
    rw [hα0] at hc0
    exact hc (by linear_combination -hc0)
  have hβ : β = 0 := by
    have := mul_ne_zero hα hα
    exact (mul_eq_zero.mp hc1).resolve_left this
  have hγ : γ = 0 := by
    rw [hβ] at hc2
    have := mul_ne_zero hα hα
    exact (mul_eq_zero.mp (by simpa using hc2)).resolve_left this
  refine ⟨α, ?_⟩
  have hlin : Matrix.toLin' g = Matrix.toLin' (α • (1 : Matrix (Fin 3) (Fin 3) F)) := by
    refine LinearMap.ext_on_range hspan fun i => ?_
    fin_cases i
    · change g *ᵥ v = (α • (1 : Matrix (Fin 3) (Fin 3) F)) *ᵥ v
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, hgv, hβ, hγ, zero_smul, zero_smul, add_zero,
        add_zero]
    · change g *ᵥ (N *ᵥ v) = (α • (1 : Matrix (Fin 3) (Fin 3) F)) *ᵥ (N *ᵥ v)
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, hgNv, hβ, zero_smul, add_zero]
    · change g *ᵥ ((N ^ 2) *ᵥ v) = (α • (1 : Matrix (Fin 3) (Fin 3) F)) *ᵥ ((N ^ 2) *ᵥ v)
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, hgN2v]
  exact Matrix.toLin'.injective hlin


theorem mem_center_of_commute [CharP F 2] {g u : GL (Fin 3) F}
    (hg3 : g ^ 3 ∈ Subgroup.center (GL (Fin 3) F)) (hgu : g * u = u * g) (hu4 : u ^ 4 = 1)
    (hu2 : u ^ 2 ≠ 1) : g ∈ Subgroup.center (GL (Fin 3) F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := (u : Matrix (Fin 3) (Fin 3) F)
  set A := (g : Matrix (Fin 3) (Fin 3) F)
  set N := U - 1 with hN
  have hcomm1 : Commute U 1 := Commute.one_right U
  have hN4 : N ^ 4 = 0 := by
    have h := sub_pow_char_pow_of_commute (R := Matrix (Fin 3) (Fin 3) F) (p := 2) (n := 2) hcomm1
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, one_pow] at h
    rw [hN, h, ← Units.val_pow_eq_pow_val, hu4, Units.val_one, sub_self]
  have hN2 : N ^ 2 ≠ 0 := by
    have h := sub_pow_char_of_commute (R := Matrix (Fin 3) (Fin 3) F) (p := 2) hcomm1
    rw [one_pow] at h
    rw [hN, h, sub_ne_zero]
    intro h'
    apply hu2
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact h'
  have hN3 : N ^ 3 = 0 := by
    have hnil : IsNilpotent N := ⟨4, hN4⟩
    have hcp : N.charpoly = Polynomial.X ^ 3 := by
      have h := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hnil
      rw [Fintype.card_fin] at h
      exact sub_eq_zero.mp h.eq_zero
    have h := Matrix.aeval_self_charpoly N
    rw [hcp] at h
    simpa using h
  have hgN : A * N = N * A := by
    have hAU : A * U = U * A := by
      rw [← Units.val_mul, ← Units.val_mul, hgu]
    rw [hN, mul_sub, sub_mul, hAU, mul_one, one_mul]
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg3 ⊢
  obtain ⟨c, hc⟩ := hg3
  have hA3 : A ^ 3 = (c : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [← Units.val_pow_eq_pow_val, ← hc, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.smul_one_eq_diagonal]
    rfl
  obtain ⟨α, hα⟩ := eq_smul_one_of_commute_nilpotent hN3 hN2 hgN (Units.ne_zero c) hA3
  have hα0 : α ≠ 0 := by
    rintro rfl
    have hdet := (Matrix.GeneralLinearGroup.det g).ne_zero
    rw [Matrix.GeneralLinearGroup.val_det_apply] at hdet
    change A.det ≠ 0 at hdet
    rw [hα, zero_smul, Matrix.det_zero] at hdet
    exact hdet rfl
  refine ⟨Units.mk0 α hα0, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
  change Matrix.scalar (Fin 3) α = A
  rw [hα, Matrix.smul_one_eq_diagonal]
  rfl

end CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof
