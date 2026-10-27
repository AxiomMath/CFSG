module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.LinearAlgebra.Matrix.CharP

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item84KFacts4

open Matrix Module
open scoped MatrixGroups

variable {K : Type} [Field K]

section Nilpotent

theorem pow_three_eq_zero_of_isNilpotent {N : Matrix (Fin 3) (Fin 3) K} (hN : IsNilpotent N) :
    N ^ 3 = 0 := by
  have hcp := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN
  have hcp' : N.charpoly = Polynomial.X ^ 3 := by
    have := hcp.eq_zero
    rwa [sub_eq_zero, Fintype.card_fin] at this
  have h := Matrix.aeval_self_charpoly N
  rw [hcp'] at h
  simpa using h

variable [CharP K 2]

theorem eq_smul_one_of_commute_regular {N W : Matrix (Fin 3) (Fin 3) K} (hN3 : N ^ 3 = 0)
    (hN2 : N ^ 2 ≠ 0) (hWN : W * N = N * W) (hW : IsUnit W) {l : K} (hW3 : W ^ 3 = l • 1) :
    ∃ a : K, W = a • 1 := by
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → K, N *ᵥ (N *ᵥ v) ≠ 0 := by
    by_contra h
    push Not at h
    apply hN2
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    rw [mulVec_mulVec, ← sq, mulVec_single_one] at this
    simpa using this
  set u1 := N *ᵥ v with hu1
  set u0 := N *ᵥ u1 with hu0
  have hNu0 : N *ᵥ u0 = 0 := by
    rw [hu0, hu1, mulVec_mulVec, mulVec_mulVec, ← pow_three', hN3, zero_mulVec]
  have hWc : ∀ y : Fin 3 → K, W *ᵥ (N *ᵥ y) = N *ᵥ (W *ᵥ y) := fun y => by
    rw [mulVec_mulVec, mulVec_mulVec, hWN]
  have hsm : ∀ (c : K) {y : Fin 3 → K}, y ≠ 0 → c • y = 0 → c = 0 :=
    fun c y hy h => (smul_eq_zero.mp h).resolve_right hy
  have hli : LinearIndependent K ![u0, u1, v] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hg
    have h1 := congrArg (fun y => N *ᵥ (N *ᵥ y)) hg
    simp only [mulVec_add, mulVec_smul, hNu0, ← hu1, ← hu0, mulVec_zero, smul_zero,
      zero_add] at h1
    have hg2 : g 2 = 0 := hsm _ hv h1
    have h2 := congrArg (fun y => N *ᵥ y) hg
    simp only [mulVec_add, mulVec_smul, hNu0, ← hu0, mulVec_zero, smul_zero, zero_add,
      hg2, zero_smul, add_zero] at h2
    have hg1 : g 1 = 0 := hsm _ hv h2
    rw [hg1, hg2, zero_smul, zero_smul, add_zero, add_zero] at hg
    have hg0 : g 0 = 0 := hsm _ hv hg
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
  have hspan := hli.span_eq_top_of_card_eq_finrank (by simp)
  have hexp : ∀ y : Fin 3 → K, ∃ d : Fin 3 → K, d 0 • u0 + d 1 • u1 + d 2 • v = y := by
    intro y
    have hy : y ∈ Submodule.span K (Set.range ![u0, u1, v]) := by rw [hspan]; trivial
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy
    refine ⟨d, ?_⟩
    rw [← hd, Fin.sum_univ_three]
    rfl
  obtain ⟨c, hc⟩ := hexp (W *ᵥ v)
  have hWu1 : W *ᵥ u1 = c 1 • u0 + c 2 • u1 := by
    rw [hu1, hWc, ← hc]
    simp only [mulVec_add, mulVec_smul, hNu0, ← hu1, ← hu0, smul_zero, zero_add]
  have hWu0 : W *ᵥ u0 = c 2 • u0 := by
    rw [hu0, hWc, hWu1]
    simp only [mulVec_add, mulVec_smul, hNu0, ← hu0, smul_zero, zero_add]
  have hW3v : ∀ y : Fin 3 → K, W *ᵥ (W *ᵥ (W *ᵥ y)) = l • y := fun y => by
    rw [mulVec_mulVec, mulVec_mulVec, ← pow_three', hW3, smul_mulVec, one_mulVec]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hl : l = c 2 * c 2 * c 2 := by
    have h := hW3v u0
    simp only [hWu0, mulVec_smul, smul_smul] at h
    have h' : (c 2 * c 2 * c 2 - l) • u0 = 0 := by rw [sub_smul, sub_eq_zero, ← h, mul_assoc]
    linear_combination -(hsm _ hv h')
  have hc2 : c 2 ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hWu0
    exact hv ((Matrix.mulVec_injective_iff_isUnit.mpr hW) (hWu0.trans (mulVec_zero W).symm))
  have hc1 : c 1 = 0 := by
    have h := hW3v u1
    simp only [hWu1, hWu0, mulVec_add, mulVec_smul, smul_add, smul_smul, hl] at h
    have h' : (c 1 * (c 2 * c 2)) • u0 = 0 := by
      rw [← sub_eq_zero.mpr h]
      funext k
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      grind
    have := hsm _ hv h'
    rcases mul_eq_zero.mp this with h1 | h1
    · exact h1
    · exact absurd (mul_self_eq_zero.mp h1) hc2
  have hWv : W *ᵥ v = c 0 • u0 + c 2 • v := by rw [← hc, hc1, zero_smul, add_zero]
  have hc0 : c 0 = 0 := by
    have h := hW3v v
    simp only [hWv, hWu0, mulVec_add, mulVec_smul, smul_add, smul_smul, hl] at h
    have h' : (c 0 * (c 2 * c 2)) • u0 = 0 := by
      rw [← sub_eq_zero.mpr h]
      funext k
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      grind
    have := hsm _ hv h'
    rcases mul_eq_zero.mp this with h1 | h1
    · exact h1
    · exact absurd (mul_self_eq_zero.mp h1) hc2
  refine ⟨c 2, ?_⟩
  have hall : ∀ y : Fin 3 → K, W *ᵥ y = c 2 • y := by
    intro y
    obtain ⟨d, rfl⟩ := hexp y
    rw [hc1] at hWu1
    rw [hc0, zero_smul, zero_add] at hWv
    rw [zero_smul, zero_add] at hWu1
    simp only [mulVec_add, mulVec_smul, hWu0, hWu1, hWv, smul_add, smul_smul, mul_comm]
  ext i j
  have := congrFun (hall (Pi.single j 1)) i
  rw [mulVec_single_one] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

end Nilpotent

section PGL

variable [Finite K] [CharP K 2]

theorem exists_pow_two_pow_eq (c : K) (e : ℕ) : ∃ μ : K, μ ^ 2 ^ e = c := by
  induction e generalizing c with
  | zero => exact ⟨c, by rw [pow_zero, pow_one]⟩
  | succ e ih =>
    obtain ⟨μ, hμ⟩ := ih c
    obtain ⟨r, hr⟩ := isSquare_of_charTwo' μ
    exact ⟨r, by rw [pow_succ', pow_mul, sq, ← hr, hμ]⟩

theorem exists_unipotent_lift {X : GL (Fin 3) K} {e : ℕ}
    (he : ProjGenLinGroup.mk X ^ 2 ^ e = 1) :
    ∃ U : GL (Fin 3) K, ProjGenLinGroup.mk U = ProjGenLinGroup.mk X ∧ U ^ 2 ^ e = 1 := by
  have h1 : ProjGenLinGroup.mk (X ^ 2 ^ e) = 1 := by rw [map_pow, he]
  rw [ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
  obtain ⟨ν, hν⟩ := h1
  obtain ⟨μ, hμ⟩ := exists_pow_two_pow_eq (ν : K) e
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ two_ne_zero)] at hμ
    exact ν.ne_zero hμ.symm
  set μu : Kˣ := Units.mk0 μ hμ0 with hμu
  have hμν : μu ^ 2 ^ e = ν := Units.ext (by rw [Units.val_pow_eq_pow_val, hμu, Units.val_mk0, hμ])
  refine ⟨X * GeneralLinearGroup.scalar (Fin 3) μu⁻¹, ?_, ?_⟩
  · rw [map_mul, ProjGenLinGroup.mk_scalar, mul_one]
  · have hc : Commute X (GeneralLinearGroup.scalar (Fin 3) μu⁻¹) := by
      have hz : GeneralLinearGroup.scalar (Fin 3) μu⁻¹ ∈ Subgroup.center (GL (Fin 3) K) := by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact ⟨_, rfl⟩
      exact Subgroup.mem_center_iff.mp hz X
    rw [hc.mul_pow, ← hν, ← map_pow, ← map_mul, inv_pow, hμν, mul_inv_cancel, map_one]

theorem sq_eq_one_of_commute_orderThree {x w : PGL(3, K)} (hx : ∃ e : ℕ, x ^ 2 ^ e = 1)
    (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) (hxw : x * w = w * x) : x ^ 2 = 1 := by
  obtain ⟨e, he⟩ := hx
  obtain ⟨X, rfl⟩ := ProjGenLinGroup.mk_surjective x
  obtain ⟨W, rfl⟩ := ProjGenLinGroup.mk_surjective w
  obtain ⟨U, hUX, hU⟩ := exists_unipotent_lift he
  rw [← hUX] at hxw ⊢
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Matrix (Fin 3) (Fin 3) K := (U : Matrix (Fin 3) (Fin 3) K) - 1 with hNdef
  have hUN : (U : Matrix (Fin 3) (Fin 3) K) = N + 1 := by rw [hNdef, sub_add_cancel]
  have hnil : IsNilpotent N := by
    refine ⟨2 ^ e, ?_⟩
    rw [hNdef, sub_pow_char_pow_of_commute 2 e (Commute.one_right _), ← Units.val_pow_eq_pow_val,
      hU, Units.val_one, one_pow, sub_self]
  have hN3 := pow_three_eq_zero_of_isNilpotent hnil
  by_cases hN2 : N ^ 2 = 0
  ·
    have hU2 : U ^ 2 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hUN, Units.val_one, sq, add_mul, mul_add, mul_add, ← sq, hN2,
        Matrix.mul_one, Matrix.one_mul, zero_add, ← add_assoc, CharTwo.add_self_eq_zero,
        zero_add, Matrix.mul_one]
    rw [← map_pow, hU2, map_one]
  · exfalso
    apply hw1
    have h1 : ProjGenLinGroup.mk (U * W) = ProjGenLinGroup.mk (W * U) := by
      rw [map_mul, map_mul, hxw]
    obtain ⟨c, hc⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h1
    have hcm : (U : Matrix (Fin 3) (Fin 3) K) * W * ((c : K) • 1) = W * U := by
      have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hc
      simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.smul_eq_diagonal_mul,
        Matrix.scalar_apply] using this
    have htr : (U : Matrix (Fin 3) (Fin 3) K).trace = 1 := by
      rw [hUN, Matrix.trace_add, (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero,
        Matrix.trace_one, Fintype.card_fin, zero_add]
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      push_cast
      linear_combination h2
    have hc1 : (c : K) = 1 := by
      have hWinv : ((W⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * W = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have hWinv' : (W : Matrix (Fin 3) (Fin 3) K) * ((W⁻¹ : GL (Fin 3) K) : Matrix _ _ K) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hcm' : (c : K) • ((U : Matrix (Fin 3) (Fin 3) K) * W) = W * U := by
        rw [← hcm, Matrix.mul_smul, Matrix.mul_one]
      have h3 : (c : K) • (((W⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((U : Matrix (Fin 3) (Fin 3) K) * W)) = U := by
        rw [← Matrix.mul_smul, hcm', ← Matrix.mul_assoc, hWinv, Matrix.one_mul]
      have h4 := congrArg Matrix.trace h3
      rw [Matrix.trace_smul, Matrix.trace_mul_comm, Matrix.mul_assoc, hWinv', Matrix.mul_one, htr,
        smul_eq_mul, mul_one] at h4
      exact h4
    have hUW : (U : Matrix (Fin 3) (Fin 3) K) * W = W * U := by
      rw [← hcm, hc1, one_smul, Matrix.mul_one]
    have hWN : (W : Matrix (Fin 3) (Fin 3) K) * N = N * W := by
      rw [hNdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hUW]
    have hW3 : ProjGenLinGroup.mk (W ^ 3) = 1 := by rw [map_pow, hw3]
    rw [ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hW3
    obtain ⟨l, hl⟩ := hW3
    have hW3' : (W : Matrix (Fin 3) (Fin 3) K) ^ 3 = (l : K) • 1 := by
      rw [← Units.val_pow_eq_pow_val, ← hl, Matrix.GeneralLinearGroup.coe_scalar]
      ext i j
      simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
    obtain ⟨a, ha⟩ := eq_smul_one_of_commute_regular hN3 hN2 hWN W.isUnit hW3'
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ha
      have := W.isUnit
      rw [ha] at this
      exact not_isUnit_zero this
    rw [ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨Units.mk0 a ha0, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, ha, Units.val_mk0]
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]

end PGL

end CFSG.RankThree.PartTwo.Sec8.Item84KFacts4
