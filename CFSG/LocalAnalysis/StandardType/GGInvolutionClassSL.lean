module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionLinearWitness
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.StandardType

open Matrix Module

section Blocks

@[expose] def ggBlockIdx (l k : ℕ) {n : ℕ} (hn : n = l + k + l) (j : Fin n) :
    Fin l ⊕ (Fin k ⊕ Fin l) :=
  if h1 : (j : ℕ) < l then Sum.inl ⟨j, h1⟩ else
    if h2 : (j : ℕ) < l + k then Sum.inr (Sum.inl ⟨j - l, by omega⟩) else
      Sum.inr (Sum.inr ⟨j - (l + k), by have := j.isLt; omega⟩)

variable {l k n : ℕ} (hn : n = l + k + l)

theorem ggBlockIdx_of_lt {j : Fin n} (h : (j : ℕ) < l) :
    ggBlockIdx l k hn j = Sum.inl ⟨j, h⟩ := by
  rw [ggBlockIdx, dite_eq_left h]

theorem ggBlockIdx_of_mid {j : Fin n} (h1 : l ≤ (j : ℕ)) (h2 : (j : ℕ) < l + k) :
    ggBlockIdx l k hn j = Sum.inr (Sum.inl ⟨j - l, by omega⟩) := by
  rw [ggBlockIdx, dite_eq_right (by omega), dite_eq_left h2]

theorem ggBlockIdx_of_ge {j : Fin n} (h : l + k ≤ (j : ℕ)) :
    ggBlockIdx l k hn j = Sum.inr (Sum.inr ⟨j - (l + k), by have := j.isLt; omega⟩) := by
  rw [ggBlockIdx, dite_eq_right (by omega), dite_eq_right (by omega)]

theorem ggBlockIdx_injective : Function.Injective (ggBlockIdx l k hn) := by
  intro a b hab
  have ha := a.isLt
  have hb := b.isLt
  apply Fin.ext
  rcases lt_or_ge (a : ℕ) l with ha1 | ha1 <;> rcases lt_or_ge (b : ℕ) l with hb1 | hb1
  · rw [ggBlockIdx_of_lt hn ha1, ggBlockIdx_of_lt hn hb1] at hab
    simpa using hab
  · rcases lt_or_ge (b : ℕ) (l + k) with hb2 | hb2
    · rw [ggBlockIdx_of_lt hn ha1, ggBlockIdx_of_mid hn hb1 hb2] at hab
      exact absurd hab Sum.inl_ne_inr
    · rw [ggBlockIdx_of_lt hn ha1, ggBlockIdx_of_ge hn hb2] at hab
      exact absurd hab Sum.inl_ne_inr
  · rcases lt_or_ge (a : ℕ) (l + k) with ha2 | ha2
    · rw [ggBlockIdx_of_mid hn ha1 ha2, ggBlockIdx_of_lt hn hb1] at hab
      exact absurd hab.symm Sum.inl_ne_inr
    · rw [ggBlockIdx_of_ge hn ha2, ggBlockIdx_of_lt hn hb1] at hab
      exact absurd hab.symm Sum.inl_ne_inr
  · rcases lt_or_ge (a : ℕ) (l + k) with ha2 | ha2 <;>
      rcases lt_or_ge (b : ℕ) (l + k) with hb2 | hb2
    · rw [ggBlockIdx_of_mid hn ha1 ha2, ggBlockIdx_of_mid hn hb1 hb2] at hab
      have := congrArg Fin.val (Sum.inl_injective (Sum.inr_injective hab))
      simp only at this
      omega
    · rw [ggBlockIdx_of_mid hn ha1 ha2, ggBlockIdx_of_ge hn hb2] at hab
      exact absurd (Sum.inr_injective hab) Sum.inl_ne_inr
    · rw [ggBlockIdx_of_ge hn ha2, ggBlockIdx_of_mid hn hb1 hb2] at hab
      exact absurd (Sum.inr_injective hab).symm Sum.inl_ne_inr
    · rw [ggBlockIdx_of_ge hn ha2, ggBlockIdx_of_ge hn hb2] at hab
      have := congrArg Fin.val (Sum.inr_injective (Sum.inr_injective hab))
      simp only at this
      omega

end Blocks

section SquareZero

variable {F : Type*} [Field F] {n : ℕ}

theorem exists_isUnit_mul_eq_mul_ggInvNil {N : Matrix (Fin n) (Fin n) F} (hN : N * N = 0) :
    ∃ l : ℕ, 2 * l ≤ n ∧ ∃ P : Matrix (Fin n) (Fin n) F, IsUnit P ∧
      N * P = P * ggInvNil n l F := by
  classical
  set φ : (Fin n → F) →ₗ[F] (Fin n → F) := N.mulVecLin with hφ
  have hφφ : ∀ x, φ (φ x) = 0 := fun x => by
    simp only [hφ, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hN, Matrix.zero_mulVec]
  set K := LinearMap.ker φ with hK
  set I := LinearMap.range φ with hI
  have hIK : I ≤ K := by
    rintro _ ⟨x, rfl⟩
    exact hφφ x
  obtain ⟨W, hW⟩ := K.exists_isCompl
  obtain ⟨C₀, hC₀⟩ := I.exists_isCompl
  set C := C₀ ⊓ K with hC
  have hsup : I ⊔ C = K := by
    rw [hC, ← sup_inf_assoc_of_le C₀ hIK, hC₀.sup_eq_top, top_inf_eq]
  have hinf : I ⊓ C = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_left).trans hC₀.inf_eq_bot.le)
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 := Submodule.finrank_add_eq_of_isCompl hW
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq I C
  rw [hsup, hinf, finrank_bot, add_zero] at h3
  rw [Module.finrank_fin_fun] at h1 h2
  rw [← hK, ← hI] at h1
  set l := finrank F I with hl
  set k := finrank F C with hk
  have hn : n = l + k + l := by omega
  have hWl : finrank F W = l := by omega
  let bW := Module.finBasisOfFinrankEq F W hWl
  let bC := Module.finBasisOfFinrankEq F C hk.symm
  let w : Fin l → (Fin n → F) := fun i => (bW i : Fin n → F)
  let v : Fin k → (Fin n → F) := fun j => (bC j : Fin n → F)
  let y : Fin l → (Fin n → F) := fun i => φ (w i)
  have hw : LinearIndependent F w := bW.linearIndependent.map' W.subtype W.ker_subtype
  have hv : LinearIndependent F v := bC.linearIndependent.map' C.subtype C.ker_subtype
  have hspanw : Submodule.span F (Set.range w) ≤ W :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (bW i).2)
  have hspanv : Submodule.span F (Set.range v) ≤ C :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (bC i).2)
  have hspany : Submodule.span F (Set.range y) ≤ I :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact ⟨w i, rfl⟩)
  have hy : LinearIndependent F y := hw.map (hW.disjoint.symm.mono_left hspanw)
  have hvy : LinearIndependent F (Sum.elim v y) :=
    hv.sum_type hy ((disjoint_iff.mpr hinf).symm.mono hspanv hspany)
  have hspanvy : Submodule.span F (Set.range (Sum.elim v y)) ≤ K := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨s | s, rfl⟩
    · exact (inf_le_right : C ≤ K) (bC s).2
    · exact hIK ⟨w s, rfl⟩
  have hg : LinearIndependent F (Sum.elim w (Sum.elim v y)) :=
    hw.sum_type hvy (hW.disjoint.symm.mono hspanw hspanvy)
  let f : Fin n → (Fin n → F) := fun j => Sum.elim w (Sum.elim v y) (ggBlockIdx l k hn j)
  have hf : LinearIndependent F f := hg.comp _ (ggBlockIdx_injective hn)
  let P : Matrix (Fin n) (Fin n) F := Matrix.of fun i j => f j i
  have hP : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp hf
  have hact : ∀ j : Fin n,
      φ (f j) = if h : (j : ℕ) < l then f ⟨j + (n - l), by omega⟩ else 0 := by
    intro j
    by_cases hj1 : (j : ℕ) < l
    · rw [dite_eq_left hj1]
      simp only [f, ggBlockIdx_of_lt hn hj1,
        ggBlockIdx_of_ge hn (j := ⟨j + (n - l), _⟩) (show l + k ≤ j + (n - l) by omega),
        Sum.elim_inl, Sum.elim_inr, y]
      congr 2
      apply Fin.ext
      simp only
      omega
    · rw [dite_eq_right hj1]
      by_cases hj2 : (j : ℕ) < l + k
      · simp only [f, ggBlockIdx_of_mid hn (by omega) hj2, Sum.elim_inr, Sum.elim_inl]
        exact (inf_le_right : C ≤ K) (bC _).2
      · simp only [f, ggBlockIdx_of_ge hn (show l + k ≤ (j : ℕ) by omega), Sum.elim_inr, y]
        exact hφφ _
  refine ⟨l, by omega, P, hP, ?_⟩
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hL : ∑ t, N i t * P t j = φ (f j) i := by
    simp [φ, P, Matrix.mulVec, dotProduct]
  rw [hL, hact j]
  split_ifs with hj
  · rw [Finset.sum_eq_single ⟨j + (n - l), by omega⟩]
    · rw [ggInvNil_apply, ite_eq_left ⟨hj, rfl, by simp only; omega⟩, mul_one]
      rfl
    · intro t _ ht
      rw [ggInvNil_apply, ite_eq_right, mul_zero]
      rintro ⟨-, h, -⟩
      exact ht (Fin.ext h)
    · simp
  · simp only [Pi.zero_apply]
    symm
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [ggInvNil_apply, ite_eq_right (fun h => hj h.1), mul_zero]

end SquareZero

section Involutions

variable {F : Type*} [Field F] [CharP F 2] {n : ℕ}

theorem sub_one_mul_sub_one_eq_zero_charTwo {U : Matrix (Fin n) (Fin n) F} (hU : U * U = 1) :
    (U - 1) * (U - 1) = 0 := by
  have e1 : (U - 1) * (U - 1) = U * U - U - U + 1 := by noncomm_ring
  rw [e1, hU]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination ((1 : Matrix (Fin n) (Fin n) F) i j - U i j) * h2

omit [CharP F 2] in
theorem diagonal_pair_mul_ggInvMatrix_comm {l : ℕ} (hl1 : 1 ≤ l) (hl : 2 * l ≤ n) (β : F) :
    Matrix.diagonal (Pi.mulSingle (⟨0, by omega⟩ : Fin n) β *
        Pi.mulSingle (⟨n - l, by omega⟩ : Fin n) β) * ggInvMatrix n l F =
      ggInvMatrix n l F * Matrix.diagonal (Pi.mulSingle (⟨0, by omega⟩ : Fin n) β *
        Pi.mulSingle (⟨n - l, by omega⟩ : Fin n) β) := by
  refine diagonal_mul_ggInvMatrix_comm _ fun a b hb ha => ?_
  simp only [Pi.mul_apply, Pi.mulSingle_apply, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | ring

end Involutions

theorem ggSLInvolutionClassInput : GGSLInvolutionClassInput := by
  intro F _ _ _ n u hu
  classical
  set U : Matrix (Fin n) (Fin n) F := (u : Matrix (Fin n) (Fin n) F) with hUdef
  have hU2 : U * U = 1 := by
    have h := congrArg (fun x : SpecialLinearGroup (Fin n) F => (x : Matrix (Fin n) (Fin n) F))
      (pow_orderOf_eq_one u)
    simpa [hu, pow_two] using h
  obtain ⟨l, hl, P, hP, hNP⟩ := exists_isUnit_mul_eq_mul_ggInvNil (sub_one_mul_sub_one_eq_zero_charTwo hU2)
  have hUP : U * P = P * ggInvMatrix n l F := by
    have e : U * P = P + (U - 1) * P := by rw [Matrix.sub_mul, Matrix.one_mul]; abel
    rw [e, hNP, ggInvMatrix, Matrix.mul_add, Matrix.mul_one]
  have hl1 : 1 ≤ l := by
    by_contra h0
    obtain rfl : l = 0 := by omega
    have h0' : ggInvNil n 0 F = 0 := by
      ext a b
      simp [ggInvNil_apply]
    rw [h0', Matrix.mul_zero] at hNP
    obtain ⟨Pu, rfl⟩ := hP
    have hN0 : U - 1 = 0 := by
      have := congrArg (· * ((Pu⁻¹ : (Matrix (Fin n) (Fin n) F)ˣ) : Matrix (Fin n) (Fin n) F)) hNP
      simpa [Matrix.mul_assoc] using this
    have hu1 : u = 1 := Subtype.ext (sub_eq_zero.mp hN0)
    rw [hu1, orderOf_one] at hu
    exact absurd hu (by norm_num)
  have hd : P.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det P).mp hP).ne_zero
  obtain ⟨β, hβ⟩ := isSquare_of_charTwo' (P.det)⁻¹
  set e : Fin n → F := Pi.mulSingle (⟨0, by omega⟩ : Fin n) β *
    Pi.mulSingle (⟨n - l, by omega⟩ : Fin n) β with he
  have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨n - l, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp only at this
    omega
  have hprod : ∏ x, e x = β * β := by
    simp only [he, Pi.mul_apply, Finset.prod_mul_distrib, Finset.prod_pi_mulSingle',
      Finset.mem_univ, ite_true]
  set A : Matrix (Fin n) (Fin n) F := P * Matrix.diagonal e with hA
  have hAdet : A.det = 1 := by
    rw [hA, Matrix.det_mul, Matrix.det_diagonal, hprod, ← hβ, mul_inv_cancel₀ hd]
  let a : SpecialLinearGroup (Fin n) F := ⟨A, hAdet⟩
  refine ⟨l, hl1, hl, a, ?_⟩
  have hua : u * a = a * ggInvSL n l F := by
    apply Subtype.ext
    change U * A = A * ggInvMatrix n l F
    rw [hA, ← Matrix.mul_assoc, hUP, Matrix.mul_assoc, Matrix.mul_assoc,
      diagonal_pair_mul_ggInvMatrix_comm hl1 hl β]
  calc u = u * a * a⁻¹ := by group
    _ = a * ggInvSL n l F * a⁻¹ := by rw [hua]

end CFSG.StandardType
