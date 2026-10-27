module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterForkProofBCD
import TauCeti.LinearAlgebra.RootSystem.FiniteType.ForkedDoubleEdge
import TauCeti.LinearAlgebra.RootSystem.FiniteType.AffineD

public section

namespace CFSG.StandardType

section Aff

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] {C : Matrix Λ Λ ℤ} {n : ℕ}

theorem not_isFiniteType_ggAttachCartan_shapeB (e : Fin (n + 3) ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.B (n + 3) i j) :
    ¬ TauCeti.IsFiniteType (ggAttachCartan C (e ⟨1, by omega⟩)) := by
  intro h
  refine TauCeti.not_isFiniteType_affineBCartanMatrix n ?_
  convert h.submatrix (Option.map_injective e.injective) using 1
  ext v w
  rcases v with _ | i <;> rcases w with _ | j
  · simp
  · simp [Fin.ext_iff]
  · simp [Fin.ext_iff]
  · simp [hC]

theorem not_isFiniteType_ggAttachCartan_shapeC (e : Fin (n + 3) ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.C (n + 3) i j) :
    ¬ TauCeti.IsFiniteType (ggAttachCartan C (e ⟨1, by omega⟩)) := by
  intro h
  refine TauCeti.not_isFiniteType_affineBCartanMatrix_transpose n ?_
  rw [TauCeti.affineBCartanMatrix_transpose]
  convert h.submatrix (Option.map_injective e.injective) using 1
  ext v w
  rcases v with _ | i <;> rcases w with _ | j
  · simp
  · simp [Fin.ext_iff]
  · simp [Fin.ext_iff]
  · simp [hC]

private def ggDoubleForkEmb {k : ℕ} (e : Fin (k + 2 + 3) ≃ Λ) :
    TauCeti.DoubleForkIndex k → Option Λ
  | .inl i => if (i : ℕ) = 0 then none else some (e ⟨0, by omega⟩)
  | .inr (.inl i) => some (e ⟨i.val + 1, by omega⟩)
  | .inr (.inr i) => some (e ⟨k + 3 + i.val, by omega⟩)

omit [DecidableEq Λ] [Fintype Λ] in
private theorem ggDoubleForkEmb_injective {k : ℕ} (e : Fin (k + 2 + 3) ≃ Λ) :
    Function.Injective (ggDoubleForkEmb e) := by
  rintro (⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, hi⟩) (⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, hj⟩) hij <;>
    simp only [ggDoubleForkEmb, EmbeddingLike.apply_eq_iff_eq, Option.some.injEq,
      Fin.mk.injEq] at hij <;>
    (try split_ifs at hij) <;> (try simp_all) <;> omega

theorem not_isFiniteType_ggAttachCartan_shapeD (e : Fin (n + 3) ≃ Λ) (hn : 1 ≤ n)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.D (n + 3) i j) :
    ¬ TauCeti.IsFiniteType (ggAttachCartan C (e ⟨1, by omega⟩)) := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · obtain rfl : n = 1 := by omega
    intro h
    refine TauCeti.not_isFiniteType_affineD₄ ?_
    have hf : Function.Injective (![some (e ⟨1, by omega⟩), none, some (e ⟨0, by omega⟩),
        some (e ⟨2, by omega⟩), some (e ⟨3, by omega⟩)] : Fin 5 → Option Λ) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    convert h.submatrix hf using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hC, CartanMatrix.D]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have hD : ∀ (a b : ℕ) (ha : a < k + 2 + 3) (hb : b < k + 2 + 3),
        C (e ⟨a, ha⟩) (e ⟨b, hb⟩) = if a = b then 2 else if (a + 1 = b ∧ b ≤ k + 2) ∨
          (b + 1 = a ∧ a ≤ k + 2) ∨ (a = k + 2 ∧ k + 3 ≤ b) ∨ (b = k + 2 ∧ k + 3 ≤ a) then -1
          else 0 := by
      intro a b ha hb
      rw [hC]
      simp only [CartanMatrix.D, Matrix.of_apply, Fin.mk.injEq]
      split_ifs <;> omega
    intro h
    refine TauCeti.not_isFiniteType_doubleForkCartanMatrix k ?_
    convert h.submatrix (ggDoubleForkEmb_injective e) using 1
    ext x y
    rcases x with ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, hi⟩ <;> rcases y with ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, hj⟩ <;>
      simp only [ggDoubleForkEmb, Matrix.submatrix_apply, TauCeti.doubleForkCartanMatrix_inl_inl,
        TauCeti.doubleForkCartanMatrix_inl_inr_inl, TauCeti.doubleForkCartanMatrix_inl_inr_inr,
        TauCeti.doubleForkCartanMatrix_inr_inl_inl, TauCeti.doubleForkCartanMatrix_inr_inl_inr_inl,
        TauCeti.doubleForkCartanMatrix_inr_inl_inr_inr, TauCeti.doubleForkCartanMatrix_inr_inr_inl,
        TauCeti.doubleForkCartanMatrix_inr_inr_inr_inl,
        TauCeti.doubleForkCartanMatrix_inr_inr_inr_inr, Fin.mk.injEq] <;>
      (try split_ifs) <;>
      simp only [ggAttachCartan_none_none, ggAttachCartan_none_some, ggAttachCartan_some_none,
        ggAttachCartan_some_some, hD, EmbeddingLike.apply_eq_iff_eq, Fin.mk.injEq] <;>
      (try split_ifs) <;>
      (try simp only [false_and, false_or, or_false, not_false_eq_true] at *) <;>
      omega

end Aff

theorem eq_of_forkShapeBCD {Λ : Type*} {C : Matrix Λ Λ ℤ} {b c : Λ} {n : ℕ}
    {e : Fin (n + 3) ≃ Λ} (he0 : e 0 = b) (hbc : C b c = -1)
    (hS : (∀ i j, C (e i) (e j) = CartanMatrix.B (n + 3) i j) ∨
      (∀ i j, C (e i) (e j) = CartanMatrix.C (n + 3) i j) ∨
      (1 ≤ n ∧ ∀ i j, C (e i) (e j) = CartanMatrix.D (n + 3) i j)) :
    c = e ⟨1, by omega⟩ := by
  have he0' : e ⟨0, by omega⟩ = b := he0
  have hk := (e.symm c).isLt
  have hval : ((e.symm c) : ℕ) = 1 := by
    rcases hS with hBC | hBC | ⟨hn, hBC⟩
    · have h1 := hBC ⟨0, by omega⟩ (e.symm c)
      rw [he0', e.apply_symm_apply, hbc] at h1
      simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff] at h1
      split_ifs at h1 <;> first | omega | simp_all
    · have h1 := hBC ⟨0, by omega⟩ (e.symm c)
      rw [he0', e.apply_symm_apply, hbc] at h1
      simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff] at h1
      split_ifs at h1 <;> first | omega | simp_all
    · have h1 := hBC ⟨0, by omega⟩ (e.symm c)
      rw [he0', e.apply_symm_apply, hbc] at h1
      simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff] at h1
      split_ifs at h1 <;> first | omega | simp_all
  rw [← e.apply_symm_apply c]
  exact congrArg e (Fin.ext hval)

theorem not_exists_weyl_ggAttachCartan_shapeBCD_c {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {C : Matrix Λ Λ ℤ} {b c : Λ} (hbc : C b c = -1) (hS : GGForkShapeBCD C b) :
    ¬ ∃ M' : CoxeterMatrix (Option Λ), GGIsWeylMatrix M' ∧
      GGIntCartan M' (ggAttachCartan C c) := by
  rintro ⟨M', hM', hC'⟩
  have hFT := isFiniteType_of_ggIsWeylMatrixFixed (hM' : GGIsWeylMatrixFixed M') hC'
  obtain ⟨n, e, he0, hBC⟩ := hS
  rw [eq_of_forkShapeBCD he0 hbc hBC] at hFT
  rcases hBC with hBC | hBC | ⟨hn, hBC⟩
  · exact not_isFiniteType_ggAttachCartan_shapeB e hBC hFT
  · exact not_isFiniteType_ggAttachCartan_shapeC e hBC hFT
  · exact not_isFiniteType_ggAttachCartan_shapeD e hn hBC hFT

end CFSG.StandardType
