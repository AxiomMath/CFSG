module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterForkProofBCD

public section

namespace CFSG.StandardType

theorem ggIntCartan_C (n : ℕ) : GGIntCartan (CoxeterMatrix.B n) (CartanMatrix.C n) := by
  refine ⟨fun i => by simp, fun i j hij => ?_⟩
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  have hi := i.isLt
  have hj := j.isLt
  simp only [CoxeterMatrix.B, CartanMatrix.C, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

section Ext

variable {Λ : Type*} [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {n : ℕ}

theorem ggAttachCartan_shapeB (e : Fin (n + 3) ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.B (n + 3) i j) :
    ggAttachCartan C (e 0) =
      Matrix.reindex (ggFirstEquiv e) (ggFirstEquiv e) (CartanMatrix.B (n + 4)) := by
  refine ggMatrix_eq_reindex _ fun i j => ?_
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simp [CartanMatrix.B]
    | succ j =>
      have hj := j.isLt
      simp only [ggFirstEquiv_zero, ggFirstEquiv_succ, ggAttachCartan_none_some,
        EmbeddingLike.apply_eq_iff_eq, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff,
        Fin.val_zero, Fin.val_succ]
      split_ifs <;> first | omega | contradiction
  | succ i =>
    have hi := i.isLt
    induction j using Fin.cases with
    | zero =>
      simp only [ggFirstEquiv_zero, ggFirstEquiv_succ, ggAttachCartan_some_none,
        EmbeddingLike.apply_eq_iff_eq, CartanMatrix.B, Matrix.of_apply, Fin.ext_iff,
        Fin.val_zero, Fin.val_succ]
      split_ifs <;> first | omega | contradiction
    | succ j =>
      have hj := j.isLt
      simp only [ggFirstEquiv_succ, ggAttachCartan_some_some, hC, CartanMatrix.B,
        Matrix.of_apply, Fin.ext_iff, Fin.val_succ]
      split_ifs <;> omega

theorem ggAttachCartan_shapeC (e : Fin (n + 3) ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.C (n + 3) i j) :
    ggAttachCartan C (e 0) =
      Matrix.reindex (ggFirstEquiv e) (ggFirstEquiv e) (CartanMatrix.C (n + 4)) := by
  refine ggMatrix_eq_reindex _ fun i j => ?_
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simp [CartanMatrix.C]
    | succ j =>
      have hj := j.isLt
      simp only [ggFirstEquiv_zero, ggFirstEquiv_succ, ggAttachCartan_none_some,
        EmbeddingLike.apply_eq_iff_eq, CartanMatrix.C, Matrix.of_apply, Fin.ext_iff,
        Fin.val_zero, Fin.val_succ]
      split_ifs <;> first | omega | contradiction
  | succ i =>
    have hi := i.isLt
    induction j using Fin.cases with
    | zero =>
      simp only [ggFirstEquiv_zero, ggFirstEquiv_succ, ggAttachCartan_some_none,
        EmbeddingLike.apply_eq_iff_eq, CartanMatrix.C, Matrix.of_apply, Fin.ext_iff,
        Fin.val_zero, Fin.val_succ]
      split_ifs <;> first | omega | contradiction
    | succ j =>
      have hj := j.isLt
      simp only [ggFirstEquiv_succ, ggAttachCartan_some_some, hC, CartanMatrix.C,
        Matrix.of_apply, Fin.ext_iff, Fin.val_succ]
      split_ifs <;> omega

theorem ggAttachCartan_shapeD (e : Fin (n + 3) ≃ Λ) (hn : 1 ≤ n)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.D (n + 3) i j) :
    ggAttachCartan C (e 0) =
      Matrix.reindex (ggFirstEquiv e) (ggFirstEquiv e) (CartanMatrix.D (n + 4)) := by
  refine ggMatrix_eq_reindex _ fun i j => ?_
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simp [CartanMatrix.D]
    | succ j =>
      have hj := j.isLt
      simp only [ggFirstEquiv_zero, ggFirstEquiv_succ, ggAttachCartan_none_some,
        EmbeddingLike.apply_eq_iff_eq, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff,
        Fin.val_zero, Fin.val_succ]
      split_ifs <;> first | omega | simp_all
  | succ i =>
    have hi := i.isLt
    induction j using Fin.cases with
    | zero =>
      simp only [ggFirstEquiv_zero, ggFirstEquiv_succ, ggAttachCartan_some_none,
        EmbeddingLike.apply_eq_iff_eq, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff,
        Fin.val_zero, Fin.val_succ]
      split_ifs <;> first | omega | simp_all
    | succ j =>
      have hj := j.isLt
      simp only [ggFirstEquiv_succ, ggAttachCartan_some_some, hC, CartanMatrix.D,
        Matrix.of_apply, Fin.ext_iff, Fin.val_succ]
      split_ifs <;> omega

end Ext

theorem exists_weyl_ggAttachCartan_shapeBCD_b {Λ : Type} [DecidableEq Λ] {C : Matrix Λ Λ ℤ}
    {b : Λ} (hS : GGForkShapeBCD C b) :
    ∃ M' : CoxeterMatrix (Option Λ), GGIsWeylMatrix M' ∧ GGIntCartan M' (ggAttachCartan C b) := by
  obtain ⟨n, e, he0, hBC | hBC | ⟨hn, hD⟩⟩ := hS
  · refine ⟨(CoxeterMatrix.B (n + 4)).reindex (ggFirstEquiv e),
      Or.inl ⟨n + 4, ggFirstEquiv e, by omega, Or.inr (Or.inl ⟨by omega, rfl⟩)⟩, ?_⟩
    rw [← he0, ggAttachCartan_shapeB e hBC]
    exact (ggIntCartan_B (n + 4)).reindex _
  · refine ⟨(CoxeterMatrix.B (n + 4)).reindex (ggFirstEquiv e),
      Or.inl ⟨n + 4, ggFirstEquiv e, by omega, Or.inr (Or.inl ⟨by omega, rfl⟩)⟩, ?_⟩
    rw [← he0, ggAttachCartan_shapeC e hBC]
    exact (ggIntCartan_C (n + 4)).reindex _
  · refine ⟨(ggCoxeterMatrixD (n + 4)).reindex (ggFirstEquiv e),
      Or.inl ⟨n + 4, ggFirstEquiv e, by omega, Or.inr (Or.inr ⟨by omega, rfl⟩)⟩, ?_⟩
    rw [← he0, ggAttachCartan_shapeD e hn hD]
    exact (ggIntCartan_D (n + 4)).reindex _

end CFSG.StandardType
