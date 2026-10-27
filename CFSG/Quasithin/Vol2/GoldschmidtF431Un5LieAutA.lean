module

public import CFSG.LocalAnalysis.EvenBN.U5.Model
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Gen

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

set_option linter.unusedSectionVars false

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit

section Blocks

variable {K : Type} [Field K]

@[expose] def nN (K : Type) [Field K] : Matrix (HypIndex 2 1) (HypIndex 2 1) K :=
  Matrix.single ιe₁ ιf₂ 1 + Matrix.single ιe₂ ιf₁ 1

theorem mul_nN_apply (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K) (a b : HypIndex 2 1) :
    (A * nN K) a b = (if ιf₂ = b then A a ιe₁ else 0) + (if ιf₁ = b then A a ιe₂ else 0) := by
  simp [nN, Matrix.mul_apply, Matrix.add_apply, Matrix.single_apply, mul_add,
    Finset.sum_add_distrib]

theorem nN_mul_apply (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K) (a b : HypIndex 2 1) :
    (nN K * A) a b = (if ιe₁ = a then A ιf₂ b else 0) + (if ιe₂ = a then A ιf₁ b else 0) := by
  simp [nN, Matrix.mul_apply, Matrix.add_apply, Matrix.single_apply, add_mul,
    Finset.sum_add_distrib]

theorem blocks_of_comm {A : Matrix (HypIndex 2 1) (HypIndex 2 1) K}
    (hA : A * nN K = nN K * A) :
    A ιz ιe₁ = 0 ∧ A ιz ιe₂ = 0 ∧ A ιf₁ ιe₁ = 0 ∧ A ιf₁ ιe₂ = 0 ∧ A ιf₂ ιe₁ = 0 ∧
      A ιf₂ ιe₂ = 0 ∧ A ιf₁ ιz = 0 ∧ A ιf₂ ιz = 0 ∧ A ιf₂ ιf₂ = A ιe₁ ιe₁ ∧
      A ιf₁ ιf₂ = A ιe₂ ιe₁ ∧ A ιf₂ ιf₁ = A ιe₁ ιe₂ ∧ A ιf₁ ιf₁ = A ιe₂ ιe₂ := by
  have e : ∀ a b, (if ιf₂ = b then A a ιe₁ else 0) + (if ιf₁ = b then A a ιe₂ else 0) =
      (if ιe₁ = a then A ιf₂ b else 0) + (if ιe₂ = a then A ιf₁ b else 0) := fun a b => by
    rw [← mul_nN_apply, ← nN_mul_apply, hA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [ιe₁, ιe₂, ιz, ιf₁, ιf₂] using e ιz ιf₂
  · simpa [ιe₁, ιe₂, ιz, ιf₁, ιf₂] using e ιz ιf₁
  · simpa [ιe₁, ιe₂, ιz, ιf₁, ιf₂] using e ιf₁ ιf₂
  · simpa [ιe₁, ιe₂, ιz, ιf₁, ιf₂] using e ιf₁ ιf₁
  · simpa [ιe₁, ιe₂, ιz, ιf₁, ιf₂] using e ιf₂ ιf₂
  · simpa [ιe₁, ιe₂, ιz, ιf₁, ιf₂] using e ιf₂ ιf₁
  · simpa [ιe₁, ιe₂, ιz, ιf₁, ιf₂] using (e ιe₂ ιz).symm
  · simpa [ιe₁, ιe₂, ιz, ιf₁, ιf₂] using (e ιe₁ ιz).symm
  · simpa [ιe₁, ιe₂, ιz, ιf₁, ιf₂] using (e ιe₁ ιf₂).symm
  · simpa [ιe₁, ιe₂, ιz, ιf₁, ιf₂] using (e ιe₂ ιf₂).symm
  · simpa [ιe₁, ιe₂, ιz, ιf₁, ιf₂] using (e ιe₁ ιf₁).symm
  · simpa [ιe₁, ιe₂, ιz, ιf₁, ιf₂] using (e ιe₂ ιf₁).symm

theorem eq_blk3_of_vanish (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K)
    (h1 : ∀ k j, A (.inr (.inl k)) (.inl j) = 0) (h2 : ∀ i j, A (.inr (.inr i)) (.inl j) = 0)
    (h3 : ∀ i l, A (.inr (.inr i)) (.inr (.inl l)) = 0) :
    A = blk3 (A.submatrix Sum.inl Sum.inl) (A.submatrix Sum.inl (Sum.inr ∘ Sum.inl))
      (A.submatrix Sum.inl (Sum.inr ∘ Sum.inr))
      (A.submatrix (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inl))
      (A.submatrix (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inr))
      (A.submatrix (Sum.inr ∘ Sum.inr) (Sum.inr ∘ Sum.inr)) := by
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j <;> simp [h1, h2, h3]

theorem oddUni_zero_eq {f : ℕ} {h : UnitaryFieldData 2 f K} (C : Matrix (Fin 2) (Fin 2) K) :
    oddUni h 0 C = blk3 1 0 C 1 0 1 := by
  rw [oddUni]
  congr 1
  ext _ _
  simp

theorem map_blk3 (σ : K ≃+* K) (A X Y P Q D : _) :
    (blk3 (r := 2) (ε := 1) A X Y P Q D).map σ =
      blk3 (A.map σ) (X.map σ) (Y.map σ) (P.map σ) (Q.map σ) (D.map σ) := by
  ext a b
  rcases a with i | k | i <;> rcases b with j | l | j <;> simp

theorem blk3_oddUni_comm {f : ℕ} {h : UnitaryFieldData 2 f K} (σ : K ≃+* K)
    (Aee : Matrix (Fin 2) (Fin 2) K) (X : Matrix (Fin 2) (Fin 1) K)
    (Yb : Matrix (Fin 2) (Fin 2) K) (P : Matrix (Fin 1) (Fin 1) K) (Q : Matrix (Fin 1) (Fin 2) K)
    (D Y Y'' : Matrix (Fin 2) (Fin 2) K) (hD : Y'' * D = Aee * Y.map σ) :
    oddUni h 0 Y'' * blk3 Aee X Yb P Q D = blk3 Aee X Yb P Q D * (oddUni h 0 Y).map σ := by
  rw [oddUni_zero_eq, oddUni_zero_eq, map_blk3, blk3_mul, blk3_mul]
  congr 1 <;> simp [hD, add_comm]

end Blocks

end CFSG.Quasithin.H13.F431.Un.L5
