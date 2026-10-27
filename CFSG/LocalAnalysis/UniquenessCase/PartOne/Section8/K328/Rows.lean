module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open

@[expose] def rhoOmega (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Matrix (Fin 2) (Fin 2) F :=
  !![0, 1; 1, 1]

@[expose] def blockDiag3 (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ)
    (A₀ A₁ A₂ : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i j =>
    if i.val / 2 = j.val / 2 then
      (if i.val / 2 = 0 then A₀ else if i.val / 2 = 1 then A₁ else if i.val / 2 = 2 then A₂
        else 1) ⟨i.val % 2, Nat.mod_lt _ (by norm_num)⟩ ⟨j.val % 2, Nat.mod_lt _ (by norm_num)⟩
    else 0

@[expose] def rhoL (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A₀ A₁ : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F :=
  Matrix.fromBlocks A₀ A₁ A₁ (A₀ + A₁)

@[expose] def ofColumns (F : Type) [Field F] [Fintype F] [DecidableEq F] {ι : Type}
    (img : ι → ι → F) : Matrix ι ι F :=
  Matrix.of fun r k => img k r

@[expose] def bv (F : Type) [Field F] [Fintype F] [DecidableEq F] {ι : Type} [DecidableEq ι]
    (i : ι) : ι → F :=
  Pi.single i 1

@[expose] def Row8 (F : Type) [Field F] [Fintype F] [DecidableEq F] : Prop :=
  Fintype.card F = 8 → ∀ b c : F, (∀ s : F, s ^ 2 + b * s + c ≠ 0) →
    ∀ α : F, α ^ 2 + α = 1 + c / b ^ 2 →
    let e : Fin 3 → (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := fun i => bv F (Sum.inl i)
    let f : Fin 3 → (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F) := fun i => bv F (Sum.inr (Sum.inl i))
    let u : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F := bv F (Sum.inr (Sum.inr 0))
    let v : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → F := bv F (Sum.inr (Sum.inr 1))
    ∀ z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F,
    (z₀ : Matrix _ _ F) = ofColumns F (Sum.elim ![e 0 + f 1, f 0 + e 1, e 2]
      (Sum.elim ![e 1, e 0, f 2] ![α • u + b⁻¹ • v, (c / b) • u + (α + 1) • v])) →
    (t₀ : Matrix _ _ F) = ofColumns F (Sum.elim ![e 1, e 0 + e 1, e 2]
      (Sum.elim ![f 0 + f 1, f 0, f 2] ![u, v])) →
    MatrixRowData (StatedOmega (StatedQuadMinus 4 F b c)) z₀ t₀
      (stdComp (StatedOmega (StatedQuadMinus 4 F b c)) z₀)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
