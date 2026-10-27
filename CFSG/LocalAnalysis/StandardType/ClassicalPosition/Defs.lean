module

public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.StandardType.ClassicalPosition

@[expose] def IsGLLift {U X ι F : Type} [Group U] [Group X] [Fintype ι] [DecidableEq ι] [Field F]
    (j : U →* GL ι F) (ψ : U →* X) (s : GL ι F) (b : X) : Prop :=
  ∀ u : U, ∃ u' : U, j u' = s * j u * s⁻¹ ∧ b⁻¹ * ψ u * b = ψ u'

@[expose] def glFixing {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (P : Matrix ι ι F) :
    Subgroup (GL ι F) where
  carrier := {g | (g : Matrix ι ι F) * P = P}
  mul_mem' {a b} ha hb := by
    change ((a * b : GL ι F) : Matrix ι ι F) * P = P
    have ha' : (a : Matrix ι ι F) * P = P := ha
    have hb' : (b : Matrix ι ι F) * P = P := hb
    rw [Units.val_mul, Matrix.mul_assoc, hb', ha']
  one_mem' := by
    change ((1 : GL ι F) : Matrix ι ι F) * P = P
    rw [Units.val_one, Matrix.one_mul]
  inv_mem' {a} ha := by
    change ((a⁻¹ : GL ι F) : Matrix ι ι F) * P = P
    have ha' : (a : Matrix ι ι F) * P = P := ha
    calc ((a⁻¹ : GL ι F) : Matrix ι ι F) * P
        = ((a⁻¹ : GL ι F) : Matrix ι ι F) * ((a : Matrix ι ι F) * P) := by rw [ha']
      _ = P := by rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mul]

@[expose] def glBlockCentralizer {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field F]
    (j : U →* GL ι F) (S : Set (GL ι F)) (ε : Matrix ι ι F) : Subgroup U :=
  (Subgroup.centralizer S ⊓ glFixing (1 - ε)).comap j

@[expose] noncomputable def formAdj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) (G a : Matrix ι ι F) : Matrix ι ι F :=
  G⁻¹ * Matrix.transpose (a.map σ) * G

@[expose] def IsPrimIdemIn {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : Subalgebra F (Matrix ι ι F)) (e : Matrix ι ι F) : Prop :=
  e ∈ A ∧ IsIdempotentElem e ∧ e ≠ 0 ∧
    ∀ e' ∈ A, IsIdempotentElem e' → e' * e = e' → e' = 0 ∨ e' = e

@[expose] def IsPrimAdjIdemIn {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (σ : F →+* F)
    (G : Matrix ι ι F) (A : Subalgebra F (Matrix ι ι F)) (ε : Matrix ι ι F) : Prop :=
  ε ∈ A ∧ IsIdempotentElem ε ∧ ε ≠ 0 ∧ formAdj σ G ε = ε ∧
    ∀ e' ∈ A, IsIdempotentElem e' → formAdj σ G e' = e' → e' * ε = e' → e' = 0 ∨ e' = ε

@[expose] noncomputable def blockDegree {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : Subalgebra F (Matrix ι ι F)) (e : Matrix ι ι F) : ℕ :=
  Module.finrank F ((Subalgebra.toSubmodule A).map (LinearMap.mulRight F e))

@[expose] def matTransvGroup {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (v φ : ι → F) :
    Subgroup (GL ι F) :=
  Subgroup.closure {g | ∃ c : F, (g : Matrix ι ι F) = 1 + c • Matrix.vecMulVec v φ}

@[expose] def unitTransvGroup {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (σ : F →+* F)
    (G : Matrix ι ι F) (v : ι → F) : Subgroup (GL ι F) :=
  Subgroup.closure {g | ∃ c : F, σ c = c ∧
    (g : Matrix ι ι F) = 1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) G)}

@[expose] def unitPairGroup {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (σ : F →+* F)
    (G : Matrix ι ι F) (v w : ι → F) : Subgroup (GL ι F) :=
  Subgroup.closure {g | ∃ c : F, (g : Matrix ι ι F) =
    1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (w i)) G) -
      σ c • Matrix.vecMulVec w (Matrix.vecMul (fun i => σ (v i)) G)}

@[expose] def altSiegelGroup {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G : Matrix ι ι F) (v w : ι → F) : Subgroup (GL ι F) :=
  Subgroup.closure {g | ∃ c : F, (g : Matrix ι ι F) =
    1 + c • (Matrix.vecMulVec v (Matrix.mulVec G w) + Matrix.vecMulVec w (Matrix.mulVec G v))}

@[expose] def siegelGroup {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (u w : V) : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure {g | ∃ c : K, g = CFSG.ClassicalGroups.Orthogonal.eichler Q u (c • w)}

end CFSG.StandardType.ClassicalPosition
