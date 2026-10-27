module

public import CFSG.Quasithin.Background.G117CanonSetup
public import CFSG.Quasithin.Background.E11Stmt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped TensorProduct

namespace G11

namespace Canon

section Nine

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def IsTensorD3Core5 (Γ₀ : Subgroup (GLV V)) : Prop :=
  ∃ (φ : ↥Γ₀ ≃* (Equiv.Perm (Fin 3) × ↥(alternatingGroup (Fin 5))))
    (ψ : V ≃ₗ[ZMod 2] (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] ↥(CFSG.Quasithin.permCore 5))),
    ∀ (γ : ↥Γ₀) (a a' : ↥(CFSG.Quasithin.permCore 3)) (b b' : ↥(CFSG.Quasithin.permCore 5)),
      (a' : Fin 3 → ZMod 2) = CFSG.Quasithin.permAct (φ γ).1 (a : Fin 3 → ZMod 2) →
      (b' : Fin 5 → ZMod 2) =
          CFSG.Quasithin.permAct ((φ γ).2 : Equiv.Perm (Fin 5)) (b : Fin 5 → ZMod 2) →
        ψ ((γ : GLV V) (ψ.symm (a ⊗ₜ b))) = a' ⊗ₜ b'

@[expose] def IsTensorD3Nat24 (Γ₀ : Subgroup (GLV V)) : Prop :=
  ∃ (φ : ↥Γ₀ ≃* (Equiv.Perm (Fin 3) × ↥(StatedSL 2 (GaloisField 2 2))))
    (ψ : V ≃ₗ[ZMod 2] (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin 2 → GaloisField 2 2))),
    ∀ (γ : ↥Γ₀) (a a' : ↥(CFSG.Quasithin.permCore 3)) (b b' : Fin 2 → GaloisField 2 2),
      (a' : Fin 3 → ZMod 2) = CFSG.Quasithin.permAct (φ γ).1 (a : Fin 3 → ZMod 2) →
      b' = ((((φ γ).2 : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 2))).mulVec b →
        ψ ((γ : GLV V) (ψ.symm (a ⊗ₜ b))) = a' ⊗ₜ b'

@[expose] def IsTensorD3Perm5 (Γ : Subgroup (GLV V)) : Prop :=
  ∃ (φ : ↥Γ ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5)))
    (ψ : V ≃ₗ[ZMod 2] (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] ↥(CFSG.Quasithin.permCore 5))),
    ∀ (γ : ↥Γ) (first first' : ↥(CFSG.Quasithin.permCore 3))
      (second second' : ↥(CFSG.Quasithin.permCore 5)),
      (first' : Fin 3 → ZMod 2) = CFSG.Quasithin.permAct (φ γ).1 (first : Fin 3 → ZMod 2) →
      (second' : Fin 5 → ZMod 2) = CFSG.Quasithin.permAct (φ γ).2 (second : Fin 5 → ZMod 2) →
        ψ ((γ : GLV V) (ψ.symm (first ⊗ₜ second))) = first' ⊗ₜ second'

@[expose] def IsTensorD3Semilin24 (Γ : Subgroup (GLV V)) : Prop :=
  ∃ ψ : V ≃ₗ[ZMod 2] (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin 2 → GaloisField 2 2)),
    (∀ γ : ↥Γ, ∃ (σ : Equiv.Perm (Fin 3))
      (matrix : ↥(StatedSL 2 (GaloisField 2 2))) (twisted : Bool),
      ∀ (first first' : ↥(CFSG.Quasithin.permCore 3)) (second : Fin 2 → GaloisField 2 2),
        (first' : Fin 3 → ZMod 2) = CFSG.Quasithin.permAct σ (first : Fin 3 → ZMod 2) →
          ψ ((γ : GLV V) (ψ.symm (first ⊗ₜ second))) = first' ⊗ₜ
            ((((matrix : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) :
              Matrix (Fin 2) (Fin 2) (GaloisField 2 2))).mulVec
                (fun coordinate => if twisted then second coordinate ^ 2 else second coordinate))) ∧
    (∀ (σ : Equiv.Perm (Fin 3)) (matrix : ↥(StatedSL 2 (GaloisField 2 2))) (twisted : Bool),
      ∃ γ : ↥Γ, ∀ (first first' : ↥(CFSG.Quasithin.permCore 3)) (second : Fin 2 → GaloisField 2 2),
        (first' : Fin 3 → ZMod 2) = CFSG.Quasithin.permAct σ (first : Fin 3 → ZMod 2) →
          ψ ((γ : GLV V) (ψ.symm (first ⊗ₜ second))) = first' ⊗ₜ
            ((((matrix : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 2)) :
              Matrix (Fin 2) (Fin 2) (GaloisField 2 2))).mulVec
                (fun coordinate => if twisted then second coordinate ^ 2 else second coordinate)))

@[expose] def IsG112Nine (Γ : Subgroup (GLV V)) : Prop :=
  Module.finrank (ZMod 2) V = 8 ∧
    ((Nonempty (↥Γ ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 5))) ∧
      (IsTensorD3Perm5 Γ ∨ IsTensorD3Semilin24 Γ)) ∨
      IsTensorD3Core5 Γ ∨ IsTensorD3Nat24 Γ)

end Nine

@[expose] def G118NineInput : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (Γ L : Subgroup (GLV V))
    (I : Submodule (ZMod 2) V) (hHI : Invariant (normalClosure Γ L) I)
    (D : E11Data (normalClosure Γ L) I),
    normalClosure Γ L ≤ Γ →
    Module.finrank (ZMod 2) V = 8 → Module.finrank D.F D.U = 2 →
      Nonempty (↥(normalClosure Γ L) ≃* ↥(alternatingGroup (Fin 5))) →
      Nonempty (↥(Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V))) ≃*
        Equiv.Perm (Fin 3)) →
      ((Nat.card D.F = 2 ∧ ∃ (b c : GaloisField 2 1),
          (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) ∧
          IsNaturalMatrixModule (restrictRange (normalClosure Γ L) I hHI)
            (StatedOmega (StatedQuadMinus 2 (GaloisField 2 1) b c))) ∨
        (Nat.card D.F = 4 ∧
          IsNaturalMatrixModule (restrictRange (normalClosure Γ L) I hHI)
            (StatedSL 2 (GaloisField 2 2)))) →
      IsG112Nine Γ

structure G118NineContains (Q : ConclPred) : Prop where
  c9 : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)), IsG112Nine Γ → Q B Γ X

end Canon

end G11

end CFSG.Quasithin
