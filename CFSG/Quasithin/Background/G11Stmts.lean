module

public import CFSG.Quasithin.Background.G10Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def fittingOf (Γ : Subgroup (GLV V)) : Subgroup (GLV V) :=
  (genFittingFitting ↥Γ).map Γ.subtype

@[expose] def centralizerIn (X H : Subgroup (GLV V)) : Subgroup (GLV V) :=
  X ⊓ Subgroup.centralizer (H : Set (GLV V))

@[expose] def IsNatAltModule (H : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) (n : ℕ) : Prop :=
  ∃ (φ : ↥H ≃* ↥(alternatingGroup (Fin n))) (β : ↥(permCore n) →ₗ[ZMod 2] V),
    LinearMap.range β = I ∧
    (∀ u : ↥(permCore n), β u = 0 ↔
      (u = 0 ∨ (Even n ∧ ∀ i, (u : Fin n → ZMod 2) i = 1))) ∧
    ∀ (γ : ↥H) (u u' : ↥(permCore n)),
      (u' : Fin n → ZMod 2) = permAct ((φ γ : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n))
        (u : Fin n → ZMod 2) → β u' = (γ : GLV V) (β u)

@[expose] def G112Concl8S8 (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)) : Prop :=
  Module.finrank (ZMod 2) V = 8 ∧ Nonempty (↥Γ ≃* Equiv.Perm (Fin 8)) ∧
    ∃ I : Submodule (ZMod 2) V, Module.finrank (ZMod 2) I = 4 ∧
      (∀ w ∈ I, ∀ w' ∈ I, B w w' = 0) ∧
      (∀ γ ∈ (genFittingLayer ↥Γ).map Γ.subtype, ∀ v ∈ I, γ v ∈ I) ∧
      ∃ x ∈ X, (∃ v ∈ I, x v ∉ I) ∧ IsCompl I (I.map (x : V →ₗ[ZMod 2] V))

@[expose] def G112Concl6U33 (Γ : Subgroup (GLV V)) : Prop :=
  Module.finrank (ZMod 2) V = 6 ∧ Nat.card Γ = 6048

@[expose] def G112ConclusionFix (B : LinearMap.BilinForm (ZMod 2) V) (Γ X : Subgroup (GLV V)) :
    Prop :=
  G112Conclusion B Γ X ∨ G112Concl8S8 B Γ X ∨ G112Concl6U33 Γ

@[expose] def TheoremG112Fix : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)),
    G111Hyp B Γ v₁ W X X₀ → IsQuotientOfSQTKTauCeti ↥Γ → G112ConclusionFix B Γ X

structure G11Cx (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)) : Prop where
  hyp : G111Hyp B Γ v₁ W X X₀
  sqtk : IsQuotientOfSQTKTauCeti ↥Γ
  notConcl : ¬ G112ConclusionFix B Γ X

structure G11Setup (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) : Prop where
  cx : G11Cx B Γ v₁ W X X₀
  h108 : G108Hyp B Γ v₁ W X X₀ L
  numConj : numConjugates Γ L ≤ 2

@[expose] def G114Stmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)),
    G11Cx B Γ v₁ W X X₀ → IsIrr Γ ⊤

@[expose] def G115Stmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)),
    G11Cx B Γ v₁ W X X₀ → IsIrr Γ ⊤ →
      ∃ x ∈ X, x ≠ 1 ∧ ∀ f ∈ fittingOf Γ, x * f = f * x

@[expose] def G115bStmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)),
    G11Cx B Γ v₁ W X X₀ → IsIrr Γ ⊤ →
      (∃ x ∈ X, x ≠ 1 ∧ ∀ f ∈ fittingOf Γ, x * f = f * x) →
      ∃ L : Subgroup (GLV V), IsComponentOf L Γ ∧ (∃ x ∈ X, ∃ l ∈ L, x * l ≠ l * x) ∧
        numConjugates Γ L ≤ 2

@[expose] def G116Props (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (X L : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) : Prop :=
  IrrPlus (normalClosure Γ L) I ∧ v₁ ∈ I ∧ Invariant X I ∧
    (∀ J : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) J → Invariant X J → J = I) ∧
    Homogeneous (normalClosure Γ L) ∧ (I = ⊤ ∨ Isotropic B I) ∧ SelfDual (normalClosure Γ L) I ∧
    FaithfulOn (normalClosure Γ L) I ∧ ¬ AutAll (normalClosure Γ L) I

@[expose] def G116Stmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    G11Setup B Γ v₁ W X X₀ L → ∃ I : Submodule (ZMod 2) V, G116Props B Γ v₁ X L I

@[expose] def G117Stmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    G11Setup B Γ v₁ W X X₀ L → ∀ I : Submodule (ZMod 2) V, G116Props B Γ v₁ X L I →
      ¬ FaithfulOn X I ∧ I ≠ ⊤

@[expose] def G118Stmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    G11Setup B Γ v₁ W X X₀ L → ∀ I : Submodule (ZMod 2) V, G116Props B Γ v₁ X L I →
      2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) V ∧
        fixedSpace X = Submodule.span (ZMod 2) {v₁} ∧
        ∀ x ∈ centralizerIn X (normalClosure Γ L), ∀ i ∈ I, x i = i

@[expose] def G119Stmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    G11Setup B Γ v₁ W X X₀ L → ∀ I : Submodule (ZMod 2) V, G116Props B Γ v₁ X L I →
      (∀ x ∈ X, x ∉ centralizerIn X (normalClosure Γ L) →
        ∃ Ix : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) Ix ∧ Ix ≤ B.orthogonal I ∧
          Ix ≠ I ∧ conjSub x Ix = Ix ∧
          ∃ c : V, Ix ⊓ W = Submodule.span (ZMod 2) {c} ∧ InducesTransvection x Ix c) ∧
      (∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ IsNatAltModule (normalClosure Γ L) I n) ∧
      (centralizerIn X (normalClosure Γ L)).relIndex X = 2 ∧
      ∀ x ∈ X, x ∉ centralizerIn X (normalClosure Γ L) →
        3 ≤ Module.finrank (ZMod 2) ↥(fixedSpace (Subgroup.zpowers x) ⊓ I)

end G11

end CFSG.Quasithin
