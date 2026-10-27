module

public import CFSG.Quasithin.Background.SzG11SConf
public import CFSG.Quasithin.Background.SzG11SConcl

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

namespace SzG11S

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

structure G11Cx (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)) : Prop where
  hyp : G111Hyp B Γ v₁ W X X₀
  sqtk : IsQuotientOfSQTKTauCeti ↥Γ
  notConcl : ¬ G112ConclusionFixS B Γ X

structure G11Setup (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) : Prop where
  cx : G11Cx B Γ v₁ W X X₀
  h108 : G108Hyp B Γ v₁ W X X₀ L
  numConj : numConjugates Γ L ≤ 2

theorem G11Setup.toConf {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
    {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)}
    (hs : G11Setup B Γ v₁ W X X₀ L) : Conf B Γ v₁ W X X₀ L :=
  ⟨hs.cx.hyp, hs.cx.sqtk, hs.h108, hs.numConj⟩

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

end SzG11S

end G11

end CFSG.Quasithin

