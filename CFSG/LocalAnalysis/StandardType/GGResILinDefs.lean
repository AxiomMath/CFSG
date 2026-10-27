module

public import CFSG.LocalAnalysis.StandardType.GGResIDefs
public import CFSG.LocalAnalysis.StandardType.GGResILineDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGResILineCert (p : ℕ) {Λ : Type} (b : Λ) (CL : Matrix Λ Λ ℤ) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Finite V] (g : Option Λ → (V ≃ₗ[ZMod p] V))
    (α : Option Λ → Module.Dual (ZMod p) V) (allA : Prop) : Prop :=
  ∃ (T : GGResLineJType) (e : Fin T.rank ≃ {i : Λ // i ≠ b}),
    (∀ k l, CL (e k).1 (e l).1 = T.cartan k l) ∧
    LinearIndependent (ZMod p) (fun j : {i : Λ // i ≠ b} => α (some j.1)) ∧
    ∃ (z w : V) (F : List ((V ≃ₗ[ZMod p] V) × Option Λ)) (S : Subgroup (V ≃ₗ[ZMod p] V)),
      (∀ j : Λ, j ≠ b → α (some j) z = 0) ∧ (∀ j : Λ, j ≠ b → α (some j) w = 0) ∧
      (∃ i : Λ, α (some i) z ≠ 0) ∧ F ≠ [] ∧
      (∀ ψo ∈ F, (allA ∨ ψo.2 ≠ none) ∧ ψo.1 ∈ Subgroup.closure (Set.range g) ∧
        α ψo.2 (ψo.1⁻¹ z) = 0 ∧ α ψo.2 (ψo.1⁻¹ w) ≠ 0 ∧
        ∃ j : Λ, j ≠ b ∧ ψo.1 * g ψo.2 * ψo.1⁻¹ * g (some j) ≠
          g (some j) * (ψo.1 * g ψo.2 * ψo.1⁻¹)) ∧
      S ≤ Subgroup.closure ({t | ∃ ψo ∈ F, t = ψo.1 * g ψo.2 * ψo.1⁻¹} ∪
        {t | ∃ j : Λ, j ≠ b ∧ t = g (some j)}) ∧
      T.bad ∣ Nat.card S

@[expose] def GGResILinInput : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [Fintype Λ] [DecidableEq Λ] (b : Λ)
    (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ) (MK : CoxeterMatrix (Option {i : Λ // i ≠ b}))
    (CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ)
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V] [Finite V]
    (g : Option Λ → (V ≃ₗ[ZMod p] V)) (h : Option Λ → V)
    (α : Option Λ → Module.Dual (ZMod p) V) (x : V),
    p ≠ 2 → 3 ≤ Fintype.card Λ → Fintype.card Λ < 8 →
    GGIsWeylMatrix ML → GGIntCartan ML CL → GGIsWeylMatrix MK → GGIntCartan MK CK →
    GGDeletedConnected ML b → ¬ GGResIForkShape b CL CK →
    (∀ o w, g o w = w - α o w • h o) →
    (∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p)) →
    (∀ o o' : Option {i : Λ // i ≠ b},
      α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod p)) →
    LinearIndependent (ZMod p) h → Submodule.span (ZMod p) (Set.range h) = ⊤ →
    (∀ i : Λ, α (some i) x = 0) →
    (∀ w : V, (∀ i : Λ, α (some i) w = 0) → w ∈ Submodule.span (ZMod p) {x}) → x ≠ 0 →
    (∃ t ∈ Subgroup.closure (Set.range g),
        Module.finrank (ZMod p) (ggLinMove t) = 1 ∧ ∀ w, t (t w - w) = t w - w) ∨
      (α none (h (some b)) = 0 ∧ ∃ M₀ : CoxeterMatrix (Option Λ), GGIsWeylMatrix M₀ ∧
        GGIntCartan M₀ (ggResIGlue b CL CK)) ∨
      (5 ≤ p ∧ ∃ ψ ∈ Subgroup.closure (Set.range g), ∃ j j' : Λ, j ≠ b ∧ j' ≠ b ∧
        GGTriBad p (ggTriMat (α (some j)) (α (some j'))
          ((α (some j)).comp (ψ⁻¹ : V ≃ₗ[ZMod p] V).toLinearMap) (h (some j)) (h (some j'))
          (ψ (h (some j))))) ∨
      (p = 3 ∧ ∃ R : List (V ≃ₗ[ZMod p] V), (∀ k : Λ, g (some k) ∈ R) ∧
        (∀ k : Λ, ∀ r ∈ R, g (some k) * r * (g (some k))⁻¹ ∈ R) ∧
        ∃ ψ ∈ Subgroup.closure (Set.range g), ∃ i : Λ, α (some i) (ψ⁻¹ x) = 0 ∧
          ψ * g (some i) * ψ⁻¹ ∉ R) ∨
      (p = 3 ∧ GGResILineCert p b CL g α False) ∨
      (GGResO2aCell p b CL CK (α none (h (some b))) (α (some b) (h none)) ∧
        GGResILineCert p b CL g α True) ∨
      GGResO2bCell p b CL CK (α none (h (some b))) (α (some b) (h none)) ∨
      ZS.LinWeyl p (Subgroup.closure (Set.range g))

end CFSG.StandardType
