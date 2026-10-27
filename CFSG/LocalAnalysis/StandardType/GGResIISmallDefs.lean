module

public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGResIILinInput : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [Fintype Λ] [DecidableEq Λ] (b : Λ)
    (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ) (MK : CoxeterMatrix (Option {i : Λ // i ≠ b}))
    (CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ)
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (g : Option Λ → (V ≃ₗ[ZMod p] V)) (h : Option Λ → V)
    (α : Option Λ → Module.Dual (ZMod p) V) (x y : V),
    p ≠ 2 → Fintype.card Λ < 9 →
    GGIsWeylMatrix ML → GGIntCartan ML CL → GGIsWeylMatrix MK → GGIntCartan MK CK →
    GGDeletedConnected ML b →
    (∀ o w, g o w = w - α o w • h o) →
    (∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p)) →
    (∀ o o' : Option {i : Λ // i ≠ b},
      α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod p)) →
    LinearIndependent (ZMod p) (fun i : Λ => h (some i)) → ¬ LinearIndependent (ZMod p) h →
    (∀ i : Λ, α (some i) x = 0) →
    (∀ w : V, (∀ i : Λ, α (some i) w = 0) → w ∈ Submodule.span (ZMod p) {x}) →
    α none x ≠ 0 →
    (∀ o : Option {i : Λ // i ≠ b}, α (o.map Subtype.val) y = 0) →
    y ∉ Submodule.span (ZMod p) {x} →
    (∃ t ∈ Subgroup.closure (Set.range g),
        Module.finrank (ZMod p) (ggLinMove t) = 1 ∧ ∀ w, t (t w - w) = t w - w) ∨
      (5 ≤ p ∧ ∃ ψ ∈ Subgroup.closure (Set.range g), ∃ j j' : Λ, j ≠ b ∧ j' ≠ b ∧
        α (some j') (ψ (h (some j))) * α (some j) (ψ⁻¹ (h (some j'))) ∉
          ({0, 1, 2, 3, 4} : Set (ZMod p))) ∨
      ZS.LinWeyl p (Subgroup.closure (Set.range g))

end CFSG.StandardType
