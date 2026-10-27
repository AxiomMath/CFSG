module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112K

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGEichler {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (g : V ≃ₗ[ZMod 3] V) : Prop :=
  g ≠ 1 ∧ ∀ v, g (g v) + g v + v = 0

@[expose] def GGWeylNoEichlerRho {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod 3) U] (h : Fin n → U)
    (α : Fin n → Module.Dual (ZMod 3) U),
    LinearIndependent (ZMod 3) h → Submodule.span (ZMod 3) (Set.range h) = ⊤ →
    (∀ i j, α i (h j) = ((C i j : ℤ) : ZMod 3)) →
    ∀ g ∈ ggQ2WeylOf h α, g ≠ 1 → ∃ (v : U) (i : Fin n), α i (g (g v) + g v + v) ≠ 0

@[expose] def GGWeylE7NoEichler : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module (ZMod 3) U] (h : Fin 7 → U)
    (α : Fin 7 → Module.Dual (ZMod 3) U),
    LinearIndependent (ZMod 3) h → Submodule.span (ZMod 3) (Set.range h) = ⊤ →
    (∀ i j, α i (h j) = ((CartanMatrix.E 7 i j : ℤ) : ZMod 3)) →
    ∀ g ∈ ggQ2WeylOf h α, ¬ GGEichler g

end CFSG.StandardType

end
