module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront05

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F05

@[expose] def Case147SzJ1 {G : Type} [Group G] (L : Subgroup G) (n : ℕ) : Prop :=
  ((2 < n ∧ IsSz ↥L n) ∨ (IsJ1 ↥L ∧ n = 3)) ∧ numConj L ≤ 2

@[expose] def K147SzJ1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V), Function.Injective ρ → ρ.IsIrreducible →
    ∀ L : Subgroup G, IsComponentOf L ⊤ → ∀ n : ℕ, Case147SzJ1 L n → n + 1 < mGV ρ

end CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
