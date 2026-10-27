module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs
public import CFSG.GH74.Uniqueness.SU.SU5Q8D8

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

@[expose] def K462 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 2 < p → ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Finite V]
      (ρ : Representation (ZMod p) G V), Function.Injective ρ → ρ.IsIrreducible →
    ∀ D : Subgroup G, Nat.card D = 3 → Subgroup.normalClosure (D : Set G) = ⊤ → fixV ρ D = ⊥ →
      CFSG.Open.pRank 3 (⊤ : Subgroup G) = 1 → commutator G = ⊤ →
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧ Nonempty (G ≃* SL(2, F))) ∨
      (∃ n : ℕ, Odd n ∧ LieModel G .PSL 2 2 n) ∨
      CFSG.Quasithin.IsExt G (fun V _ => CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 (⊤ : Subgroup V))
        (fun Y _ => CFSG.Quasithin.IsAlt 5 Y)

@[expose] def K46Semireg : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 2 < p → ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Finite V]
      (ρ : Representation (ZMod p) G V), Function.Injective ρ → ρ.IsIrreducible →
    ∀ D : Subgroup G, Nat.card D = 3 → Subgroup.normalClosure (D : Set G) = ⊤ → fixV ρ D = ⊥ →
      CFSG.Open.pRank 3 (⊤ : Subgroup G) = 1 → commutator G = ⊤ →
      (∀ (r : ℕ) (A : Subgroup G), r.Prime → r ≠ 2 → Nat.card A = r → fixV ρ A = ⊥) →
      Nonempty (G ≃* SL(2, ZMod 5)) ∨
      CFSG.Quasithin.IsExt G (fun V _ => CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 (⊤ : Subgroup V))
        (fun Y _ => CFSG.Quasithin.IsAlt 5 Y)

end CFSG.LocalAnalysis.UniquenessCase.UCK
