module

public import CFSG.RankThree.PartOne.KE.A1Main

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open scoped MatrixGroups

@[expose] def d4Nodes (τ : Tag) : Set (Fin τ.rank) := {i | 1 ≤ i.val ∧ i.val ≤ 4}

@[expose] def D4TranspositionLayer (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
    (letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L) →
    ∀ i j : Fin τ.rank, i ≠ j → i.val ∈ ({1, 2, 4} : Set ℕ) → j.val ∈ ({1, 2, 4} : Set ℕ) →
    ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice (Equiv.swap i j) α) →
      ∀ P : Subgroup (ModGL τ L), P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
      Finite P ∧ CFSG.IsQuasisimple P ∧
      (∀ y ∈ torusGroup τ L ⊔ rootSpan τ L (parabolicRoots τ (d4Nodes τ)),
        (∀ u ∈ P, y * u = u * y) →
        y ∈ torusGroup τ L ∧
          y ∈ Subgroup.centralizer (rootSpan τ L (parabolicRoots τ (d4Nodes τ)) : Set (ModGL τ L))) ∧
      ∀ (m : Fin τ.rank), m.val = 3 → ∀ (k : Type) [Field k] [Algebra k L] [IsAlgClosure k L],
        Nat.card k = ℓ ^ f → ∃ h₀ : ModGL τ L, ∀ Y : SL(2, k),
          h₀ * simpleRootSL2 τ L m (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P

@[expose] def D4TrialityLayer (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
    ∀ a b c : Fin τ.rank, a ≠ b → b ≠ c → a ≠ c → a.val ∈ ({1, 2, 4} : Set ℕ) →
    b.val ∈ ({1, 2, 4} : Set ℕ) → c.val ∈ ({1, 2, 4} : Set ℕ) →
    ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice (List.formPerm [a, b, c]) α) →
      ∀ P : Subgroup (ModGL τ L), P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
      Finite P ∧ CFSG.IsQuasisimple P ∧
      (∀ y ∈ torusGroup τ L ⊔ rootSpan τ L (parabolicRoots τ (d4Nodes τ)),
        (∀ u ∈ P, y * u = u * y) →
        y ∈ torusGroup τ L ∧
          y ∈ Subgroup.centralizer (rootSpan τ L (parabolicRoots τ (d4Nodes τ)) : Set (ModGL τ L))) ∧
      ∀ (m : Fin τ.rank), m.val = 3 → ∀ (k : Type) [Field k] [Algebra k L] [IsAlgClosure k L],
        Nat.card k = ℓ ^ f → ∃ h₀ : ModGL τ L, ∀ Y : SL(2, k),
          h₀ * simpleRootSL2 τ L m (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P

end CFSG.RankThree.PartOne.KE
