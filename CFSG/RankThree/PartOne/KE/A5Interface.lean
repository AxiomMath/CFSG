module

public import CFSG.RankThree.PartOne.KE.A1Main

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open scoped MatrixGroups

@[expose] def a5Nodes (τ : Tag) : Set (Fin τ.rank) := {i | i.val ∈ ({1, 3, 4, 5, 6} : Set ℕ)}

@[expose] def A5Layer (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ], 1 ≤ f →
    (letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L) →
    ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → (ε = -1 → 2 < ℓ ^ f) →
    ∀ (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L), n ∈ adjointGroup τ L →
      (∃ u ∈ parabolicWeylGroup τ (a5Nodes τ), ∀ α ∈ parabolicRoots τ (a5Nodes τ),
        weylQuotientHom τ L ⟨n, hn⟩ • α = u • (ε • α)) →
      ∀ Γ P : Subgroup (ModGL τ L), Γ = rootSpan τ L (parabolicRoots τ (a5Nodes τ)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) →
      P = ⁅Γ, Γ⁆ →
      Finite P ∧ CFSG.IsQuasisimple P ∧
      (∀ y ∈ torusGroup τ L ⊔ rootSpan τ L (parabolicRoots τ (a5Nodes τ)),
        (∀ u ∈ P, y * u = u * y) →
        y ∈ torusGroup τ L ∧
          y ∈ Subgroup.centralizer (rootSpan τ L (parabolicRoots τ (a5Nodes τ)) : Set (ModGL τ L))) ∧
      ∀ (m : Fin τ.rank), m.val = 3 → ∀ (k : Type) [Field k] [Algebra k L] [IsAlgClosure k L],
        Nat.card k = ℓ ^ f → ∃ h₀ : ModGL τ L, ∀ Y : SL(2, k),
          h₀ * simpleRootSL2 τ L m (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P

end CFSG.RankThree.PartOne.KE
