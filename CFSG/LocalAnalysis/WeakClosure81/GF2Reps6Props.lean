module

public import CFSG.LocalAnalysis.WeakClosure81.W18Asch66

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (CoverOf)
open CFSG.Blueprint (LieModel)

@[expose] def Asch6_4Odd : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ ρ : Q →* MulAut V, Function.Injective ρ →
    ∀ (L A : Subgroup Q), IsComponentOf L ⊤ → A ≤ normalizer (L : Set Q) → Nat.card A = 4 →
      IsElemAbelian 2 A → IsQuadraticOn ρ A → A ⊓ centralizer (L : Set Q) = ⊥ →
      ∀ p e : ℕ, p.Prime → p ≠ 2 → 9 < p ^ e → F6.IsL2 p e ↥L → False

@[expose] def Asch6_4Seven : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ ρ : Q →* MulAut V, Function.Injective ρ →
    ∀ (L A : Subgroup Q), IsComponentOf L ⊤ → A ≤ normalizer (L : Set Q) → Nat.card A = 4 →
      IsElemAbelian 2 A → IsQuadraticOn ρ A → A ⊓ centralizer (L : Set Q) = ⊥ → F6.IsL2 7 1 ↥L →
      ∀ a ∈ A, ∃ l ∈ L, a * l⁻¹ ∈ centralizer (L : Set Q)

@[expose] def Asch6_5Odd : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ ρ : Q →* MulAut V, Function.Injective ρ →
    ∀ (L A : Subgroup Q), IsComponentOf L ⊤ → Odd (Nat.card (center ↥L)) →
      A ≤ normalizer (L : Set Q) → Nat.card A = 4 → IsElemAbelian 2 A → IsQuadraticOn ρ A →
      A ⊓ centralizer (L : Set Q) = ⊥ →
      ∀ (p e : ℕ) (Y : Type) (_ : Group Y), p.Prime → p ≠ 2 → 3 < p ^ e →
        ((Odd e ∧ LieModel Y .PSL 3 p e) ∨ LieModel Y .PSU 3 p e) → CoverOf ↥L Y → False

@[expose] def Asch6_5Four : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ ρ : Q →* MulAut V, Function.Injective ρ →
    ∀ (L A : Subgroup Q), IsComponentOf L ⊤ → Odd (Nat.card (center ↥L)) →
      A ≤ normalizer (L : Set Q) → Nat.card A = 4 → IsElemAbelian 2 A → IsQuadraticOn ρ A →
      A ⊓ centralizer (L : Set Q) = ⊥ →
      ∀ (Y : Type) (_ : Group Y), (LieModel Y .PSL 3 2 2 ∨ LieModel Y .PSU 3 2 2) →
        CoverOf ↥L Y → ∀ a ∈ A, ∃ l ∈ L, a * l⁻¹ ∈ centralizer (L : Set Q)

end CFSG.LocalAnalysis.WeakClosure81

end
