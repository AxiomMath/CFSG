module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def IsMinFam16 (M U S H : Subgroup G) : Prop :=
  (S ≤ H ∧ H ≤ centralizer (U : Set G) ∧ ¬ H ≤ M) ∧
    ∀ H' : Subgroup G, H' ≤ H → (S ≤ H' ∧ H' ≤ centralizer (U : Set G) ∧ ¬ H' ≤ M) → H' = H

@[expose] def iSub16 (V H : Subgroup G) : Subgroup G :=
  conjClosure (V ⊓ pCoreOf 2 H) H

@[expose] def Shape166 (X : Type) [Group X] (Y : Subgroup X) (n : ℕ) : Prop :=
  Nat.card Y = 2 ^ n ∧
    ((1 < n ∧ (CFSG.Quasithin.IsPSL 2 2 n X ∨ CFSG.Quasithin.IsSz n X ∨
        (commutator X = ⊤ ∧ IsPSUGp (X ⧸ Subgroup.center X) 3 n ∧
          Nat.card (Subgroup.center X) ∣ 3))) ∨
      (n = 1 ∧ Y ⊔ fusionOddCore X = ⊤ ∧ ∃ p : ℕ, p.Prime ∧
        (Nat.card (fusionOddCore X) = p ∨
          (CFSG.IsExtraspecial p ↥(fusionOddCore X) ∧ Nat.card (fusionOddCore X) = p ^ 3))))

@[expose] def PSUThreeOuterInvolutionInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), commutator X = ⊤ →
    IsPSUGp (X ⧸ Subgroup.center X) 3 n → Nat.card (Subgroup.center X) ∣ 3 →
    ∀ Y : Subgroup X, IsElemAbelian 2 Y → Nat.card Y = 2 ^ n →
    ∀ α : MulAut X, α * α = 1 → (∀ y ∈ Y, α y = y) → (∀ y ∈ Y, α ≠ MulAut.conj y) →
      ∃ X₀ : Subgroup X, X₀ ≤ centralizer (Y : Set X) ∧ Odd (Nat.card X₀) ∧
        ¬ X₀ ≤ Subgroup.center X ∧
          ∀ c ∈ X₀, α c * c ∈ pCoreOf 2 (centralizer (Y : Set X))

end CFSG.LocalAnalysis.WeakClosure81

end
