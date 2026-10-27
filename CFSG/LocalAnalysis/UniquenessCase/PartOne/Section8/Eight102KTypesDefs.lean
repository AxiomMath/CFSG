module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def KTypesAt (G : Type) [Group G] [Finite G] (L : Subgroup G) (p n : ℕ) : Prop :=
  ∀ S : Subgroup G, S ≤ L → IsPGroup 3 S → ¬ 3 ∣ S.relIndex L →
    (∃ A : Subgroup G, F08.NotationA8103 L S p n A) ∧
    (∃ B : Subgroup G, F08.NotationB8103 L S n B) ∧
    (∀ Y : Subgroup G, Y ≤ S → Nat.card Y = 3 →
      F08.NotationA8103 L S p n Y ∨ F08.NotationB8103 L S n Y) ∧
    (∀ A : Subgroup G, F08.NotationA8103 L S p n A →
      p ∣ Nat.card (Bar2 (F08.DerInf8 (L ⊓ centralizer (A : Set G))))) ∧
    ∀ B₁ B₂ : Subgroup G, F08.NotationB8103 L S n B₁ → F08.NotationB8103 L S n B₂ →
      ∃ x ∈ L, B₂ = B₁.map (MulAut.conj x).toMonoidHom

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes
