module

public import CFSG.RankThree.PartTwo.Sec13.F135LastKDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec13.F135LastAct

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup
open scoped commutatorElement

@[expose] def KF135 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Sec4.Census.List42 S → ∀ p : ℕ, p.Prime → 7 ≤ p →
    ∀ P : Subgroup (MulAut S), IsPGroup p P → p ^ 3 ≤ Nat.card P → (∀ x ∈ P, x ^ p = 1) →
    ∀ x ∈ P, orderOf x = p →
    ∀ u : MulAut S, u ≠ 1 → (∃ k : ℕ, u ^ 2 ^ k = 1) → u * x = x * u →
    ∀ V : Subgroup (MulAut S), V ≠ ⊥ → IsPGroup 2 V →
      (∀ v ∈ V, x * v * x⁻¹ ∈ V) →
      ⁅V, Subgroup.zpowers x⁆ = V →
    (∀ F : Subgroup (MulAut S), F ≤ (MulAut.conj : S →* MulAut S).range →
        CFSG.Open.IsElemAbelian p F → Nat.card F = p ^ 2 →
        ∀ T : Subgroup S, T ≠ ⊥ → IsPGroup 2 T → ∃ φ ∈ F, T.map φ.toMonoidHom ≠ T) →
    (∀ F : Subgroup (MulAut S), F ≤ P → CFSG.Open.IsElemAbelian p F → Nat.card F = p ^ 2 →
        ∀ T : Subgroup S, T ≠ ⊥ → IsPGroup 2 T → ∃ φ ∈ F, T.map φ.toMonoidHom ≠ T) →
    Identified p S

@[expose] def KFactG1 : Prop :=
  ∀ (I : Type) [Group I] [Finite I], CFSG.IsQuasisimple I →
    Sec4.Census.List42 (I ⧸ Subgroup.center I) →
    ∀ p : ℕ, p.Prime → 7 ≤ p → ∀ f : MulAut I, orderOf f = p →
      ∀ V : Subgroup (MulAut (I ⧸ Subgroup.center I)), V ≠ ⊥ → IsPGroup 2 V →
        (∀ v ∈ V, (centerQuotMulAut I f) * v *
          (centerQuotMulAut I f)⁻¹ ∈ V) →
        ⁅V, Subgroup.zpowers (centerQuotMulAut I f)⁆ = V →
        ∃ T : Subgroup I, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T.map f.toMonoidHom = T

@[expose] def KFactOutP : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Sec4.Census.List42 S → ∀ p : ℕ, p.Prime → 7 ≤ p →
    ∀ P : Subgroup (MulAut S), (∀ x ∈ P, x ^ p = 1) →
      (P ⊓ (MulAut.conj : S →* MulAut S).range).relIndex P ≤ p

@[expose] def KFactMultPrime : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], CFSG.IsQuasisimple Q →
    Sec4.Census.List42 (Q ⧸ Subgroup.center Q) →
    ∀ p : ℕ, p.Prime → 7 ≤ p → ¬ p ∣ Nat.card (Subgroup.center Q)

end CFSG.RankThree.PartTwo.Sec13.F135Last
