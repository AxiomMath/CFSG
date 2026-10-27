module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsSz)
open Subgroup

structure KFacts1234 : Prop where
  card_L2 : ∀ (X : Type) [Group X] (n : ℕ), 1 ≤ n → IsL2 X n → Nat.card X = 2 ^ n * (4 ^ n - 1)
  card_Sz : ∀ (X : Type) [Group X] (n : ℕ), IsSz X n →
    Nat.card X = (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1)
  card_SzGp : ∀ (X : Type) [Group X] (n : ℕ), SevenK.IsSzGp X n →
    Nat.card X = (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1)
  card_PSU2 : ∀ (X : Type) [Group X] (n : ℕ), 1 ≤ n → IsPSUGp X 2 n →
    Nat.card X = 2 ^ n * (4 ^ n - 1)
  card_suzukiRoot : ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (W : Subgroup X),
    Odd (Nat.card (Subgroup.center X)) → SevenK.IsSzGp (X ⧸ Subgroup.center X) n →
      IsSuzukiRootGroup X W → Nat.card W = 2 ^ n
  transvection_normalizer : ∀ (m : ℕ) (F : Type) [Field F] [Finite F] (a a' : Fin m → F),
    3 ≤ m → a ≠ 0 → a' ≠ 0 → (∀ c : F, a' ≠ c • a) →
      ∃ x ∈ transvectionCenterSet m F a, x ≠ 1 ∧
        ∀ y ∈ transvectionCenterSet m F a', x * y * x⁻¹ ∈ transvectionCenterSet m F a'
  transvection_conj : ∀ (m : ℕ) (F : Type) [Field F] [Finite F] (a : Fin m → F)
      (γ : StatedProj (StatedSL m F)), 3 ≤ m → a ≠ 0 → ∃ a' : Fin m → F, a' ≠ 0 ∧
      {x | ∃ y ∈ transvectionCenterSet m F a, x = γ * y * γ⁻¹} = transvectionCenterSet m F a'
  sp_config : ∀ (l n : ℕ) (F : Type) [Field F] [Finite F], 2 ≤ l → 2 ≤ n → Nat.card F = 2 ^ n →
    ∀ A B : Subgroup ↥(StatedSp l F), Nat.card A = 2 ^ n → Nat.card B = 2 ^ n →
      (∀ x ∈ A, x ≠ 1 → SevenK.IsSymplecticTransvectionIn l x) →
      (∀ x ∈ B, x ≠ 1 → SevenK.IsSymplecticTransvectionIn l x) →
      ¬ (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
      ∃ γ τ, τ ∈ A ⊔ B ∧ conjSubgroup A γ ≠ A ∧
        (∀ x ∈ conjSubgroup A γ, ∀ y ∈ A ⊔ B, x * y = y * x) ∧
        τ ∈ Subgroup.normalizer (A : Set _) ∧ (∀ a ∈ A, τ * a = a * τ → a = 1)
  su_config : ∀ (m n : ℕ) (F : Type) [Field F] [Finite F], 4 ≤ m → 2 ≤ n →
    Nat.card F = (2 ^ n) ^ 2 →
    ∀ A B : Subgroup (StatedProj (StatedSU m (2 ^ n) F)), Nat.card A = 2 ^ n →
      Nat.card B = 2 ^ n →
      (∀ x ∈ A, x ≠ 1 → SevenK.IsUnitaryTransvectionIn m n x) →
      (∀ x ∈ B, x ≠ 1 → SevenK.IsUnitaryTransvectionIn m n x) →
      ¬ (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
      ∃ γ τ, τ ∈ A ⊔ B ∧ conjSubgroup A γ ≠ A ∧
        (∀ x ∈ conjSubgroup A γ, ∀ y ∈ A ⊔ B, x * y = y * x) ∧
        τ ∈ Subgroup.normalizer (A : Set _) ∧ (∀ a ∈ A, τ * a = a * τ → a = 1)
  rank_U3 : ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n →
    IsPSUGp (X ⧸ Subgroup.center X) 3 n → Odd (Nat.card (Subgroup.center X)) →
      ∀ E : Subgroup X, IsElemAbelian 2 E → Nat.card E ≤ 2 ^ n
  rank_out_U3 : ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n → IsPSUGp X 3 n →
    ∀ E : Subgroup (MulAut X), IsElemAbelian 2 E →
      E ⊓ (MulAut.conj : X →* MulAut X).range = ⊥ → Nat.card E ≤ 2
  rank_A6 : ∀ E : Subgroup (alternatingGroup (Fin 6)), IsElemAbelian 2 E → Nat.card E ≤ 4
  rank_out_A6 : ∀ E : Subgroup (MulAut (alternatingGroup (Fin 6))), IsElemAbelian 2 E →
    E ⊓ (MulAut.conj : alternatingGroup (Fin 6) →* _).range = ⊥ → Nat.card E ≤ 2

end CFSG.LocalAnalysis.WeakClosure81
