module

public import CFSG.Quasithin.Background.A3Structure312Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def A312PairStructCase {X : Type} [Group X] (B : Subgroup X) : Prop :=
  A312C2 B ⊤ ∨ A312C3 B ⊤ ∨
    (IsAlt 5 ↥B ∧ ∃ p : ℕ, p.Prime ∧ IsPSL 2 p 1 ↥(⊤ : Subgroup X) ∧ p ^ 2 % 5 = 1 ∧
      (p % 8 = 3 ∨ p % 8 = 5) ∧ 9 ∣ p ^ 2 - 1 ∧ 25 ∣ p ^ 2 - 1) ∨
    (∃ (s : Bool) (p : ℕ), p.Prime ∧ 3 < p ∧ IsSL2 p ↥B ∧
      (IsPSLEps3 s p 1 ↥(⊤ : Subgroup X) ∨ IsSLEps3 s p ↥(⊤ : Subgroup X)) ∧
      ∃ j : ℕ, (if s then p + 1 else p - 1) = 2 ^ j) ∨
    A312C16 B ⊤ ∨
    (IsExt ↥B (fun V _ => IsZ4StarExtra2 V) (fun Y _ => IsAlt 5 Y) ∧
      IsSporadic .HS ↥(⊤ : Subgroup X)) ∨
    (IsExt ↥B (fun V _ => IsExtraspecial2 3 V) (fun Y _ => IsPSL 3 2 1 Y) ∧
      IsSporadic .He ↥(⊤ : Subgroup X)) ∨
    (IsAlt 5 (ModO2 B) ∧ Nat.card (CFSG.pCore 2 ↥B) = 2 ^ 11 ∧
      IsSporadic .Ru ↥(⊤ : Subgroup X))

@[expose] def A312PairCentStruct : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSQTKCat X → CFSG.pCore 2 X = ⊥ →
    ∀ T : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ → ∀ B₁ ∈ lFamily T,
      ∀ B₂ ∈ lFamily T, B₁ ≠ ⊤ → B₂ ≠ ⊤ → B₁ ≠ B₂ →
      T ≤ Subgroup.normalizer (B₁ : Set X) → T ≤ Subgroup.normalizer (B₂ : Set X) →
      ⁅B₁, B₂⁆ ≤ pCoreOf 2 B₁ ⊓ pCoreOf 2 B₂ → Nonempty (ModO2 B₁ ≃* ModO2 B₂) →
      A312PairStructCase B₁ → False

end CFSG.Quasithin.Vol2.Ch10
