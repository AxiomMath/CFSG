module

public import CFSG.Quasithin.Background.A3Structure312Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def KGRank2ParabolicOrder : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (f : ℕ), 2 ≤ f → ∀ P : Subgroup Y,
    IsMaxParabolic2 (⊤ : Subgroup Y) P →
      ((IsPSL 3 2 f Y ∨ IsSL3 (2 ^ f) Y) →
        Nat.card ↥(perfectCore P) = 2 ^ (3 * f) * (2 ^ (2 * f) - 1)) ∧
      (IsPSp4 2 f Y → Nat.card ↥(perfectCore P) = 2 ^ (4 * f) * (2 ^ (2 * f) - 1))

@[expose] def KGA7OneA5 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], (IsAlt 7 Y ∨ IsHat Y ↥(alternatingGroup (Fin 7))) →
    ∀ T : Subgroup Y, IsSylowTwoOf T ⊤ → ∀ B₁ ∈ lFamily T, ∀ B₂ ∈ lFamily T,
      IsAlt 5 ↥B₁ → IsAlt 5 ↥B₂ → B₁ = B₂

@[expose] def KGTwoA5Generate : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (T : Subgroup Y), IsSylowTwoOf T ⊤ →
    ∀ B₁ ∈ lFamily T, ∀ B₂ ∈ lFamily T, IsAlt 5 ↥B₁ → IsAlt 5 ↥B₂ → B₁ ≠ B₂ →
      (((∃ p : ℕ, p.Prime ∧ (p % 5 = 1 ∨ p % 5 = 4) ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
            IsPSL 2 p 1 Y) ∨ IsPSL 2 5 2 Y) → B₁ ⊔ B₂ = ⊤) ∧
      (IsSporadic .J1 Y → B₁ ⊔ B₂ = ⊤ ∨ IsPSL 2 11 1 ↥(B₁ ⊔ B₂))

@[expose] def KGMathieuNatBlock : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y],
    (IsSporadic .M22 Y ∨ IsHat Y (CFSG.Blueprint.NativeSporadic.Carrier .M22)) →
    ∀ T : Subgroup Y, IsSylowTwoOf T ⊤ → ∀ B₁ ∈ lFamily T, ∀ B₂ ∈ lFamily T,
      (∀ B : Subgroup Y, (B = B₁ ∨ B = B₂) →
        IsElemAbelianOfRank 2 4 ↥(CFSG.pCore 2 ↥B) ∧ IsAlt 5 (ModO2 B) ∧
          ∀ x : ↥B, orderOf x = 3 → ∀ u ∈ CFSG.pCore 2 ↥B, x * u = u * x → u = 1) →
      B₁ = B₂

@[expose] def KGJ4NoA5Block : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSporadic .J4 Y →
    ∀ T : Subgroup Y, IsSylowTwoOf T ⊤ → ∀ B ∈ lFamily T,
      ¬ IsAlt 5 ↥B ∧ ¬ (IsElemAbelianOfRank 2 4 ↥(CFSG.pCore 2 ↥B) ∧ IsAlt 5 (ModO2 B))

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
