module

public import CFSG.Quasithin.Background.F918P0

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace S153M

section TwoDef

variable {V : Type} [CommGroup V]

@[expose] def TwoB56 (X L₁ L₂ : Subgroup (MulAut V)) : Prop :=
  ffJ X = L₁ ⊔ L₂ ∧ ∃ W₁ W₂ : Subgroup V, fixV (L₁ ⊔ L₂) ≤ W₁ ∧ fixV (L₁ ⊔ L₂) ≤ W₂ ∧
    W₁ ⊔ W₂ = ⊤ ∧ W₁ ⊓ W₂ = fixV (L₁ ⊔ L₂) ∧ B56Piece L₁ W₁ (fixV (L₁ ⊔ L₂)) ∧
      B56Piece L₂ W₂ (fixV (L₁ ⊔ L₂))

@[expose] def KsCoverTwo (L : Type) [Group L] : Prop :=
  ∃ (Y : Type) (_ : Group Y) (Ks : Subgroup Y) (n : ℕ) (σ : L →* ↥Ks),
    3 ≤ n ∧ Odd n ∧ (IsPSL 2 2 n ↥Ks ∨ IsSz n ↥Ks) ∧ Function.Surjective σ ∧ σ.ker ≤ Subgroup.center L

@[expose] def TwoNat (L₁ L₂ : Subgroup (MulAut V)) (τ : MulAut V) : Prop :=
  (∃ m : ℕ, 2 ≤ m ∧
      BinaryNaturalSL L₁ (commV L₁ ⊔ fixV (L₁ ⊔ L₂)) (fixV (L₁ ⊔ L₂)) 2 m) ∧
    (∃ m : ℕ, 2 ≤ m ∧
      BinaryNaturalSL L₂ (commV L₂ ⊔ fixV (L₁ ⊔ L₂)) (fixV (L₁ ⊔ L₂)) 2 m) ∧
    (⊤ : Subgroup V) = (commV L₁ ⊔ fixV (L₁ ⊔ L₂)) ⊔ (commV L₂ ⊔ fixV (L₁ ⊔ L₂)) ∧
    (commV L₁ ⊔ fixV (L₁ ⊔ L₂)) ⊓ (commV L₂ ⊔ fixV (L₁ ⊔ L₂)) ≤ fixV (L₁ ⊔ L₂) ∧
    IsSumMod (fixV (L₁ ⊔ L₂)) (commV L₁) ((commV L₁).map τ.toMonoidHom) ⊤ ∧
    commV L₁ ≤ fixV L₂ ∧ commV L₂ ≤ fixV L₁

end TwoDef

end S153M

end CFSG.Quasithin
