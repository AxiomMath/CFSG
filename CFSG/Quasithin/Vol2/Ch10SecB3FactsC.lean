module

public import CFSG.Quasithin.Background.B4ModelsLie

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] def FactCommField : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H R : Subgroup (MulAut V)) (x : MulAut V) (a r : ℕ),
    ((2 ≤ a ∧ BinaryNaturalSL H ⊤ ⊥ 2 a) ∨ BinaryNaturalSz H ⊤ ⊥ a ∨
      (2 ≤ a ∧ BinaryOrthogonalFour H ⊤ ⊥ a)) →
    IsPGroup 2 R → (∀ ρ ∈ R, ∀ h ∈ H, ρ * h * ρ⁻¹ ∈ H) →
    (∃ S : Subgroup (MulAut V), S ≤ R ⊓ H ∧ QuasithinUnique.IsSylowTwoOf S H) →
    r.Prime → r ≠ 2 → ¬ r ∣ Nat.card H → x ^ r = 1 → (∀ h ∈ H, x * h * x⁻¹ ∈ H) →
    (∀ v : V, (∀ ρ ∈ R, ρ v = v) → x v = v) → x = 1

@[expose] def FactBenderOver : Prop :=
  ∀ (K : Type) [Group K] [Finite K],
    ((∃ (F : Type) (_ : Field F) (_ : Finite F) (a : ℕ), 2 ≤ a ∧ Nat.card F = 2 ^ a ∧
        Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
      ∃ n : ℕ, CFSG.Blueprint.SuzukiModel K 2 n) →
    ∀ S X : Subgroup K, QuasithinUnique.IsSylowTwoOf S ⊤ → S ≤ X →
      X ≤ Subgroup.normalizer (S : Set K) ∨ X = ⊤

end CFSG.Quasithin.Vol2.Ch10.SecB
