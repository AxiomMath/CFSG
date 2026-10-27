module

public import CFSG.Quasithin.Background.C2Blocks

public section

namespace CFSG.Quasithin.H13

@[expose] def Lem1211NNParab : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X P D : Subgroup Y) (k m : ℕ) (t : Y),
    (k = 4 ∨ k = 5) → (m = 3 ∨ m = 4) →
    Nonempty (↥X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL k (ZMod 2))) →
    IsParabolic2 X P → ¬ IsBorelIn X P →
    D ≤ P → P ≤ Subgroup.normalizer (D : Set Y) →
    ∀ π : ↥D →* Matrix.SpecialLinearGroup (Fin m) (ZMod 2), Function.Surjective π →
      IsPGroup 2 π.ker →
    t ∈ Subgroup.normalizer (X : Set Y) → t ∈ Subgroup.normalizer (P : Set Y) →
    ∀ htD : t ∈ Subgroup.normalizer (D : Set Y),
    (¬ ∃ z : Matrix.SpecialLinearGroup (Fin m) (ZMod 2), ∀ d : ↥D,
        π ⟨t * d * t⁻¹, (Subgroup.mem_normalizer_iff.mp htD d).mp d.2⟩ = z * π d * z⁻¹) →
      (k = 5 ∧ m = 3 ∧ ¬ ∃ x ∈ X, ∀ y ∈ X, t * y * t⁻¹ = x * y * x⁻¹) ∨
        (k = 4 ∧ m = 4 ∧ P = X)

@[expose] def Lem1211NNG2 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X P : Subgroup Y), IsG2Two ↥X → IsMaxParabolic2 X P →
    ¬ 7 ∣ Nat.card ↥P

@[expose] def Lem1211NNSL3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X P D : Subgroup Y) (F : Type) [Field F] [Fintype F]
    (k m : ℕ), 1 ≤ k → Fintype.card F = 2 ^ k →
    Nonempty (↥X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) → IsMaxParabolic2 X P → D ≤ P →
    (m = 3 ∨ m = 4) → ∀ π : ↥D →* Matrix.SpecialLinearGroup (Fin m) (ZMod 2),
      Function.Surjective π → IsPGroup 2 π.ker → False

end CFSG.Quasithin.H13
