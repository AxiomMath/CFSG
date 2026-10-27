module

public import CFSG.Quasithin.Background.B5Statement

public section

namespace CFSG.Quasithin.H13

@[expose] def Lem1211NNMod : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (G₀ X P D : Subgroup (MulAut V)) (τ : MulAut V),
    Nonempty (↥X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2))) →
    B51Part1 G₀ X → B51Part2 X →
    τ ∈ Subgroup.normalizer (X : Set (MulAut V)) →
    (¬ ∃ x ∈ X, ∀ y ∈ X, τ * y * τ⁻¹ = x * y * x⁻¹) →
    IsParabolic2 X P → τ ∈ Subgroup.normalizer (P : Set (MulAut V)) →
    D ≤ P → P ≤ Subgroup.normalizer (D : Set (MulAut V)) →
    ∀ π : ↥D →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), Function.Surjective π →
      IsPGroup 2 π.ker →
    ∀ hτD : τ ∈ Subgroup.normalizer (D : Set (MulAut V)),
    (¬ ∃ z : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), ∀ d : ↥D,
        π ⟨τ * d * τ⁻¹, (Subgroup.mem_normalizer_iff.mp hτD d).mp d.2⟩ = z * π d * z⁻¹) →
      ∀ v : V, (∀ d : ↥D, d ∈ π.ker → (d : MulAut V) v = v) → ∀ d : ↥D, (d : MulAut V) v = v

end CFSG.Quasithin.H13
