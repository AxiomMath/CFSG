module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.BorelTits.Kempf
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor
public import CFSG.Quasithin.EmptyFaithful.S152O4Mod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E

section Coset

variable {G : Type*} [Group G] [Finite G]

theorem exists_fixed_in_coset {p : ℕ} [Fact p.Prime] {D V : Subgroup G} (hD : IsPGroup p D)
    (hVp : ¬ p ∣ Nat.card V) {x : G} (hinv : ∀ d ∈ D, x⁻¹ * (d * x * d⁻¹) ∈ V)
    (hVD : ∀ d ∈ D, ∀ v ∈ V, d * v * d⁻¹ ∈ V) :
    ∃ y : G, x⁻¹ * y ∈ V ∧ ∀ d ∈ D, d * y * d⁻¹ = y := by
  let X : Type _ := {y : G // x⁻¹ * y ∈ V}
  have hX : ∀ (d : D) (y : X), x⁻¹ * ((d : G) * (y : G) * (d : G)⁻¹) ∈ V := by
    intro d y
    have h1 := hinv d d.2
    have h2 := hVD d d.2 _ y.2
    have e : x⁻¹ * ((d : G) * (y : G) * (d : G)⁻¹) =
        (x⁻¹ * ((d : G) * x * (d : G)⁻¹)) * ((d : G) * (x⁻¹ * (y : G)) * (d : G)⁻¹) := by group
    rw [e]
    exact V.mul_mem h1 h2
  let _ : MulAction D X :=
    { smul := fun d y => ⟨(d : G) * (y : G) * (d : G)⁻¹, hX d y⟩
      one_smul := fun y => Subtype.ext (by
        show ((1 : D) : G) * (y : G) * ((1 : D) : G)⁻¹ = y
        simp)
      mul_smul := fun d₁ d₂ y => Subtype.ext (by
        show ((d₁ * d₂ : D) : G) * (y : G) * ((d₁ * d₂ : D) : G)⁻¹ =
          (d₁ : G) * ((d₂ : G) * (y : G) * (d₂ : G)⁻¹) * (d₁ : G)⁻¹
        simp [mul_assoc]) }
  have hcard : Nat.card X = Nat.card V := by
    refine Nat.card_congr ⟨fun y => ⟨x⁻¹ * (y : G), y.2⟩, fun v => ⟨x * (v : G), by simp⟩, ?_, ?_⟩
    · intro y
      apply Subtype.ext
      simp
    · intro v
      apply Subtype.ext
      simp
  have hmod := hD.card_modEq_card_fixedPoints X
  have hne : Nat.card (MulAction.fixedPoints D X) ≠ 0 := by
    intro h0
    rw [h0, hcard] at hmod
    exact hVp ((Nat.modEq_zero_iff_dvd).1 hmod)
  have hpos : 0 < Nat.card (MulAction.fixedPoints D X) := Nat.pos_of_ne_zero hne
  obtain ⟨⟨y, hy⟩⟩ := (Nat.card_pos_iff.1 hpos).1
  refine ⟨(y : G), y.2, fun d hd => ?_⟩
  have := hy ⟨d, hd⟩
  exact congrArg Subtype.val this

end Coset

end S153E

end CFSG.Quasithin
