module

import CFSG.Quasithin.Background.F918C4
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_e3_l3_inner_of_stab {L : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hI : BinaryNaturalSL L I Z 3 1) {τ : MulAut W}
    (hτN : τ ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hτI : ∀ u ∈ I, τ u ∈ I) (hτZ : ∀ z ∈ Z, τ z ∈ Z) :
    ∃ γ ∈ L, ∀ l ∈ L, τ * l * τ⁻¹ = γ * l * γ⁻¹ := by
  have hmap : ∀ {Y : Subgroup W}, (∀ y ∈ Y, τ y ∈ Y) → Y.map τ.toMonoidHom = Y := by
    intro Y hY
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hY y hy
    · exact (Subgroup.card_map_of_injective (f := τ.toMonoidHom) τ.injective).ge
  obtain ⟨l₀, hl₀, hc⟩ := A6Twist.inner_of_stable_nat3 hI hτN (hmap hτI) (hmap hτZ)
  refine ⟨l₀, hl₀, fun l hl => ?_⟩
  have h1 := hc (l₀ * l * l₀⁻¹) (L.mul_mem (L.mul_mem hl₀ hl) (L.inv_mem hl₀))
  calc τ * l * τ⁻¹ = (τ * l₀⁻¹) * (l₀ * l * l₀⁻¹) * (τ * l₀⁻¹)⁻¹ := by group
    _ = (l₀ * l * l₀⁻¹) * (τ * l₀⁻¹) * (τ * l₀⁻¹)⁻¹ := by rw [h1]
    _ = l₀ * l * l₀⁻¹ := by group

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
