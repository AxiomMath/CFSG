module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearUnitaryLine
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Background.Huppert.II.theorem_10_12

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowth

open Matrix CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.External

universe u

variable {K : Type u} [Field K] [CharP K 2]

theorem unitary_coordinate_square_one_iff {n : ℕ} (J : HermitianForm n K)
    (z : hermitianUnipotentCoord J) :
    z ^ 2 = 1 ↔ z.1.1 = 0 := by
  constructor
  · intro h
    have hsecond := congrArg (fun w : hermitianUnipotentCoord J => w.1.2) h
    rw [pow_two] at hsecond
    change z.1.2 + z.1.2 - z.1.1 * J.conj z.1.1 = 0 at hsecond
    have hprod : z.1.1 * J.conj z.1.1 = 0 := by
      simpa only [CharTwo.add_self_eq_zero, zero_sub, neg_eq_zero] using hsecond
    rcases mul_eq_zero.mp hprod with hz | hz
    · exact hz
    · exact J.conj.injective (hz.trans (map_zero J.conj).symm)
  · intro hz
    rw [pow_two]
    change hermitianUnipotentMul J z z = hermitianUnipotentOne J
    apply Subtype.ext
    apply Prod.ext
    · change z.1.1 + z.1.1 = 0
      rw [hz, zero_add]
    · change z.1.2 + z.1.2 - z.1.1 * J.conj z.1.1 = 0
      rw [CharTwo.add_self_eq_zero, hz, zero_mul, sub_zero]

theorem unitary_projective_root_square_one_iff (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (z : hermitianUnipotentCoord J) :
    (hermitianUnipotentPSU J hJ z) ^ 2 = 1 ↔ z.1.1 = 0 := by
  have hinj := CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ
  constructor
  · intro h
    apply (unitary_coordinate_square_one_iff J z).mp
    apply hinj
    simpa only [map_pow, map_one] using h
  · intro h
    have hsquare := (unitary_coordinate_square_one_iff J z).mpr h
    simpa only [map_pow, map_one] using congrArg (hermitianUnipotentPSU J hJ) hsquare

theorem unitary_projective_root_involution_iff (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (z : hermitianUnipotentCoord J) :
    orderOf (hermitianUnipotentPSU J hJ z) = 2 ↔
      z.1.1 = 0 ∧ z.1.2 ≠ 0 := by
  rw [orderOf_eq_prime_iff, unitary_projective_root_square_one_iff]
  constructor
  · rintro ⟨hfirst, hne⟩
    refine ⟨hfirst, ?_⟩
    intro hsecond
    apply hne
    have hz : z = 1 := by
      apply Subtype.ext
      exact Prod.ext hfirst hsecond
    rw [hz, map_one]
  · rintro ⟨hfirst, hsecond⟩
    refine ⟨hfirst, ?_⟩
    intro h
    have hz : z = 1 := CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ
      (h.trans (map_one (hermitianUnipotentPSU J hJ)).symm)
    exact hsecond (congrArg (fun w : hermitianUnipotentCoord J => w.1.2) hz)

theorem unitary_entire_root_middle_set (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (((hermitianUnipotentPSU J hJ).range ⊓ unitaryMiddleStabilizer J :
        Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set _) =
      {g : ProjectiveSpecialUnitaryMatrixGroup J |
        g ∈ (hermitianUnipotentPSU J hJ).range ∧ (g = 1 ∨ orderOf g = 2)} := by
  ext g
  constructor
  · rintro ⟨⟨z, rfl⟩, hmiddle⟩
    have hfirst := (unitary_root_mem_middle_iff J hJ z).mp hmiddle
    refine ⟨⟨z, rfl⟩, ?_⟩
    by_cases hsecond : z.1.2 = 0
    · left
      have hz : z = 1 := by
        apply Subtype.ext
        exact Prod.ext hfirst hsecond
      rw [hz, map_one]
    · exact Or.inr ((unitary_projective_root_involution_iff J hJ z).mpr
        ⟨hfirst, hsecond⟩)
  · rintro ⟨hg, horder⟩
    refine ⟨hg, ?_⟩
    rcases horder with rfl | horder
    · exact (unitaryMiddleStabilizer J).one_mem
    · obtain ⟨z, rfl⟩ := hg
      exact (unitary_root_mem_middle_iff J hJ z).mpr
        ((unitary_projective_root_involution_iff J hJ z).mp horder).1

theorem unitary_entire_root_involutions_fix_middle (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {g : ProjectiveSpecialUnitaryMatrixGroup J}
    (hg : g ∈ (hermitianUnipotentPSU J hJ).range) (horder : orderOf g = 2) :
    g ∈ unitaryMiddleStabilizer J := by
  obtain ⟨z, rfl⟩ := hg
  exact (unitary_root_mem_middle_iff J hJ z).mpr
    ((unitary_projective_root_involution_iff J hJ z).mp horder).1

end CFSG.ShultStronglyClosedTI.TwoCoreGrowth
