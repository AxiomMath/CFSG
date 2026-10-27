module

public import CFSG.RankThree.GF2n.Tim79aCitedAS
public import CFSG.Sporadic.J2.Representations.Sylow5Normalizer
public import CFSG.RepresentationTheory.GF2.FiveSquaredOrderThreeMatrix


public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Blueprint
open CFSG.Sporadic.Bridge.J2
open CFSG.Sporadic.J2.Sylow5


noncomputable def aJ : NativeSporadic.J2 := nativeEquiv.symm a0

noncomputable def bJ : NativeSporadic.J2 := nativeEquiv.symm b0

noncomputable def gJ : NativeSporadic.J2 := nativeEquiv.symm g0

theorem aJ_pow_five : aJ ^ 5 = 1 := by
  have := congrArg nativeEquiv.symm a0_5
  simpa [aJ, map_pow] using this

theorem bJ_pow_five : bJ ^ 5 = 1 := by
  have := congrArg nativeEquiv.symm b0_5
  simpa [bJ, map_pow] using this

theorem aJbJ_comm : aJ * bJ = bJ * aJ := by
  have := congrArg nativeEquiv.symm a0b0_comm
  simpa [aJ, bJ, map_mul] using this

theorem gJ_pow_three : gJ ^ 3 = 1 := by
  have := congrArg nativeEquiv.symm g0_3
  simpa [gJ, map_pow] using this

theorem aJ_ne_one : aJ ≠ 1 := by
  intro h
  apply a0_ne_one
  have := congrArg nativeEquiv h
  simpa [aJ] using this

theorem bJ_ne_pow (i : ℕ) : bJ ≠ aJ ^ i := by
  intro h
  apply b0_not_pow i
  have := congrArg nativeEquiv h
  simpa [aJ, bJ, map_pow] using this

theorem hgaJ : gJ * aJ * gJ⁻¹ = aJ ^ 4 * bJ ^ 2 := by
  have := congrArg nativeEquiv.symm hga0
  simpa [aJ, bJ, gJ, map_mul, map_pow] using this

theorem hgbJ : gJ * bJ * gJ⁻¹ = aJ ^ 2 := by
  have := congrArg nativeEquiv.symm hgb0
  simpa [aJ, bJ, gJ, map_mul, map_pow] using this

theorem hgncJ : gJ * aJ * gJ⁻¹ ≠ aJ ∨ gJ * bJ * gJ⁻¹ ≠ bJ := by
  right
  rw [hgbJ]
  intro h
  apply bJ_ne_pow 2
  simpa using h.symm

theorem AschbacherHJRepresentationStatement_proof : AschbacherHJRepresentationStatement := by
  unfold AschbacherHJRepresentationStatement
  intro n ρ hinj
  exact CFSG.RepresentationTheory.GF2.twelve_le_of_injective ρ hinj
    aJ_pow_five aJ_ne_one bJ_pow_five aJbJ_comm bJ_ne_pow gJ_pow_three
    ⟨4, 2, hgaJ⟩ ⟨2, 0, by simpa using hgbJ⟩ hgncJ

end CFSG.RankThree.GF2n.Tim79a
