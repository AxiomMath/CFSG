module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutFusWeyl

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

section Cent

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2]

theorem torus_trans_Xc : ∀ w ∈ Xc K, w ≠ 1 → ∃ h ∈ torusSub Tag.G2 K, h * xc 1 * h⁻¹ = w := by
  intro w hw hne
  obtain ⟨s, rfl⟩ := mem_Xc_iff.1 hw
  have hs : s ≠ 0 := fun h => hne (h ▸ xc_zero)
  refine ⟨dT K Cls.iA (Units.mk0 s hs), dT_mem_torusSub _ _, ?_⟩
  rw [dT_xc, Units.val_mk0, mul_one]

end Cent

end CFSG.Quasithin.H13.F431.G2
