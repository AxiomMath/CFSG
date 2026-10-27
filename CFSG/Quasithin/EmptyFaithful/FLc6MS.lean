module

public import CFSG.Quasithin.Background.FLc6Grp
public import CFSG.Quasithin.EmptyFaithful.FLcP0
public import CFSG.Quasithin.EmptyFaithful.FLc5OffTr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uOf1527_le_sup {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hc : Ctx15128 T Mc M Z₁ Z₂ V₁ V₂ L) : uOf1527 Z₂ L ≤ L ⊔ s1516 T Z₁ := by
  have hF := facts_of_ctx hc
  have hZ₂Q := z2_le_q1 hc
  refine conjClosure_le fun l hl z hz => ?_
  have hzS : z ∈ s1516 T Z₁ := hF.QS (hZ₂Q hz)
  have h1 : z * l⁻¹ * z⁻¹ ∈ L := hF.SL z hzS l⁻¹ (L.inv_mem hl)
  have e : l * z * l⁻¹ = (l * (z * l⁻¹ * z⁻¹)) * z := by group
  rw [e]
  exact (L ⊔ s1516 T Z₁).mul_mem (Subgroup.mem_sup_left (L.mul_mem hl h1))
    (Subgroup.mem_sup_right hzS)

theorem input15129MSHyp_holds : Input15129MSHyp := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L n W hc hF hMS3
  obtain ⟨D⟩ := nonempty_p0Setup15129 hc hF
  have hn := hF.n_eq
  have hsqtk : IsSQTKIn (L ⊔ s1516 T Z₁) :=
    IsSQTKIn.mono hc.base.h18.five.2.2.sqtk
      (sup_le (le_of_mem_cComp hc.base.hL.comp) (s1516_le_g1 T Z₁))
  have hUL : uLOf1527 Z₂ L ≤ L ⊔ s1516 T Z₁ :=
    (facts_of_ctx hc.base).ULU.trans (uOf1527_le_sup hc.base)
  obtain ⟨α, hα⟩ := D.exists_isModO2Surj hn
  exact ⟨D.isMSPair_gNode hn hUL hsqtk hMS3, D.kNode_mem_cComp_gNode hn, D.coe_gNode,
    1, ZMod 2, inferInstance, inferInstance, α, by simp, hα⟩

end CFSG.Quasithin
