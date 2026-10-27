module

public import CFSG.Quasithin.EmptyFaithful.FLc6MS

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uLOf1527_le_L {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hc : Ctx15128 T Mc M Z₁ Z₂ V₁ V₂ L) :
    uLOf1527 Z₂ L ≤ L := by
  have hF := facts_of_ctx hc
  refine Subgroup.commutator_le.2 fun u hu l hl => ?_
  obtain ⟨l', hl', s, hs, rfl⟩ := FLc.mem_sup_prod_of_conj hF.SL u (uOf1527_le_sup hc hu)
  have h1 : l' * s * l * (l' * s)⁻¹ ∈ L := by
    have e : l' * s * l * (l' * s)⁻¹ = l' * (s * l * s⁻¹) * l'⁻¹ := by group
    rw [e]
    exact L.mul_mem (L.mul_mem hl' (hF.SL s hs l hl)) (L.inv_mem hl')
  have e2 : ⁅l' * s, l⁆ = (l' * s * l * (l' * s)⁻¹) * l⁻¹ := by
    simp [commutatorElement_def, mul_assoc]
  rw [e2]
  exact L.mul_mem h1 (L.inv_mem hl)

end CFSG.Quasithin
