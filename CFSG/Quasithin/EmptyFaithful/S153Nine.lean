module

public import CFSG.Quasithin.EmptyFaithful.S1417Glue
public import CFSG.Quasithin.EmptyFaithful.S153Y

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace Hyp153

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem commutator_VZ_Y153 (h113 : StageLemma14113) (h : Hyp153 G T Mc M) :
    ⁅VZ T M, Y153 Mc M⁆ = VZ T M := by
  obtain ⟨q, L₁, L₂, t, -, -, -, -, hS, -⟩ := h.exists_ofourStruct
  have hV := h.elemAbelian
  rw [commutator_eq_map_commV hV ((Y153_le Mc M).trans h.le_normalizer)]
  have e : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := h.autOn_Y153 h113
  rw [e, hS.commV_oTwoUpper]
  exact map_inclMod_top hV

theorem VZ_le_Y153 (h113 : StageLemma14113) (h : Hyp153 G T Mc M) : VZ T M ≤ Y153 Mc M := by
  rw [← h.commutator_VZ_Y153 h113]
  refine Subgroup.commutator_le.mpr fun v hv y hy => ?_
  have hvM : v ∈ M := h.T_le (h.VZ_le_T hv)
  have h1 : v * y * v⁻¹ ∈ Y153 Mc M :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_Y153 Mc M hvM) y).mp hy
  have e : ⁅v, y⁆ = (v * y * v⁻¹) * y⁻¹ := by rw [commutatorElement_def]
  rw [e]
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hy)

theorem VZ_le_pCoreOf_Y153 (h113 : StageLemma14113) (h : Hyp153 G T Mc M) :
    VZ T M ≤ pCoreOf 2 (Y153 Mc M) :=
  le_pCoreOf_of_le_normalizer 2 (h.VZ_le_Y153 h113)
    ((Y153_le Mc M).trans h.le_normalizer) (B2F.isPGroup_of_isElemAbelian h.elemAbelian)

end Hyp153

end CFSG.Quasithin
