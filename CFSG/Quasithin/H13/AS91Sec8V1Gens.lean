module

public import CFSG.Quasithin.H13.AS91Sec8V1AutData
public import CFSG.Quasithin.H13.AS91Sec8V1Defs
public import CFSG.Quasithin.H13.AS91Sec7Eight

public section

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH (M24g S24)
open scoped Pointwise
open CFSG.Monster.Code (mem_AutPerm_of_basis)

private theorem sxA_basis :
    ∀ i : Fin 12, CFSG.Monster.Code.B i ∘ ⇑sxA ∈ CFSG.Monster.Code.C := by
  decide +kernel

private theorem sxA_basis' :
    ∀ i : Fin 12, CFSG.Monster.Code.B i ∘ ⇑sxA⁻¹ ∈ CFSG.Monster.Code.C := by
  decide +kernel

private theorem sxB_basis :
    ∀ i : Fin 12, CFSG.Monster.Code.B i ∘ ⇑sxB ∈ CFSG.Monster.Code.C := by
  decide +kernel

private theorem sxB_basis' :
    ∀ i : Fin 12, CFSG.Monster.Code.B i ∘ ⇑sxB⁻¹ ∈ CFSG.Monster.Code.C := by
  decide +kernel

theorem sxA_mem_M24 : sxA ∈ M24g := mem_AutPerm_of_basis sxA_basis sxA_basis'

theorem sxB_mem_M24 : sxB ∈ M24g := mem_AutPerm_of_basis sxB_basis sxB_basis'

theorem sxA_mem : sxA ∈ sextStab := by
  refine ⟨sxA_mem_M24, ?_⟩
  change sxA • sextFin 0 = sextFin 0
  rw [sextFin_zero_eq]
  decide +kernel

theorem sxB_mem : sxB ∈ sextStab := by
  refine ⟨sxB_mem_M24, ?_⟩
  change sxB • sextFin 0 = sextFin 0
  rw [sextFin_zero_eq]
  decide +kernel

end CFSG.Quasithin.H13.AS91.M24G
