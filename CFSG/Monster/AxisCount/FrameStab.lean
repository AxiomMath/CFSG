module

public import CFSG.Monster.VisQuot.Simple

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.VisCert
  CFSG.Monster.VisQuot

@[expose] noncomputable def psiVis : Gvis →* GLV := opQHom.comp piVis

theorem psiVis_thetaEquiv (p : Pvis) :
    psiVis ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ = modTwoUnit p.1.2 := by
  rw [psiVis, MonoidHom.comp_apply, piVis_thetaEquiv, opQHom_op_mk]

theorem psiVis_smul_thetaEquiv (p : Pvis) (x : L2) :
    psiVis ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩ • x = modTwoEnd p.1.2 x := by
  rw [psiVis_thetaEquiv]
  rfl

theorem range_psiVis :
    psiVis.range = Hvis := by
  rw [psiVis, MonoidHom.range_comp, range_piVis, ← MonoidHom.range_eq_map, range_opQHom]

theorem psiVis_mem_Hvis
    (g : Gvis) : psiVis g ∈ Hvis :=
  range_psiVis ▸ MonoidHom.mem_range.2 ⟨g, rfl⟩

@[expose] noncomputable def Nfr : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) :=
  ((MulAction.stabilizer GLV twoΩCls).comap psiVis).map Gvis.subtype

theorem mem_Nfr {g : SpaceB ≃ₗ[ℚ] SpaceB} :
    g ∈ Nfr ↔ ∃ hg : g ∈ Gvis, psiVis ⟨g, hg⟩ • twoΩCls = twoΩCls := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g'.2, hg'⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem Nfr_le_Gvis : Nfr ≤ Gvis := fun _ hg => (mem_Nfr.1 hg).1

end CFSG.Monster.AxisCount
