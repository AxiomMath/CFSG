module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem ggE6Dep_x_not_mem_L {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥L)) : x ∉ L := by
  intro hxL
  obtain ⟨-, -, -, hLx, -⟩ := hcfg.tableB_facts
  have hc : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    exact ((Subgroup.mem_centralizer_iff.mp (hLx l.2)) x rfl).symm
  have hdvd : orderOf (⟨⟨x, hxL⟩, hc⟩ : ↥(Subgroup.center ↥L)) ∣
      Nat.card ↥(Subgroup.center ↥L) := orderOf_dvd_natCard _
  have hord : orderOf (⟨⟨x, hxL⟩, hc⟩ : ↥(Subgroup.center ↥L)) = p := by
    rw [← hcfg.orderOf_x, ← Subgroup.orderOf_coe (⟨⟨x, hxL⟩, hc⟩ : ↥(Subgroup.center ↥L))]
    exact (Subgroup.orderOf_coe (⟨x, hxL⟩ : ↥L)).symm
  exact hZ (hord ▸ hdvd)

end CFSG.StandardType

end
