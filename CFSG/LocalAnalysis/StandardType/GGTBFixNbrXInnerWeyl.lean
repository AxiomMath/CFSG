module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteNbrWeyl
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrDefs
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL43

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTBFixNbrXInput_of_innerWeyl (hW : GGNbrInnerWeylInput) : GGTBFixNbrXInput := by
  intro G _ _ p B Bs x L D J hcfg _ hI _ y K hN _ _ b hbx hfix
  by_contra hb1
  have hp : p.Prime := hcfg.tableB_facts.1
  have : Fact p.Prime := ⟨hp⟩
  have hx : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hxp : x ^ p = 1 := hcfg.tableB_facts.2.1.2 x hx
  obtain ⟨φ, hφ, hφx⟩ := FrameRoute.exists_automizer_moves_x_of_innerWeyl hW hcfg hI hN hx
  have hzc : Subgroup.zpowers (b : G) = Subgroup.zpowers x :=
    zpowers_eq_of_mem_of_ne_one hxp hbx hb1
  have hxmem : x ∈ Subgroup.zpowers (b : G) := by
    rw [hzc]
    exact Subgroup.mem_zpowers x
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxmem
  have hbpow : b ^ k = ⟨x, hx⟩ := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)
  have hφb : φ b = b := hfix φ hφ
  exact hφx (by rw [← hbpow, map_zpow φ b k, hφb])

end CFSG.StandardType

end
