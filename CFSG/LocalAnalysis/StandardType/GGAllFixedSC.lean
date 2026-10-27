module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8

public section

namespace CFSG.StandardType.SecFiveL1Solv

section CentralizerPComplement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G}

theorem hasNormalPComplement_centralizer_of_ggBstar
    (hp : p.Prime) (hp2 : p ≠ 2) (hBs : GGBstar p B Bs) :
    CFSG.HasNormalPComplement p (Subgroup.centralizer (Bs : Set G)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine CFSG.HardMathSupport.Timmesfeld.ComponentBalance.hasNormalPComplement_of_central_order_p
    hp2 ?_
  intro z hz
  have hzord : orderOf (z : G) = p := by
    rw [Subgroup.orderOf_coe]
    exact hz
  have hzp : (z : G) ^ p = 1 := by
    rw [← hzord]
    exact pow_orderOf_eq_one (z : G)
  have hzB : (z : G) ∈ Bs := hBs.2.2.2 (z : G) z.2 hzp
  rw [Subgroup.mem_center_iff]
  intro c
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.1 c.2 (z : G) hzB).symm

end CentralizerPComplement

end CFSG.StandardType.SecFiveL1Solv
