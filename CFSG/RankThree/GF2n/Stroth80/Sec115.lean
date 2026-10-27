module

public import CFSG.RankThree.GF2n.Stroth80.Sec115J2
public import CFSG.Timmesfeld.RootInvolutionDegenerate
import CFSG.RankThree.GF2n.Stroth80.Sec112

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

theorem stroth115_holds : Stroth115Statement := by
  intro G' _ _ M' Q' Z' B' _ hc n hw hn ha2
  obtain ⟨y, hy⟩ := hc.exists_isLBTorus
  obtain ⟨a, ha, hA⟩ := ha2
  obtain ⟨hcls, hroot, hgen, h2, hDZ⟩ :=
    hc.ebarIn_rootData hw hn ⟨a, ha, hA⟩ stroth112_holds
  rcases CFSG.Timmesfeld.lieModel_quotient_center_or_exception hcls hroot hgen
    (hc.ebarIn_meetsSq ha hA hy) h2 hDZ with h | ⟨hnd, hU | hA6 | hJ⟩
  · exact h
  · exact absurd hU (hc.not_lieModel_xbarMod_psu_three_three hw hn ⟨a, ha, hA⟩ hy)
  · exact absurd hA6 (not_nonempty_iff.mpr
      (hc.isEmpty_xbarMod_mulEquiv_alt_six hw hn ⟨a, ha, hA⟩ hy))
  · obtain ⟨d, hd, e, he, hde⟩ := hnd
    have hde' : orderOf ((d : Mbar M' Q') * (e : Mbar M' Q')) = 4 := by
      rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]
      exact hde
    exact absurd hJ
      (hc.not_isSporadic_J2_xbarMod hw hn ⟨a, ha, hA⟩ ⟨d, hd, e, he, hde'⟩)

end CFSG.RankThree.GF2n.Stroth80
