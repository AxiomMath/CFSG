module

public import CFSG.RankThree.GF2n.Stroth80.Sec713O2Steps
import CFSG.RankThree.GF2n.Stroth80.Sec8CentreModel

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG
open scoped commutatorElement


private theorem mem_H0_of_inO2NormPre {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {Z0 : Subgroup G} {x : G}
    (hx : InO2NormPre M Q Z Z0 x) : x ∈ H0 M Z := by
  obtain ⟨hxM, y, -, hy⟩ := hx
  have h1 : ((y : Hbar M Q Z) : Mbar M Q) ∈ bar M Q (NormH0 M Z Z0) :=
    Subgroup.mem_subgroupOf.mp y.2
  rw [hy] at h1
  exact (mk_mem_bar_iff_sec4 hc.Q_le_H0 ⟨x, hxM⟩).mp (MbarPrimeLe M Q Z Z0 h1)

theorem step713CentreFix_of (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement) :
    Step713CentreFixStatement := by
  intro G _ _ M Q Z B _ hc n t hs _ Z0 hZ0 x hx _ hxV _
  exact commZ0_mem_Q_of_centralizes_Vt hc hZ0
    (fun z hz w hw => (hZc G M Q Z B hc n t hs Z0 hZ0 z hz).2 w hw)
    (hZV G M Q Z B hc n t hs Z0 hZ0) (mem_H0_of_inO2NormPre hc hx) hxV

end CFSG.RankThree.GF2n.Stroth80

end
