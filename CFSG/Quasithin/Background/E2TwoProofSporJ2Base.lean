
module

public import CFSG.Quasithin.Background.E2TwoProofSporGen
public import CFSG.Quasithin.Background.E2TwoProofSporJ2Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatO2
public import CFSG.Quasithin.Background.E2TwoProofSporJ2KInputs
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

@[expose] public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat

namespace E2P

namespace SporB

section J2

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.E2P.SporB.J2Lat CFSG.Sporadic.J2

theorem j2_delta_valid : CodeSetValid 315 j2Delta := by
  have h : ∀ l ∈ j2Sets, PtValid 315 l := by decide
  refine ⟨sortN_sorted _, fun c hc => ?_⟩
  rw [j2Delta, mem_sortN] at hc
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
  exact ⟨l, h l hl, rfl⟩

theorem j2_ta' : (tab 315 (a : J)).toArray = j2ta.toArray := by
  rw [j2_tab_a]

theorem j2_tb' : (tab 315 (b : J)).toArray = j2tb.toArray := by
  rw [j2_tab_b]

theorem j2_sGens :
    genTabs 315 j2Sg = j2STabs ∧ Nat.card (Subgroup.closure {x | x ∈ j2Sg}) = 2 ^ 7 := by
  have hc : BaseCertS 315 (List.range 315)
      (slpTabsA (tab 315 (a : J)).toArray (tab 315 (b : J)).toArray j2Prog) j2Qp
      143 181 185 183 187 j2Enum.1 j2Enum.2.1 j2Enum.2.2 7 := by
    rw [j2_ta', j2_tb']
    exact j2_cert
  have := sGens_of_baseCertS (n := 315) (List.range 315) (fun b hb => List.mem_range.mp hb)
    base_of_faithful (a : J) (b : J) j2Prog j2_valid j2Qp 143 181 185 183 187 j2Enum.1
    j2Enum.2.1 j2Enum.2.2 7 hc
  refine ⟨?_, this.2⟩
  rw [j2Sg, this.1, j2_ta', j2_tb']
  rfl

end J2

end SporB

end E2P

end CFSG.Quasithin
