module

import CFSG.LocalAnalysis.UniquenessCase.UC22K331Over
import CFSG.Quasithin.EmptyFaithful.S146zYFSJ2
import CFSG.Quasithin.Vol2.KGFactAutSylowM22
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.UC22K331Basic
public import CFSG.Quasithin.Vol2.KGFactSporLatInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open CFSG.Blueprint.NativeSporadic (Carrier)

theorem k331Idx_j2
    (hbr : Nonempty (Carrier .J2 ≃* TauCeti.SporadicName.J2.Group)) :
    K331Idx (.sporadic .J2) := by
  obtain ⟨b⟩ := hbr
  intro L _ _ hs _ ⟨e⟩
  refine k331At_of_overgroups hs fun T Y hT hTY hY => ?_
  rcases CFSG.Quasithin.S146zY.j2_overgroups ⟨e.trans b.symm⟩ hT hTY with h | h | h | h | h
  · exact absurd h hY
  all_goals rw [h]; norm_num

theorem k331Idx_m22
    (hbr : Nonempty (Carrier .M22 ≃* TauCeti.SporadicName.M22.Group)) :
    K331Idx (.sporadic .M22) := by
  obtain ⟨b⟩ := hbr
  intro L _ _ hs _ ⟨e⟩
  refine k331At_of_overgroups hs fun T Y hT hTY hY => ?_
  rcases CFSG.Quasithin.H13.KGSporLat.m22_overgroups ⟨e.trans b.symm⟩ hT hTY with
    h | ⟨m, hm, hc, -⟩
  · exact absurd h hY
  · simp only [CFSG.Quasithin.H13.KGSporLat.m22Mems, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    rw [hc]
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> decide

theorem k331Idx_hs
    (hbr : Nonempty (Carrier .HS ≃* TauCeti.SporadicName.HS.Group)) :
    K331Idx (.sporadic .HS) := by
  obtain ⟨b⟩ := hbr
  intro L _ _ hs _ ⟨e⟩
  refine k331At_of_overgroups hs fun T Y hT hTY hY => ?_
  rcases CFSG.QuasithinUnique.Ch1.SporLat.HS.hs_overgroups ⟨e.trans b.symm⟩ hT hTY with
    h | ⟨m, hm, hc, -⟩
  · exact absurd h hY
  · simp only [CFSG.QuasithinUnique.Ch1.SporLat.HS.hsMems, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    rw [hc]
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> decide

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
