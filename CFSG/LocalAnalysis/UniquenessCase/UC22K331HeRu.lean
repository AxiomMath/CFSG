module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate

public import CFSG.LocalAnalysis.UniquenessCase.UC22K331Fams
import CFSG.LocalAnalysis.UniquenessCase.UC22K331Over
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open TauCeti
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.QuasithinUnique.Ch1.SporLat.He (he_overgroups heMems)
open CFSG.QuasithinUnique.Ch1.SporLat.Ru (ru_overgroups ruMems)

theorem k331_heRu
    (hbridge : ∀ s : SporadicName, Nonempty (Carrier s ≃* s.Group)) : K331Fam K331HeRu := by
  intro i hi
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨d, hv⟩⟩ | s
  · exact False.elim hi
  · exact False.elim hi
  · exact False.elim hi
  · intro L _ _ hs _ ⟨e⟩
    obtain ⟨b⟩ := hbridge s
    have e' : L ≃* Carrier s := e.trans b.symm
    refine k331At_of_overgroups hs fun T Y hT hTY hY => ?_
    rcases hi with rfl | rfl
    · rcases he_overgroups ⟨e'⟩ hT hTY with h | ⟨m, hm, hord, -, -⟩
      · exact absurd h hY
      · rw [hord]
        simp only [heMems, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    · rcases ru_overgroups ⟨e'⟩ hT hTY with h | ⟨m, hm, hord, -, -⟩
      · exact absurd h hY
      · rw [hord]
        simp only [ruMems, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl <;> norm_num

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
