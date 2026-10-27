module

public import CFSG.LocalAnalysis.WeakClosure81.W16LRootGen
public import CFSG.LocalAnalysis.WeakClosure81.W16LRootCent

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open Subgroup

theorem psuThreeRootFacts_holds :
    PSUThreeRootFacts := by
  intro P _ _ n hP R hR hcard
  obtain ⟨Q, rfl⟩ := hP.exists_sylow_sylowCenter_eq hR hcard
  refine ⟨fun g hg => ?_, fun X hX hXC => ?_⟩
  · obtain ⟨Q', -, hQ'⟩ := sylowCenter_conj_exists Q g
    have hne : Q ≠ Q' := fun h => hg (by rw [← hQ', h])
    refine ⟨by rw [← hQ']; exact hP.isL2Gp_sylowCenter_sup hne, ?_⟩
    obtain ⟨Q'', hQ''⟩ := hP.exists_sylowCenter_sup_eq_top hne
    obtain ⟨h, hh⟩ := exists_conj_eq_sylowCenter Q Q''
    exact ⟨h, by rw [hh, ← hQ']; exact hQ''⟩
  · obtain ⟨Q', hne, hX'⟩ := hP.exists_sylow_centralizer_of_odd Q hX hXC
    obtain ⟨g, hg⟩ := exists_conj_eq_sylowCenter Q Q'
    refine ⟨g, fun h => hne (hP.sylowCenter_injective ?_), by rw [hg]; exact hX'⟩
    rw [← hg, h]

end CFSG.LocalAnalysis.WeakClosure81

end
