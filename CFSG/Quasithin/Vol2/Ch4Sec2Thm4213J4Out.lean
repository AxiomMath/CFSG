module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4Defs
public import CFSG.Quasithin.Vol2.KGFactHeInspJ4

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Sporadic.J4

theorem j4OutTrivial_holds :
    J4OutTrivial := by
  intro X _ ⟨e⟩ φ
  obtain ⟨g, hg⟩ := KGInsp.j4_all_inner (e.trans (seedEquiv (j4Facts).mat)) φ
  exact ⟨g, fun y => by rw [hg]; rfl⟩

end CFSG.Quasithin.H13.Ch4
