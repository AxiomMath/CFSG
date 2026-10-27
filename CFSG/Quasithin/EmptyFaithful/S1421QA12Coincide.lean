module

public import CFSG.Quasithin.EmptyFaithful.S1421QA12Lie
public import CFSG.Quasithin.EmptyFaithful.S1421QA12Sp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace QA12

theorem lieBorelCoincide : LieBorelCoincide := by
  intro X _ _ n hn hX U P P' hU hPar heq
  rcases hX with h | h | h
  · obtain ⟨hn2, hle, hcard⟩ := borel_isPSL hn h hU hPar heq
    subst hn2
    exact ⟨h, hle, hcard⟩
  · exact (false_of_isSL3 hn h hU hPar heq).elim
  · exact (false_of_isPSp4 hn h hU hPar heq).elim

theorem lieTorusCoincide : LieTorusCoincide :=
  lieTorusCoincide_of_borel lieSylowLePerfectCore lieBorelCoincide

end QA12

end CFSG.Quasithin
