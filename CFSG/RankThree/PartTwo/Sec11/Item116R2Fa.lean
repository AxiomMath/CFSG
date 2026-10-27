module

public import CFSG.RankThree.PartTwo.Sec11.Item116R2FaDefs
public import CFSG.RankThree.PartTwo.Sec11.Item116R2FaAlt
public import CFSG.RankThree.PartTwo.Sec11.Item116R2FaON
public import CFSG.RankThree.PartTwo.Sec11.Item116R2FaL3

public section

open CFSG

namespace CFSG.RankThree.PartTwo.Sec11

section Certified


theorem threeCentralCoverOmegaNonabelian'_holds : ThreeCentralCoverOmegaNonabelian' := by
  intro J _ _ hq hZ3 hZ hA S
  obtain hL3 | h6 | h7 | hM | hO := hA
  · obtain ⟨p, e, hp, he, hb, hpi⟩ := hL3
    haveI := hp
    exact fa_L3 hq hZ3 hZ he hb hpi S
  · obtain ⟨e⟩ := h6
    exact fa_alt6 hq hZ3 hZ e S
  · obtain ⟨e⟩ := h7
    exact fa_alt7 hq hZ3 hZ e S
  · obtain ⟨e⟩ := hM
    exact fa_M22 hq hZ3 hZ e S
  · obtain ⟨e⟩ := hO
    exact fa_ON hq hZ3 hZ e S

end Certified

end CFSG.RankThree.PartTwo.Sec11
