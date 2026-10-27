module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res4ProofSix
public import CFSG.RankThree.PartTwo.Sec4.RonanK423Sp4
public import CFSG.RankThree.PartTwo.Sec4.RonanK423U4
public import CFSG.RankThree.PartTwo.Sec4.RonanK423G2
public import CFSG.RankThree.PartTwo.Sec4.RonanK423D4
public import CFSG.RankThree.PartTwo.Sec4.RonanK423ReeF4

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.RankThree.PartTwo.Sec4.RonanK423

theorem k423Inner46SixLieRest_holds
    : K423Inner46SixLieRest := by
  intro X _ _ hX hq hZ _
  rcases hX with ⟨n, hn, hSp | ⟨hev, hU⟩⟩ | ⟨f, hG2 | hD4 | hF4⟩
  · obtain ⟨e⟩ := hSp
    exact census423_of_sp4 hn e hq
  · obtain ⟨e⟩ := hU
    exact census423_of_u4 hn hev e hq hZ
  · exact census423_of_g2 hG2 hq hZ
  · exact census423_of_trialityD4 hD4 hq hZ
  · exact census423_of_twistedF4 hF4

end CFSG.RankThree.PartTwo.Sec4
