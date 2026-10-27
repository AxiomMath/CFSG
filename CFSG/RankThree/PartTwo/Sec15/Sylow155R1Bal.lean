module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Defs
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1L65
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1OddL2
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1OddL3
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1J1
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Small
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1L2Odd

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

theorem step155HostE0WRes1Type_oddL2 : Step155HostE0WRes1Type Res1OddL2Type := by
  refine step155HostE0WRes1Type_of_autCent fun Y _ _ _ hY => ?_
  obtain ⟨p, f, hp, hp2, -, hf, ⟨e⟩⟩ := hY
  exact Res1AutCent.of_mulEquiv e (res1AutCent_projSL_two_of_odd hp2 hf)

theorem step155HostE0WRes1Type_oddL3 : Step155HostE0WRes1Type Res1OddL3Type := by
  refine step155HostE0WRes1Type_of_autCent fun Y _ _ _ hY => ?_
  rcases hY with ⟨p, f, hp, hp2, hf, -, ⟨e⟩⟩ | ⟨p, f, hp, hp2, hf, hq, ⟨e⟩⟩
  · exact Res1AutCent.of_mulEquiv e (res1AutCent_projSL_three_of_odd hp2 hf)
  · exact Res1AutCent.of_mulEquiv e (res1AutCent_projSU_three_of_odd hp2 hf hq)

theorem step155HostE0WRes1Type_j1 :
    Step155HostE0WRes1Type Res1J1Type := by
  refine step155HostE0WRes1Type_of_autCent fun Y _ _ _ hY => ?_
  obtain ⟨e⟩ := hY
  exact Res1AutCent.of_mulEquiv e res1AutCent_J1

theorem step155HostE0WRes1Type_small : Step155HostE0WRes1Type Res1SmallType := by
  refine step155HostE0WRes1Type_of_autCent fun Y _ _ _ hY => ?_
  rcases hY with h | h
  · obtain ⟨e⟩ := h
    exact Res1AutCent.of_mulEquiv e res1AutCent_projSL_two_four
  · obtain ⟨e⟩ := h
    exact Res1AutCent.of_mulEquiv e res1AutCent_projSL_three_two

theorem step155HostE0WRes1Type_l2Odd : Step155HostE0WRes1Type Res1L2OddType := by
  refine step155HostE0WRes1Type_of_autCent fun Y _ _ _ hY => ?_
  obtain ⟨n, hn, ⟨e⟩⟩ := hY
  exact Res1AutCent.of_mulEquiv e (res1AutCent_projSL_two_odd hn)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
