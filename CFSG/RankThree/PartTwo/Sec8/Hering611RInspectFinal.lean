module

public import CFSG.RankThree.PartTwo.Sec8.Hering611RInspectL2
public import CFSG.RankThree.PartTwo.Sec8.Hering611RInspectSpFour
public import CFSG.RankThree.PartTwo.Sec8.Hering611RInspectF4
public import CFSG.RankThree.PartTwo.Sec8.Hering611RInspectA2
public import CFSG.RankThree.PartTwo.Sec8.Hering611Facts

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSU StatedSp StatedProj)
open CFSG.Blueprint

section Final


theorem kF611InspectField_of (h45 : Sec4.Item4_5)
    (h47 : Sec4.Item4_7) : Hering611.KF611InspectField := by
  intro G _ _ A c L E T d S K C ⟨x, hxA, hxk⟩
  have hout : InducesOuterTheta x K := by
    rcases hxk with h | h
    · exact KFacts.InducesStdKind.inducesOuterTheta K h (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta K h (by decide)
  have hAlt := alt47_of_cfg h47 C hxA hout
  have hA6 : HasA6Cent K c := hasA6Cent_of_cfg h45 C
  have hc3 : c ^ 3 = 1 := C.mem_S.1.1.2 c C.c_mem
  have hx3 : x ^ 3 = 1 := C.mem_S.1.1.2 x hxA
  obtain ⟨hcN, hα3, hα1, P, hP, ⟨e6⟩⟩ := hA6
  have hPsub : IsA6Sub P := ⟨isPerfect_of_mem_thetaComponentsIn hP, ⟨e6⟩⟩
  have hA6' : HasA6Cent K c := ⟨hcN, hα3, hα1, P, hP, ⟨e6⟩⟩
  rcases hAlt with ⟨p, e, hp, hp2, he, ⟨φ⟩, hk⟩ | ⟨p, e, hp, hp3, he1, he2, hX, hk⟩ |
    ⟨⟨m, hm, hX⟩ | ⟨n, hn, hX⟩, hk⟩ | ⟨n, hn, hX, hk⟩ | ⟨n, hn, hX, hk, hC⟩
  ·
    by_cases hp3 : p = 3
    · subst hp3
      exact Or.inl ⟨e, he, ⟨φ⟩⟩
    · exact (false_of_projSL2 hp3 (by omega) φ hPsub).elim
  ·
    rcases hX with hX | hX
    · exact (false_of_isSLThreePiAt hX hPsub).elim
    · exact (false_of_isoLThreePi_two hp3 he1 he2 hX hA6').elim
  ·
    rcases hX with h | ⟨K', _, _, hK, ⟨φ⟩⟩ | h | ⟨K', _, _, hK, ⟨φ⟩⟩
    · obtain ⟨φ⟩ := h
      exact (false_of_projSL2 (r := 2) (by norm_num) hm φ hPsub).elim
    · exact (false_of_statedSU hm hK φ hPsub).elim
    · obtain ⟨φ⟩ := h
      exact (false_of_projSU hm φ hPsub).elim
    · exact (false_of_statedSL hm hK φ hPsub).elim
  ·
    rcases hX with hX | h | h | hX | hX
    · exact (false_of_suzuki hX hPsub).elim
    · obtain ⟨φ⟩ := h
      exact (false_of_projSL3 hn φ hPsub).elim
    · obtain ⟨φ⟩ := h
      exact Or.inr (spFour611 hc3 hn φ hA6')
    · exact (false_of_g2 hn hX hPsub).elim
    · exact (largeRee611 hc3 hn hX hA6').elim
  ·
    rcases hX with hX | hX
    · exact (false_of_isSLThreePiAt hX hPsub).elim
    · exact (false_of_isoLThreePi_four hn hX hx3 hk hxk hPsub).elim
  ·
    exact (false_of_d4 hn hX hPsub).elim

end Final

end CFSG.RankThree.PartTwo.Sec8.Hering611R
