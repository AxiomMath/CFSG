module

public import CFSG.RankThree.PartTwo.Sec18.SimsItem186HStatement
public import CFSG.RankThree.PartTwo.Sec18.Item189StepMKNormalizer
import CFSG.RankThree.PartTwo.Sec18.SimsAlt2Normalizer
import CFSG.RankThree.PartTwo.Sec18.SimsItem186Local
import CFSG.RankThree.PartTwo.Sec18.SylowPlane

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

theorem centralizer_le_normalizer_of_hyp187 (hT : NormalizerLeN189OfO2Trivial)
    {A M H : Subgroup G} {c : G} (hH : Sec18H G A M H c) (h7 : Hyp187 A M H c) :
    Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (inSubgroup perfectResidual H : Set G) := by
  refine (Rem187QProof.centralizer_le_normalizer_zpowers c).trans ?_
  by_cases hO : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) = ⊥
  · exact hT G A M H c hH h7.1 h7.2.1 hO
  · exact h7.2.2 hO

section Certified


theorem item186H_of_normalizerLeN189OfO2Trivial (h4443 : Sec4.Item4_44_3) (h1812 : Item181_2)
    (h1813 : Item181_3) (h184 : Item184_1) (hT : NormalizerLeN189OfO2Trivial) : Item186H := by
  intro G _ _ A M H c hH h7
  have hc := mem_and_commutator_mem_of_sec18H hH
  exact item186_of_item182Alt1At h1812 h1813 h184 hH h7.1 h7.2.1
    (item182Alt1At_of_centralizer_le_normalizer h4443 hH.toSec18Std h7.1 hc.1 hc
      (centralizer_le_normalizer_of_hyp187 hT hH h7))

theorem item186H_of (h4443 : Sec4.Item4_44_3) (h1812 : Item181_2) (h1813 : Item181_3)
    (h184 : Item184_1) (h1842 : Item184_2) (hAlt : Item182Alt1C) : Item186H :=
  item186H_of_normalizerLeN189OfO2Trivial h4443 h1812 h1813 h184
    (normalizerLeN189OfO2Trivial_of_alt1C h1812 hAlt h184 h1842)

end Certified

end CFSG.RankThree.PartTwo.Sec18
