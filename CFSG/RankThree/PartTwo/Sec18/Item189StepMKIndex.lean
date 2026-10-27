module

public import CFSG.RankThree.PartTwo.Sec18.Item189StepIndexI
public import CFSG.RankThree.PartTwo.Sec18.Item18ResProofStatements
import CFSG.RankThree.PartTwo.Sec18.Item189StepMKNormalizer

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

theorem relIndex_sup_inf_n189_eq_one_alt1C (h1812 : Item181_2) (hAlt : Item182Alt1C)
    (h1841 : Item184_1) (h1842 : Item184_2) {G : Type} [Group G] [Finite G] {A M H : Subgroup G}
    {c : G} (hset : Setting189 G A M H c)
    (hO : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) = ⊥) :
    (normalClosureIn M c ⊔ (M ⊓ n189 H)).relIndex M = 1 :=
  Subgroup.relIndex_eq_one.mpr (le_sup_inf_n189_of_normalizer_le189 hset.toSec18H hset.pRank_eq
    (normalizerLeN189OfO2Trivial_of_alt1C h1812 hAlt h1841 h1842 G A M H c hset.toSec18H
      hset.hyp187.1 hset.hyp187.2.1 hO))

theorem step189MKTwoI_of_alt1C (h1812 : Item181_2) (hAlt : Item182Alt1C) (h1841 : Item184_1)
    (h1842 : Item184_2) : Step189MKTwoI := by
  intro G _ _ A M H c hset _ hO _
  rw [relIndex_sup_inf_n189_eq_one_alt1C h1812 hAlt h1841 h1842 hset hO]
  norm_num

theorem step189MKOddL4_of_alt1C (h1812 : Item181_2) (hAlt : Item182Alt1C) (h1841 : Item184_1)
    (h1842 : Item184_2) : Step189MKOddL4 := by
  intro G _ _ A M H c hset _ _ hO
  rw [relIndex_sup_inf_n189_eq_one_alt1C h1812 hAlt h1841 h1842 hset hO]
  norm_num

theorem step189IndexI_of_sec18_alt1C (h186 : Item186H) (h187 : Item187) (h1812 : Item181_2)
    (hAlt : Item182Alt1C) (h1841 : Item184_1) (h1842 : Item184_2) : Step189IndexI :=
  step189IndexI_of h186 h187 (step189MKTwoI_of_alt1C h1812 hAlt h1841 h1842)

theorem step189L4_of_sec18_alt1C (h186 : Item186H) (h187 : Item187) (h1812 : Item181_2)
    (hAlt : Item182Alt1C) (h1841 : Item184_1) (h1842 : Item184_2) : Step189L4 :=
  step189L4_of h186 h187 (step189MKOddL4_of_alt1C h1812 hAlt h1841 h1842)

end CFSG.RankThree.PartTwo.Sec18
