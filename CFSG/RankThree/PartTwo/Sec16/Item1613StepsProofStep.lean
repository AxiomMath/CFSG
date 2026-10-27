module

import CFSG.RankThree.PartTwo.Sec16.Item16Tail13Tools
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1613Type

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec16.Proof1613 CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem mem_partTwoE_of_even {E : Subgroup G} {c : G} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) (hEc : E ≤ Subgroup.centralizer ({c} : Set G))
    (hev : ¬ Odd (Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer ({c} : Set G))))) :
    E ∈ partTwoE G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := pPrimeCoreOf 3 (Subgroup.centralizer ({c} : Set G)) with hX
  have hEN : E ≤ Subgroup.normalizer (X : Set G) := hEc.trans (le_normalizer_pPrimeCoreOf 3 _)
  have h2 : 2 ∣ Nat.card X := by
    rcases Nat.even_or_odd (Nat.card X) with he | ho
    · exact even_iff_two_dvd.mp he
    · exact absurd ho hev
  obtain ⟨T, hET, hT1⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
      3 2 Nat.prime_three Nat.prime_two E X (isPGroup_three_of_isElemAbelian hE) hEN
      (coprime_card_pPrimeCoreOf 3 _) h2
  exact ⟨hE, hE27, _, hT1, T.isPGroup'.map _, hET⟩

end CFSG.RankThree.PartTwo.Sec16.Proof1613Type

