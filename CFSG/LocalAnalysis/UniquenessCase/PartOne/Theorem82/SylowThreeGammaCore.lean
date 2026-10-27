module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
public import CFSG.Open.RankThreeDefs

import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.RankThree.PartOne.S12.Sec159Tools
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.RankThree.PartOne.S11d.OutCentral
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SylowThreeData

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem relPPrimeCore_le_of_AA_le_of_gamma_two_le
    (d : SylowThreeData G)
    (hΓ : CFSG.Open.rankThreeGamma 2 3 d.AA ≤ d.M)
    {H : Subgroup G} (hAH : d.AA ≤ H) :
    CFSG.Open.relPPrimeCore 3 H ≤ d.M := by
  refine CFSG.RankThree.PartOne.Sec159.le_of_pPrime_normalized Nat.prime_three
    (A := d.AA) (Z := CFSG.Open.relPPrimeCore 3 H) (N := d.M)
    (CFSG.Open.IsElemAbelian.isElementaryAbelian d.isElemAbelian_AA) ?_ ?_ ?_ ?_
  · rw [d.card_AA]
    norm_num
  · intro B hBA hBcyc
    have hBp : IsPGroup 3 B :=
      (CFSG.Open.IsElemAbelian.isPGroup d.isElemAbelian_AA).to_le hBA
    have hrank : 2 ≤ CFSG.Open.pRank 3 B := by
      by_contra hlt
      have hlt' : CFSG.Open.pRank 3 B < 2 := Nat.lt_of_not_ge hlt
      have hle : CFSG.pRank 3 ↥B ≤ 1 := by
        rw [CFSG.SectionRank.pRank_coe_eq_openPRank 3 B]
        omega
      exact hBcyc (CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one Nat.prime_three
        (by norm_num) le_rfl hBp hle)
    exact (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore
      (p := 3) (k := 2) (P := d.AA) (Q := B) hBA hrank).trans hΓ
  · refine hAH.trans ?_
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le (p := 3) H)).mp
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_normal
        Nat.prime_three H)
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
        Nat.prime_three H)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SylowThreeData
