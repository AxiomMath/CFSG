module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporHNRank
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105In
public import Certificates.Certificate2089
public import Certificates.Certificate26777
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105InThompson
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporHNWreath
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporHNOdd
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Quotient
import CFSG.Quasithin.Background.A4V
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG CFSG.QuasithinUnique Subgroup CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore
  CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.SideF4 HNRank


theorem hn_k105In_centralizer : K105In (centralizer {t4J}) hnT0 := by
  obtain ⟨e⟩ := nonempty_quotient_QJ
  refine k105In_of_quotient isSylowTwoOf_hnT0 hnT0_le_centralizer QJ ?_ e
    fun S H hS hSH _ h3 => le_of_isSylowTwoOf_of_not_three_dvd_a5WrTwo hS hSH h3
  rintro _ ⟨q, hq, rfl⟩
  exact Subgroup.mem_subgroupOf.1 (hn_qJ_le_subgroupOf isSylowTwoOf_hnT0 hnT0_le_centralizer hq)

theorem hn_k105In_normalizer_thompsonJ :
    K105In (normalizer (CFSG.Quasithin.thompsonJ hnT0 : Set JH)) hnT0 :=
  (k105In_normalizer_of_card_le_four isSylowTwoOf_hnT0 hnT0_le_centralizer
    t4J_mem_omegaOneCenterOf_thompsonJ card_omegaOneCenterOf_thompsonJ_le
    hn_k105In_centralizer).mono
    (CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf _)

theorem k105SporAt_HN : K105SporAt .HN := by
  have ht : t4J ∈ hnT0 := Subgroup.subset_closure (by simp [t0Gens])
  have hz : t4J ∈ CFSG.Open.quasithinOmegaOneCenter hnT0 := by
    unfold CFSG.Open.quasithinOmegaOneCenter
    refine Subgroup.subset_closure ⟨Subgroup.mem_inf.2 ⟨ht, ?_⟩, by rw [sq]; exact t4J_sq⟩
    exact Subgroup.mem_centralizer_iff.2 fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.1 (hnT0_le_centralizer hs)
  exact k105SporAt_of_k105In isSylowTwoOf_hnT0
    (k105In_top_of_thompson isSylowTwoOf_hnT0 hz hn_k105In_centralizer
      hn_k105In_normalizer_thompsonJ
      (hn_oddLocal isSylowTwoOf_hnT0 hnT0_le_centralizer)) hnEquivJ

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
