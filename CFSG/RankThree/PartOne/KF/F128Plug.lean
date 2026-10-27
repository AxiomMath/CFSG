module

public import CFSG.RankThree.PartOne.KF.F128Rk2
public import CFSG.RankThree.PartOne.KF.F128Final
public import CFSG.RankThree.PartOne.S12.Sec128
public import CFSG.RankThree.PartOne.S12.KF128Rank1
import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.FieldFix
open CFSG.Blueprint (LieModel EvenLieType)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem kf128Rank1_holds
    (hT : ∀ t, TagFixedFacts t) : KF128Rank1 := by
  intro G _ _ p J E a d hp h5 hq _ _ hr hZ hEel hEN haE hdE hdJ hd1 hfa _
  exact kf128_of_rank_one hT hp h5 hq hZ hr hEel hEN haE hdE hdJ hd1 hfa

theorem node128_of_split (hSchreier : SchreierFor InCatalog) (hTwoAction : TwoActionInputs)
    (h81 : SelectedPrimeElementsNormalizeThetaComponents)
    (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple) (h112 : InSec11Two)
    (hKF1 : KF128Rank1) (hKF2 : KF128Rk2c) : Node128 := by
  intro G _ _ p A c L E h hX
  obtain ⟨X, hX0, hX2⟩ := hX
  have hXfam : X ∈ thetaComponentFamily p A := (sectionTenZeroStar_subset p A).2.2.1 hX0.2
  obtain ⟨cX, hcXA, hcX1, hXc⟩ := mem_thetaComponentFamily_iff.mp hXfam
  have hXq : CFSG.IsQuasisimple X := h106 hSchreier hTwoAction G p A h.setup X hX0
  obtain ⟨hEven, hZ, a, d, haA, hdA, hd1, -, hdAX, hFA⟩ :=
    h112 G p A h.setup cX hcXA hcX1 X ⟨⟨hX0, hX2⟩, hXc⟩
  have hdX : d ∈ X := (Subgroup.mem_inf.mp (hdAX ▸ Subgroup.mem_zpowers d)).2
  have hEnorm : E ≤ Subgroup.normalizer (X : Set G) :=
    h.E_normalizes_thetaComponentsAt h81 (h.A_le_E hcXA) hXc
  obtain ⟨-, S, hSX, hS1, hS2, hAS, -⟩ := (sectionTenZeroStar_subset p A).1 hX0
  have hp := h.prime
  have h5 : 5 ≤ p := by
    have h3 := h.three_lt
    by_contra hlt
    have h4 : p = 4 := by omega
    exact absurd hp (by rw [h4]; decide)
  have hrank : evenRank ↥X ≤ 3 := (Sec9A.evenRank_subgroup_le X).trans h.evenRank_eq.le
  have : Fact p.Prime := ⟨hp⟩
  by_cases hr1 : CFSG.pRank p ↥X ≤ 1
  · obtain ⟨y, -, -, hyd, hya, hye⟩ := hKF1 G p X E a d hp h5 hXq hEven hrank hr1 hZ h.E_elem hEnorm
      (h.A_le_E haA) (h.A_le_E hdA) hdX hd1 hFA ⟨S, hSX, hS1, hS2, hAS haA, hAS hdA⟩
    exact Sec128.torusHasTransvection_of_commutators h.E_elem (h.A_le_E hdA) hd1 (h.A_le_E haA)
      hyd hya hye
  · have hcXC : cX ∈ Subgroup.centralizer (X : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun g hg =>
        Subgroup.mem_centralizer_singleton_iff.1 ((mem_thetaComponentsAt_iff.mp hXc).1 hg)
    obtain ⟨y, -, -, hyd, hya, hye⟩ := hKF2 G p X E a cX d hp h5 hXq h.evenRank_eq.le
      (by omega) hZ h.E_elem hEnorm (h.A_le_E haA) (h.A_le_E hdA) (h.A_le_E hcXA) hdX hd1 hcX1 hcXC
      hFA
    exact Sec128.torusHasTransvection_of_commutators h.E_elem (h.A_le_E hdA) hd1 (h.A_le_E haA)
      hyd hya hye

end CFSG.RankThree.PartOne
