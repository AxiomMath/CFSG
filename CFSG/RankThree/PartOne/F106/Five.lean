module

public import CFSG.RankThree.PartOne.F106.Assemble
public import CFSG.RankThree.PartOne.F106.Defs
public import CFSG.RankThree.PartOne.S9.StatementsSylow
public import CFSG.RankThree.PartOne.N143.SectionListBound
import CFSG.RankThree.PartOne.F106.Central
import CFSG.RankThree.PartOne.F106.ZeroStar
import CFSG.RankThree.PartOne.S10.FiveSuccessorConstruction
import CFSG.RankThree.PartOne.S10.FiveSuccessorMaximal

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.RankThree.PartOne.N143 (SectionListBound)
open scoped commutatorElement

theorem movingQuasisimpleFive_of (hCVD : CoreVanishingDichotomy) (hI : InSec10Seven)
    (hSLB : SectionListBound) (hRank : EvenLieFiveRank) (hQD : EvenLieNoQD32)
    (hN1 : FiveNoncentralExcluded) : MovingQuasisimpleFive := by
  intro hS hTwo G _ _ A h K hK
  by_contra hnq0
  have hp : Nat.Prime 5 := by norm_num
  obtain ⟨L, hL, hnq, hmax⟩ := exists_five_maximal_nonquasisimple hS h ⟨K, hK, hnq0⟩
  obtain ⟨c, hcA, hc1, hLc⟩ := mem_thetaComponentFamily_iff.mp hL.1
  obtain ⟨q, D, R, -, -, hcrit⟩ := section_ten_five_critical_action_and_central_involution hTwo G A
    c L hcA hc1 h ⟨hL, hLc⟩ hnq
  obtain ⟨e, K₀, hsucc⟩ := exists_five_successor hS h hmax hcrit
  by_cases hcent : ⁅thetaQuotientCentralizer 5 A L, D⁆ = ⊥
  · exact central_false hS hTwo hCVD hI hSLB hRank hQD hsucc hcent
  · obtain ⟨K', hK', hKK'⟩ := exists_zeroStar_above_of_zero hS h hsucc.K_mem.1
    exact hN1 G A L c q D R e K₀ hsucc hcent K' hK'
      (K156.le_of_sectionTenRel_of_quasisimple hp hsucc.K_quasisimple hKK')
      (hI G 5 A h K' hK') (zeroStar_quotient_list hS hTwo hSLB h hK')

theorem full106_of_inputs (h7 : MB3.MovingQuasisimpleSeven) (hCVD : CoreVanishingDichotomy)
    (hI : InSec10Seven) (hSLB : SectionListBound) (hRank : EvenLieFiveRank)
    (hQD : EvenLieNoQD32) (hN1 : FiveNoncentralExcluded) : K156.Full106Stmt :=
  full106_of_seven_five h7 (movingQuasisimpleFive_of hCVD hI hSLB hRank hQD hN1)

end CFSG.RankThree.PartOne.F106
