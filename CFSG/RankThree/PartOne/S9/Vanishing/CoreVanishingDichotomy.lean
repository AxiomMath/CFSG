module

public import CFSG.RankThree.PartOne.S9.StatementsAlpha
public import CFSG.RankThree.PartOne.S9.StatementsSylow
import CFSG.RankThree.PartOne.S9.Vanishing.Basic

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

theorem coreVanishingDichotomy_of (hUAV : SectionNineUniformAlphaVerification)
    (hAPCLN : AlphaProductCoreLocalNormalizer) (hAZSC : AlphaZeroSylowCentralization)
    (hAZOI : AlphaZeroOddIntersection) : CoreVanishingDichotomy := by
  intro G _ _ p hS hgood A hA hAcard P hAP B hBA hBcard c hc hc1
  by_cases hα : twoCoreAlpha B = ⊥
  · exact Or.inr ⟨hα, (hAZSC G p hS hgood A hA hAcard B hBA hBcard hα).2 c hc hc1,
      hAZOI G p hS hgood A hA hAcard B hBA hBcard hα⟩
  · have hp2 : p ≠ 2 := by
      have := hS.three_lt
      omega
    have hBP : B ≤ (P : Subgroup G) := hBA.trans hAP
    have hBe : IsElementaryAbelian p B := Vanish.isElementaryAbelian_of_le hA hBA
    have hrank : 3 ≤
        CFSG.Assembly.pRank p ((P : Subgroup G) ⊓ Subgroup.centralizer (B : Set G)) := by
      refine Vanish.le_assemblyPRank hS.prime.one_lt (E := A) (le_inf hAP ?_) hA hAcard
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact congrArg Subtype.val (hA.is_comm.comm ⟨b, hBA hb⟩ ⟨a, ha⟩)
    obtain ⟨-, hcore, hloc⟩ := hAPCLN G p hS.prime hp2
      (fun A' hA' hcard' => (hUAV G p hS hgood A' hA' hcard').1) (P : Subgroup G)
      P.isPGroup' B hBP hBe hBcard hrank
    exact Or.inl ⟨hα, _, hloc hα, hcore⟩

end CFSG.RankThree.PartOne
