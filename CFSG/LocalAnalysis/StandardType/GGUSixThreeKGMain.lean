module

public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGDefs
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGCases
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGDescent
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Two
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverOdd
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitary

public section

namespace CFSG.StandardType.UnitSixThreeKG

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD CFSG.Assembly CFSG.StandardType

section Certificates


theorem ggTorusNoLineComp_unitSix {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1) :
    GGTorusNoLineComp 3 0 (LargeEvenProj (unitarySU 2 n K 6))
      (LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
        (LargeEvenGUSet (Fin 6) K (2 ^ n))) := by
  refine ggTorusNoLineComp_of_perLine fun L' _ _ ψ hψ hker hperf A hA hAI h3 => ?_
  by_cases hn1 : n = 1
  · subst hn1
    have hcov := LineU.unitaryCoverOddAt_six_two K (by simpa using hK)
    refine perLineOn_descent hψ hker hperf hA hAI
      (fun L₁ _ _ ψ₁ hs hk hp hodd A₁ hA₁ hAI₁ hc => ?_)
    exact perLineOn_of_cover hK le_rfl hpq hcov.1
      (fun ψ'' hs'' hk'' => hcov.2 L₁ ψ'' hs'' (hk'' ▸ hk) hp (hk'' ▸ hodd)) hs hk hp hA₁ hAI₁
      (by rw [hc]; exact h3)
  · have hcov := LineU.unitaryUniversalCover_holds n 6 K hK (by norm_num)
      (fun h => hn1 (Prod.mk.inj h).2)
    exact perLineOn_of_cover hK hn hpq hcov.1
      (fun ψ'' hs'' hk'' => hcov.2 L' ψ'' hs'' (hk'' ▸ hker) hperf) hψ hker hperf hA hAI h3

theorem ggNbrKGUnitSixThree_holds : GGNbrKGUnitSixThree := by
  intro lab hlab htag hrank h3
  refine largeEvenLabelAll_unitaryLift (p := 3) hlab ⟨Or.inl htag, h3⟩
    (fun _ R _ I => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGTorusNoLineComp 3 0 R I) ?_
  intro K _ _ n d hK hn _ _ hpq hd
  have hd6 : d = 6 := by omega
  subst hd6
  intro _ _
  exact ggTorusNoLineComp_unitSix hK hn hpq

end Certificates

end CFSG.StandardType.UnitSixThreeKG

end
