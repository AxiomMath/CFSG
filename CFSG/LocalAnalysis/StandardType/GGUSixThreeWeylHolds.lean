module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplit
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeWeylDescent
public import CFSG.LocalAnalysis.StandardType.GGStdPosC13UnitaryDvdGen
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Two
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverOdd

public section

namespace CFSG.StandardType

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.Assembly TableB

theorem ggTorusReflGenW_unitSixThree
    {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) :
    GGTorusReflGenW 3 4 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenGUSet (Fin 6) K (2 ^ n))) := by
  have hcard : ∀ {L' : Type} [Group L'] {A : Subgroup (MulAut L')}, 3 ^ 4 ≤ Nat.card A →
      3 ^ (6 / 3 + 2) ≤ Nat.card A := fun h => by simpa using h
  by_cases hn1 : n = 1
  · subst hn1
    have hcov := unitaryCoverOddAt_six_two K (by simpa using hK)
    refine ggTorusReflGenW_three_of_oddKernel fun L₁ _ _ ψ₁ A₁ hTB hodd => ?_
    obtain ⟨hψ, hker, hperf, hA, hAI, hr, -, hsc⟩ := hTB
    obtain ⟨φ, hφs, hφker, hdiag⟩ := Line63.exists_diagModel_of hK le_rfl (by norm_num)
      Nat.prime_three h3 (by norm_num) hcov.1 hψ hker hperf hA hAI (hcard hr)
      fun ψ'' hs hk => hcov.2 L₁ ψ'' hs (hk ▸ hker) hperf (hk ▸ hodd)
    exact unitDvd_automizer_le_closure ⟨TableBU.unitaryFieldData_of_card hK le_rfl, hφs, hφker⟩
      hK Nat.prime_three (by norm_num) h3 (by norm_num) hA hsc hdiag
  · intro L' _ _ ψ A hTB
    obtain ⟨hψ, hker, hperf, hA, hAI, hr, -, hsc⟩ := hTB
    obtain ⟨φ, hφs, hφker, hdiag⟩ := exists_diagModel hK hn (by norm_num) Nat.prime_three h3
      (by norm_num) (unitaryUniversalCover_holds n 6 K hK (by norm_num)
        fun h => hn1 (congrArg Prod.snd h)) hψ hker hperf hA hAI (hcard hr)
    exact unitDvd_automizer_le_closure ⟨TableBU.unitaryFieldData_of_card hK hn, hφs, hφker⟩
      hK Nat.prime_three (by norm_num) h3 (by norm_num) hA hsc hdiag

theorem ggUSixThreeNbrWeylInput_holds :
    GGUSixThreeNbrWeylInput := by
  rintro ⟨t, l, n⟩ hlab ⟨ht, hl5, -, h3⟩
  dsimp only at ht hl5 h3
  subst ht hl5
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  exact ⟨K, i1, i2, hK, ⟨hQ', ggTorusReflGenW_unitSixThree hK hn h3⟩⟩

end CFSG.StandardType

end
