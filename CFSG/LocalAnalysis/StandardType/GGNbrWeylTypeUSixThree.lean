module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeUSixThreeAux
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeUSixThreeAux2
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverOdd
import CFSG.LocalAnalysis.StandardType.GGUSixThreeWeylHolds

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.StandardType.LineU

private theorem ggWTUS_unitSixThree
    {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) :
    GGTorusWeylTypeW 3 4
      (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenGUSet (Fin 6) K (2 ^ n))) := by
  by_cases hn1 : n = 1
  · subst hn1
    have hcov := LineU.unitaryCoverOddAt_six_two K (by simpa using hK)
    refine ggWTUS_weylTypeW_of_oddKernel (r := 4) fun L₁ _ _ ψ₁ A₁ hTB₁ hodd => ?_
    obtain ⟨hψ₁, hker₁, hperf₁, hAab₁, hAI₁, hr₁, -, hsc₁⟩ := hTB₁
    have hcard : 3 ^ (6 / 3 + 2) ≤ Nat.card A₁ := by
      have : 6 / 3 + 2 = 4 := by norm_num
      rw [this]; exact hr₁
    obtain ⟨φ, hφs, hφker, hdiag⟩ := Line63.exists_diagModel_of (K := K) hK le_rfl
      (by norm_num : 5 ≤ 6) Nat.prime_three h3 (by norm_num : 3 ∣ 6) hcov.1 hψ₁ hker₁
      hperf₁ hAab₁ hAI₁ hcard
      (fun ψ'' hs hk => hcov.2 L₁ ψ'' hs (hk ▸ hker₁) hperf₁ (hk ▸ hodd))
    exact ggWTUS_diagModel_weylAt (n := 1) (d := 6) (p := 3) (ψ := ψ₁) hK le_rfl (by norm_num)
      Nat.prime_three h3 hAab₁ hsc₁ hφs hφker hdiag
  · intro L' _ _ ψ A hA
    obtain ⟨hψ, hker, hperf, hAab, hAI, hr, -, hsc⟩ := hA
    have hcard : 3 ^ (6 / 3 + 2) ≤ Nat.card A := by
      have : 6 / 3 + 2 = 4 := by norm_num
      rw [this]; exact hr
    have hdnd : (6, n) ≠ (6, 1) := by
      intro h
      exact hn1 (congrArg Prod.snd h)
    obtain ⟨φ, hφs, hφker, hdiag⟩ := exists_diagModel hK hn (by norm_num : 5 ≤ 6)
      Nat.prime_three h3 (by norm_num : 3 ∣ 6)
      (unitaryUniversalCover_holds n 6 K hK (by norm_num) hdnd) hψ hker hperf hAab hAI hcard
    exact ggWTUS_diagModel_weylAt (n := n) (d := 6) (p := 3) (ψ := ψ) hK hn (by norm_num)
      Nat.prime_three h3 hAab hsc hφs hφker hdiag

theorem ggUSixThreeNbrWeylTypeInput_holds :
    GGUSixThreeNbrWeylTypeInput := by
  rintro ⟨t, l, n⟩ hlab ⟨ht, hl5, -, h3⟩
  dsimp only at ht hl5 h3
  subst ht hl5
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  exact ⟨K, i1, i2, hK, ⟨hQ', ggWTUS_unitSixThree hK hn h3⟩⟩

end CFSG.StandardType

end
