module

public import CFSG.LocalAnalysis.StandardType.GGQ2CentralizerPort
public import CFSG.LocalAnalysis.StandardType.GGQTwoAssemble
public import CFSG.LocalAnalysis.StandardType.GGXInLDispatch
public import CFSG.LocalAnalysis.StandardType.GGCSRHolds
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVac

public section

namespace CFSG.StandardType.GGQ2CentPort

open CFSG CFSG.Assembly

theorem smallLabelsTwoInput_holds :
    smallLabelsTwoInput := by
  intro G _ _ p B Bs x L D J hS hon R _ θ hN
  exfalso
  have hp3 : p = 3 := ggQ2_pThree hS
  subst hp3
  have hperf : commutator L = ⊤ := (isQuasisimple_of_largeEvenMarking (K := L) hS.2.1).1
  obtain ⟨-, lab, hlab, hraw⟩ := hon
  have hfam : lab.tag = .triD4 ∨ lab.tag = .G2 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
      lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der ∨
        (lab.tag = .twD ∧ lab.rank = 2) := by
    obtain ⟨-, -, -, -, -, -, -, hP, -, -⟩ := largeEvenRawDatum_exists hraw
    exact hP.2
  have hsmall : (lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
      lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der) →
      LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
        (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ 3 := by
    intro h7
    exact (ggSmallThreeRank_of_labels lab hlab h7).mono fun R _ I F hR X hXI hX =>
      lt_of_le_of_lt (hR X (fun a ha => hXI ha) hX) (by norm_num)
  have hbound : LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ 3 := by
    rcases hfam with ht | ht | ht | ht | ht | ht | ht | hD
    · exact hsmall (by simp [ht])
    · exact hsmall (by simp [ht])
    · exact hsmall (by simp [ht])
    · exact hsmall (by simp [ht])
    · exact hsmall (by simp [ht])
    · exact hsmall (by simp [ht])
    · exact hsmall (by simp [ht])
    · exact largeEvenLabelAll_card_lt_linearTwo Nat.prime_three (by norm_num) hlab (Or.inr hD)
  refine GGXInL.lup8g_rank_contra hS hperf (largeEvenRawDatum_mono ?_ hraw) hbound
  rintro R' _ I' F' ⟨hs, hna, θ', ⟨hq, -⟩, hrest⟩
  exact ⟨hs, hna, θ', hq, hrest⟩

end CFSG.StandardType.GGQ2CentPort

end
