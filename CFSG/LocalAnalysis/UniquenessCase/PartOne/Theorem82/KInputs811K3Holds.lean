module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811
import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaKFacts3Onan
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowONan
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

theorem k3Exp_holds : K3Exp := by
  intro Y _ _ hY S
  obtain ⟨hq, hZ3, ⟨e⟩⟩ := hY
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZp : IsPGroup 3 (Subgroup.center Y) := IsPGroup.of_card (n := 1) (by rw [hZ3, pow_one])
  have hZc : IsCyclic (Subgroup.center Y) := isCyclic_of_prime_card hZ3
  have hZ : Subgroup.center Y ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZ3
    omega
  exact CFSG.LocalAnalysis.RankThreeTheoremC.pow_three_eq_one_of_abelianSylowDatum hq hZ hZp hZc e
    CFSG.AGLEmbedding.abelianSylowDatum_ON_three S

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
