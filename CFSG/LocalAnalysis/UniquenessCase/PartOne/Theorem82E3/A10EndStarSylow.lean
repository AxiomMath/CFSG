module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndStarAS
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndStarL227
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndStarOuter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

@[expose] def KFactE27SignalizerAlmostSimpleSylow : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (P A : Subgroup X), CFSG.Open.IsKGroup X →
    UC22.InS3.UC327.Hyp327 X P A → Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1) →
    CFSG.pPrimeCore 3 X = ⊥ →
    (∀ a ∈ A, a ≠ 1 → ∀ W : Subgroup X, W ≤ Subgroup.centralizer ({a} : Set X) →
      A ≤ Subgroup.normalizer (W : Set X) → Nat.Coprime (Nat.card W) 3 →
      W ≤ CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer ({a} : Set X))) →
    ∀ L : Subgroup X, CFSG.IsComponent L → Subgroup.centralizer (L : Set X) = ⊥ → P ≤ L →
    ∀ W : Subgroup X, A ≤ Subgroup.normalizer (W : Set X) → Nat.Coprime (Nat.card W) 3 →
      W = ⊥

theorem kFactE27SignalizerAlmostSimple_of_sylow (h717 : RankThreeUC.AGL81C.SevenOneSeven)
    (hO3 : RankThreeTheoremC.KFactOutThreePrimeSimple) (hA3 : KFactAutThreeRankTwo)
    (h : KFactE27SignalizerAlmostSimpleSylow) : KFactE27SignalizerAlmostSimple := by
  intro X _ _ P A hK hX hPZ h3' hbal L hL hC W hW hcop
  by_cases hPL : P ≤ L
  · exact h X P A hK hX hPZ h3' hbal L hL hC hPL W hW hcop
  · exact A10Gen.eq_bot_of_le_of_not_le h717 hX hPZ hL hC
      (A10Gen.le_of_centralizer_eq_bot hO3 hA3 hX hPZ h3' hL hC) hPL hW hcop

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
