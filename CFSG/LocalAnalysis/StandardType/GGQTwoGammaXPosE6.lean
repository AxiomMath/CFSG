module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXPosLeaf
public import CFSG.LocalAnalysis.StandardType.GGQTwoDepE6

public section

namespace CFSG.StandardType

@[expose] def GGQ2GammaXPosNoModelInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L → ∀ [Fact p.Prime],
    (¬ ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
      ((GGQTwoTwoNodeRowAt p L J ∧ x ∉ L) ∨ (GGQTwoTwoNodeRowAt p K J ∧ y ∉ K))) →
    (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ¬ Nonempty (GGQTwoModel p Bs x y D L J K)) →
    ∀ {u : ↥Bs}, Subgroup.zpowers (u : G) = Subgroup.zpowers x → GGGammaAt p B Bs x L D J u

theorem ggQ2_gammaXPosE6_of_noModel (hHeart : GGQ2HeartInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (h5 : GGQTwoCentralizerInput) (h : GGQ2GammaXPosNoModelInput) :
    GGQ2GammaXPosE6Input := by
  intro G _ _ p B Bs x L D J hS hp hI1 hxL _ hrow _ hall u hu
  by_cases hex : ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
      Nonempty (GGQTwoModel p Bs x y D L J K)
  · obtain ⟨y, K, hnb, ⟨M⟩⟩ := hex
    obtain ⟨⟨e, he, hea, -⟩, -⟩ := hall y K hnb M
    have hA := ggQ2_e6_automizer_le hHeart hLB hP hp hS (ggQ2_ajOfSetting hP h5 hS)
      (ggQ2_K1_of_I1 hLB hP hS.1 hI1) hnb M e (M.toLin.coxeter_eq_E6_of_cartan e he) hea.symm
    exact fun φ hφ _ => hA hφ
  · exact h hS hp hI1 hxL hrow (fun y K hnb hM => hex ⟨y, K, hnb, hM⟩) hu

end CFSG.StandardType

end
