module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107Thin
import CFSG.LocalAnalysis.UniquenessCase.UC22U3Loss
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFourFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace R8107U3

theorem lossAt_of_isU3 {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsU3 X n) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) : R8107Loss.LossAt X p := by
  intro P _ _ hexp hPab φ
  exact exists_orderOf_three_index_le_u3 hX hp hp5 hexp hPab φ

theorem center_and_loss (D : Data G) (hKThin : KThinSimple) {L : Subgroup G} (hL : L ∈ calC D.M)
    (r : CFSG.Open.pRank 3 L = 1) (hs : F08.Thin8 L ∨ ∃ n : ℕ, IsU3 (Bar2 L) n) :
    center (Bar2 L) = ⊥ ∧ ∀ p : ℕ, p.Prime → 5 ≤ p → R8107Loss.LossAt (Bar2 L) p := by
  rcases hs with s | ⟨n, hn⟩
  · exact ⟨R8107Shape.center_eq_bot_of_thin8 hL s,
      fun _ hp hp5 => R8107Thin.lossAt_of_thin8 D hKThin hL r s hp hp5⟩
  · exact ⟨PartTwo.S17.center_eq_bot_of_isU3 hn, fun _ hp hp5 => lossAt_of_isU3 hn hp hp5⟩

end R8107U3

theorem r8107_u3_of_inputs (D : Data G) (hx : DataExt D) (he : 3 < CFSG.Open.evenRank G)
    (hSg : UC6S846.SigmaStd D) (h82 : F08.R82 D)
    (h76 : F07.R76Sig D) (h614 : UC6.R6_14 D)
    (hKThin : KThinSimple) : R8107U3 D := by
  intro L₁ hL₁ L₂ hL₂ h12 r₁ r₂ s₁ s₂ _ A₁ A₂ hA₁ hc₁ hA₂ hc₂
  obtain ⟨hZ₁, hloss₁⟩ := R8107U3.center_and_loss D hKThin hL₁ r₁ s₁
  exact r8107_of_loss D hx he hSg h82 h76 h614 hL₁ hL₂ h12 r₁ r₂ hZ₁ hloss₁
    (R8107U3.center_and_loss D hKThin hL₂ r₂ s₂).2 hA₁ hc₁ hA₂ hc₂

theorem r8107_of_inputs (D : Data G) (hx : DataExt D) (he : 3 < CFSG.Open.evenRank G)
    (hSg : UC6S846.SigmaStd D) (h82 : F08.R82 D)
    (h76 : F07.R76Sig D) (h614 : UC6.R6_14 D)
    (hKThin : KThinSimple) : F08.R8107 D :=
  r8107_of_thin_and_u3 (r8107_thin_of_inputs D hx he hSg h82 h76 h614 hKThin)
    (r8107_u3_of_inputs D hx he hSg h82 h76 h614 hKThin)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
