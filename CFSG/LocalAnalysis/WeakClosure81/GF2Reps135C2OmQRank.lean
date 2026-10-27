module

import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL28
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open

theorem w135c2_omq_mQuot_eq {X : Type} [Group X] {W : Type} [CommGroup W] [Finite W] {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {L : Subgroup (MulAut W)} (e : X ≃* ↥L)
    {ρ : Representation (ZMod 2) X V} {θ : W ≃* Multiplicative V}
    (hθ : ∀ (s : X) (w : W),
      θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))))
    {g : MulAut W} {y : X} (hge : ((e y : ↥L) : MulAut W) = g) :
    E3.mQuot ⊤ (fixV (Subgroup.zpowers g)) =
      Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
  have heq := finL28_two_pow_mQuot_eq_card_range θ g (ρ y) (fun w => by
    rw [← hge]
    exact hθ y w)
  have hcardR : Nat.card (LinearMap.range (ρ y - 1)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := by
    refine letI : Module.Finite (ZMod 2) (LinearMap.range (ρ y - 1)) :=
      Module.Finite.of_finite;
      ?_
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  exact Nat.pow_right_injective (le_refl 2) (heq.trans hcardR)

end CFSG.LocalAnalysis.WeakClosure81
