module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofHelpers

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSp projSU)
open Subgroup

@[expose] def K423Inner46SixLie : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    ((∃ n : ℕ, 1 ≤ n ∧
        (Nonempty (X ≃* projSp 2 (GaloisField 2 n)) ∨ Nonempty (X ≃* projSU 4 2 n))) ∨
      ∃ f : ℕ, Blueprint.ChevalleyExceptionalModel X .G2 2 f ∨
        Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f ∨
        Blueprint.ReeTitsModel X .twistedF4 2 f) →
    IsQuasisimple X → Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census423 X

namespace Res423Three

open Res423Two CFSG.Sporadic.Schreier.Tits

theorem census423_of_tits
    {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : Blueprint.ReeTitsModel X .Tits 2 f) : Census423 X := by
  obtain ⟨e⟩ := titsModelEquiv X 2 f h
  refine census423_of_alphaVanishes fun D hD hD9 => alphaVanishes_of_mulEquiv e ?_
  have hD' : CFSG.Assembly.IsElemAbelian 3 (D.map e.toMonoidHom) := isElemAbelian_map' _ hD.prop
  have hD'9 : Nat.card (D.map e.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective e.injective, hD9]
  exact @alphaVanishes_of_noSignalizer titsD titsD.toGroup _ titsD_center _
    (comm_of_isElemAbelian hD') (ne_bot_of_card_nine hD'9)
    (Item434RemTits.noSignalizer hD' hD'9)

end Res423Three

open Res423Three

theorem k423Inner46SixRest_of
    (h : K423Inner46SixLie) : K423Inner46SixRest := by
  intro X _ _ hX hq hZ hSL
  rcases hX with hX | ⟨f, hG | hD | hF | hT⟩
  · exact h X (Or.inl hX) hq hZ hSL
  · exact h X (Or.inr ⟨f, Or.inl hG⟩) hq hZ hSL
  · exact h X (Or.inr ⟨f, Or.inr (Or.inl hD)⟩) hq hZ hSL
  · exact h X (Or.inr ⟨f, Or.inr (Or.inr hF)⟩) hq hZ hSL
  · exact census423_of_tits hT

end CFSG.RankThree.PartTwo.Sec4
