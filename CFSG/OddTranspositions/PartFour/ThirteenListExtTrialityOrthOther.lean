module

public import CFSG.OddTranspositions.PartFour.ThirteenListExtTrialityDerived
public import CFSG.OddTranspositions.PartFour.ThirteenListExtTrialityOrthOtherMinus
import CFSG.Quasithin.EmptyFaithful.S146zYOutComm

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem extTrialityOrthOther_holds : ExtTrialityOrthOther := by
  intro G _ _ t M _ h Y₀ _ _ s₀ n hL hcase
  obtain ⟨e₁, -⟩ := hL.equiv
  have hncM : ∃ a b : ↥M, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact h.not_isMulCommutative ⟨⟨hcon⟩⟩
  have key : ∀ {X : Type} [Group X], (↥M ≃* X) → (∀ a b : Outer X, a * b = b * a) → False :=
    fun e hX => h.not_comm_outer (CFSG.Quasithin.S146zY.outer_comm_of_mulEquiv e.symm hX)
  rcases hcase with ⟨k, hk2, hk4, F, _, _, hF, e₂, -⟩ | ⟨k, hk1, F, _, _, hF, b, c, hirr, e₂, -⟩
  · have : CharP F 2 := CFSG.SeitzReduction.F4Pilot.charP_two_of_natCard_eq_two_pow hF
    rcases (by omega : k = 2 ∨ k = 3 ∨ 5 ≤ k) with rfl | rfl | hk5
    · have hs := h.isSimpleGroup_derivedSeries_one (e₂.symm.trans e₁)
      refine false_of_simple_normal_orthogonalPlus_two (N := derivedSeries _ 1) (fun a b => ?_)
        hs ?_
      · rw [derivedSeries_one, ← commutatorElement_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      · by_contra hcon
        push Not at hcon
        exact h.not_isMulCommutative_derivedSeries_one (e₂.symm.trans e₁) ⟨⟨hcon⟩⟩
    · exact h.not_comm_outer (outer_comm_of_mulEquiv_commutator_orthogonalPlus_three h.simple hncM
        hF ((h.derivedEquiv (e₂.symm.trans e₁)).symm.trans
          (MulEquiv.subgroupCongr (derivedSeries_one _))))
    · exact key ((h.derivedEquiv (e₂.symm.trans e₁)).symm.trans
        (MulEquiv.subgroupCongr (derivedSeries_one _)))
        (outer_comm_commutator_orthogonalPlus_of_five_le hk5)
  · have : CharP F 2 := CFSG.SeitzReduction.F4Pilot.charP_two_of_natCard_eq_two_pow hF
    rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | hk3
    · exact key ((h.derivedEquiv (e₂.symm.trans e₁)).symm.trans
        (MulEquiv.subgroupCongr (derivedSeries_one _)))
        (outer_comm_commutator_orthogonalMinus_one hirr)
    · exact h.not_comm_outer (outer_comm_of_mulEquiv_commutator_orthogonalMinus_two h.simple hncM
        hirr hF ((h.derivedEquiv (e₂.symm.trans e₁)).symm.trans
          (MulEquiv.subgroupCongr (derivedSeries_one _))))
    · exact key ((h.derivedEquiv (e₂.symm.trans e₁)).symm.trans
        (MulEquiv.subgroupCongr (derivedSeries_one _)))
        (outer_comm_commutator_orthogonalMinus_of_three_le hk3 hirr hF)

end CFSG.OddTranspositions.PartFour
