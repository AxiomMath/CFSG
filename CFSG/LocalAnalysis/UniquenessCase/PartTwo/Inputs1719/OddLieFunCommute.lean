module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FunHypOmega
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFun
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFunThree
import CFSG.LocalAnalysis.UniquenessCase.FundamentalOddCore
import CFSG.ClassicalInvolution.AschTight.Sec6GenFunCommute
import CFSG.ClassicalInvolution.Asc77.IsSylow2InIsSylowOf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.LocalAnalysis.UniquenessCase (IsFundamentalOver fundPred)
open CFSG.ClassicalInvolution.Asc77 (IsSylow2In oddCoreOf)
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)


theorem commutator_eq_bot_of_mem_funSet {X : Type} [Group X] [Finite X] {q : ℕ}
    (hΩ : HypOmegaGen {Kb : Subgroup X | IsFundamentalOver q Kb})
    (P : Sylow 2 X) {K₁ K₂ : Subgroup X}
    (hK₁ : K₁ ∈ FunSet (fundPred q) X (P : Subgroup X))
    (hK₂ : K₂ ∈ FunSet (fundPred q) X (P : Subgroup X)) (hne : K₁ ≠ K₂) :
    ⁅K₁, K₂⁆ = ⊥ := by
  have hO : ∀ K : Subgroup X, K ∈ FunSet (fundPred q) X (P : Subgroup X) →
      oddCoreOf K = ⊥ := by
    intro K hK
    have hmem : K ∈ {Kb : Subgroup X | IsFundamentalOver q Kb} := hK.1
    obtain ⟨z, hz⟩ := (hΩ.omega1 K hmem).1
    exact oddCoreOf_eq_bot_of_isFundamentalOver hK.1
      ⟨z, hz.mem, orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one⟩
  exact hΩ.commutator_eq_bot_of_isSylow2In_inf P hK₁.1 hK₂.1 hne (hO K₁ hK₁) (hO K₂ hK₂)
    (IsSylow2In.of_isSylowOf hK₁.2) (IsSylow2In.of_isSylowOf hK₂.2)

theorem k_FunCommuteThree_of_funHypOmega (h : K_FunHypOmega) : K_FunCommuteThree := by
  intro X _ _ r q hr hr2 hLie hqs hodd hL2 hL3 hRee _ P K₁ hK₁ K₂ hK₂ hne
  exact commutator_eq_bot_of_mem_funSet (h X r q hr hr2 hLie hqs hodd hL2 hL3 hRee)
    P hK₁ hK₂ hne

theorem k_FunCommute_of_funHypOmega (h : K_FunHypOmega) : K_FunCommute := by
  intro X _ _ r q hr hr2 hLie hqs hodd hL2 hL3 hRee _ P K₁ hK₁ K₂ hK₂ hne
  exact commutator_eq_bot_of_mem_funSet (h X r q hr hr2 hLie hqs hodd hL2 hL3 hRee)
    P hK₁ hK₂ hne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
