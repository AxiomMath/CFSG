module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseInvertedOddCoreDisjoint
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFittingInvolutionDecomposition
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: the decomposition's inverted subgroup misses `O₂′(M)`
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The inverted subgroup `K` from equations (1)--(2) has trivial
intersection with the maximal subgroup's odd core. -/
public theorem secondCase_involution_K_inf_oddCore_eq_bot
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) :
    ∃ K B : Subgroup G, ∃ s : d.E,
      (K : Set G) = invertedElements (c.U ⊓ w.M) (s : G) ∧
      IsCyclic K ∧
      B = centralizerIn (c.U ⊓ w.M) (s : G) ∧
      K ⊔ B = c.U ⊓ w.M ∧
      K ⊓ oddCoreOf w.M = ⊥ := by
  classical
  obtain ⟨SM, hSMcent, SE, hSEamb, T, s, hsSE, hsI, hTcyc,
      hq_s_not_T, hinvT, hcontainT, hUEbar_le_T, hUEbar_cyclic,
      hUEbar_inv, K, B, hK_eq, hK_cyc, hB_def, hjoinX, K0, F,
      hK0_def, hF_def, hF_eq, hjoinY⟩ :=
    secondCase_fitting_involution_decomposition c w d
  have hKleX : K ≤ c.U ⊓ w.M := by
    intro x hx
    change x ∈ (K : Set G) at hx
    rw [hK_eq] at hx
    exact hx.1
  have hUodd : Odd (Nat.card (↥c.U)) := by
    change Odd (Nat.card (↥(oddCoreOf c.H)))
    exact odd_card_oddCoreOf c.H
  have hKodd : Odd (Nat.card (↥K)) :=
    Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le (hKleX.trans inf_le_left))
  have hEcentO := secondCase_component_centralizes_oddCore c w d
  have hKinv : ∀ x : G, x ∈ K →
      (s : G) * x * (s : G)⁻¹ = x⁻¹ := by
    intro x hx
    change x ∈ (K : Set G) at hx
    rw [hK_eq] at hx
    exact hx.2
  have hdisj := secondCase_inverted_inf_oddCore_eq_bot
    (M := w.M) (E := d.E) (K := K) (s : G) s.2 hEcentO hKodd hKinv
  exact ⟨K, B, s, hK_eq, hK_cyc, hB_def, hjoinX, hdisj⟩

end CFSG.GorensteinWalter
