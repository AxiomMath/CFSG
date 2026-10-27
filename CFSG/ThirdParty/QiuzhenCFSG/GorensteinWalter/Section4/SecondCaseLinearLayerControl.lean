module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationEightDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2NormalizerFittingAction
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2NormalizerLayerEquality

namespace CFSG
end CFSG
open CFSG

/-!
# Normalizer-layer control from the linear omega package

The aligned omega-data producer retains all equation-(4)--(7) facts needed
for the repeated normalizer-layer argument.  This module exposes that argument
once, so both the ambient-Sylow contradiction and the final equation-(9)
constructor use the same source-faithful interface.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Every nontrivial subgroup of the fixed factor has normalizer layer equal
to the selected PSL₂ component. -/
public theorem secondCase_linear_layer_eq_component_of_omegaData
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (od : SecondCaseLinearOmegaData c w d)
    (hsS : (od.s : G) ∈ (c.S : Subgroup G))
    (hsS0 : (od.s : G) ∉ c.S0) :
    ∀ X : Subgroup G, X ≠ ⊥ → X ≤ od.F →
      componentLayerOf (Subgroup.normalizer (X : Set G)) = d.E := by
  have hFleFU : od.F ≤ c.FU := by
    intro f hf
    rw [od.F_fixed] at hf
    exact hf.1.1
  have hFleM : od.F ≤ w.M := by
    intro f hf
    rw [od.F_fixed] at hf
    exact hf.1.2
  have hFne : od.F ≠ ⊥ := by
    intro hFbot
    have hPbot : od.P = ⊥ := by
      apply le_bot_iff.mp
      simpa [hFbot] using od.P_le_F
    have hp1 : od.p = 1 := by
      calc
        od.p = Nat.card od.P := od.P_card.symm
        _ = 1 := by rw [hPbot]; simp
    exact od.hp_prime.ne_one hp1
  intro X hXne hXleF
  have hcentral := secondCase_psl2_normalizer_fitting_action
    hmin c w d K hK e od.F X od.s od.F_fixed ⟨hsS, hsS0⟩
      hFleFU hFleM od.F_centralizes_E hXne hXleF
  exact secondCase_psl2_normalizer_layer_eq_component
    hmin c w d K hK e od.F X hFleFU hFleM od.F_centralizes_E
      od.F_normal_M hFne hXne hXleF hcentral

end CFSG.GorensteinWalter
