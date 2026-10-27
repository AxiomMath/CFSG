module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComponentLayerCentralizesSolvableNormalized
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27IndexTwo
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The selected component centralizes the maximal subgroup's odd core
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The selected component centralizes `O₂′(M)`. -/
public theorem secondCase_component_centralizes_oddCore
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) :
    d.E ≤ Subgroup.centralizer (oddCoreOf w.M : Set G) := by
  let M : Subgroup G := w.M
  let O : Subgroup G := oddCoreOf M
  have hOleM : O ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.2
  have hOodd : Odd (Nat.card (↥O)) := by
    simpa [O, M] using odd_card_oddCoreOf M
  have hOsolv : IsSolvable O := odd_order_theorem O hOodd
  have hOnorm : IsNormalIn O M := by
    refine ⟨hOleM, ?_⟩
    intro m hm o ho
    rcases Subgroup.mem_map.mp ho with ⟨o0, ho0, rfl⟩
    exact Subgroup.mem_map.mpr ⟨
      (⟨m, hm⟩ : M) * o0 * (⟨m, hm⟩ : M)⁻¹,
      (pPrimeCore_normal (p := 2) (G := M)).conj_mem
        o0 ho0 (⟨m, hm⟩ : M), by simp⟩
  have hEN : componentLayerOf M ≤
      Subgroup.normalizer (O : Set G) :=
    (componentLayerOf_isNormalIn M).1.trans
      (le_normalizer_of_isNormalIn hOnorm)
  have hcomm := componentLayerOf_centralizes_solvable_of_le_normalizer
    M O hOleM hOsolv hEN
  have hcent : componentLayerOf M ≤
      Subgroup.centralizer (O : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := componentLayerOf M) (H₂ := O)).mp hcomm
  have hEleLayer : d.E ≤ componentLayerOf M :=
    le_sSup (s := {E : Subgroup G | IsComponentOf E M}) d.E_component
  exact hEleLayer.trans hcent

end CFSG.GorensteinWalter
