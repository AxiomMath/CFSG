module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma23Core
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27TwoCoreTrivial
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27PiCentralizes
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27CommutatorCentralizes
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27CommutatorInPiCompl
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27ComponentLayer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27PiCoreInversion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26

namespace CFSG
end CFSG
open CFSG

/-!
# Lemma 2.7, first conjunct

The `[M, ⟨t⟩] ≤ F_{πᶜ}(M)` half of Lemma 2.7, extracted below `Lemma27`
so the final `[S,U] ≰ F(U)` transfer can import it without a cycle.
-/

namespace CFSG.GorensteinWalter

universe u

noncomputable section

open scoped Pointwise

/-- `t ∈ O₂(Ĥ)`, the consequence of Theorem 2.6 used in Lemma 2.7. -/
private theorem lemma_2_7_t_mem_twoCore
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) :
    c.t ∈ twoCoreOf c.Hhat := by
  rcases theorem_2_6 hmin c with ⟨_hU, hSinter, _halternative⟩
  have htS : c.t ∈ (c.S : Subgroup G) := c.S0_le_S c.t_mem_S0
  have htC : c.t ∈ Subgroup.centralizer (c.U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzH : z ∈ c.H := by
      exact SetLike.le_def.1 (Subgroup.map_subtype_le (H := c.H)
        (pPrimeCore 2 c.H)) hz
    have hzCent : z ∈ Subgroup.centralizer ({c.t} : Set G) := by
      rw [← c.H_eq_centralizer]
      exact hzH
    have hcomm : c.t * z = z * c.t :=
      (Subgroup.mem_centralizer_iff (g := z) (s := ({c.t} : Set G))).1 hzCent c.t (by simp)
    exact hcomm.symm
  rw [← hSinter]
  exact ⟨htS, htC⟩

/-- `t ∈ M`: the same Theorem 2.6 consequence transported through
`NormalizerControlledBy c.Hhat M`. -/
private theorem lemma_2_7_t_mem_M
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (hM : Lemma27Hypothesis c M) :
    c.t ∈ M :=
  t_mem_M_of_centralizerStructure c M hM (theorem_2_6 hmin c)

/-- The first conjunct of Lemma 2.7: `[M, ⟨t⟩] ≤ F_{πᶜ}(M)`. -/
public theorem lemma_2_7_commutator_le_piCore_compl
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (hM : Lemma27Hypothesis c M) :
    let π := primesOfOrder (fittingSubgroupOf c.Hhat)
    ⁅M, Subgroup.zpowers c.t⁆ ≤ piCoreOf (fittingSubgroupOf M) πᶜ := by
  classical
  intro π
  have h26 : CentralizerStructure c := theorem_2_6 hmin c
  have hO2 : twoCoreOf M = ⊥ :=
    twoCoreOf_eq_bot_of_Lemma27Hypothesis hmin c M hM
  have hE : componentLayerOf M = ⊥ :=
    componentLayerOf_eq_bot_of_Lemma27Hypothesis hmin c M hM h26
  have htM : c.t ∈ M := lemma_2_7_t_mem_M hmin c M hM
  have htTwo : c.t ∈ twoCoreOf c.Hhat := lemma_2_7_t_mem_twoCore hmin c
  have hControl : NormalizerControlledBy c.Hhat M := hM.2.1
  have htwo : c.t ∈ Subgroup.centralizer (twoCoreOf M : Set G) := by
    rw [hO2]
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    simp at hx
    rw [hx]
    simp
  have hAcent : c.t ∈ Subgroup.centralizer
      (piCoreOf (fittingSubgroupOf M) π : Set G) :=
    t_centralizes_piCoreOf_fittingSubgroupOf_of_centralizes_twoCore
      (minimalCounterexample_isSimple hmin) c M hControl htwo htTwo
  rcases lemma_2_7_piCore_disjoint_and_inverted hmin c M hControl with
    ⟨_hDdisj, hInv⟩
  have hBinv : ∀ x : G,
      x ∈ (piCoreOf (fittingSubgroupOf M) πᶜ : Set G) →
        c.t * x * c.t⁻¹ = x⁻¹ := hInv htM
  have hCommCent : ⁅M, Subgroup.zpowers c.t⁆ ≤
      Subgroup.centralizer ((fittingSubgroupOf M : Subgroup G) : Set G) :=
    commutator_centralizes_fittingSubgroupOf_of_centralizes_inverts
      M c.t htM c.t_involution π hAcent hBinv
  have hKleM : ⁅M, Subgroup.zpowers c.t⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro m hm z hz
    have hzM : z ∈ M := (Subgroup.zpowers_le.mpr htM) hz
    exact M.mul_mem (M.mul_mem (M.mul_mem hm hzM) (M.inv_mem hm))
      (M.inv_mem hzM)
  have hCommF : ⁅M, Subgroup.zpowers c.t⁆ ≤ fittingSubgroupOf M :=
    le_fittingSubgroupOf_of_le_centralizer_fittingSubgroupOf_of_componentLayer_eq_bot
      M (⁅M, Subgroup.zpowers c.t⁆) hKleM hCommCent hE
  exact commutator_le_piCoreOf_compl_of_centralizes_fitting_of_twoCore_bot
    M c.t c.t_involution π hCommF hCommCent hO2 hAcent hBinv

end

end CFSG.GorensteinWalter
