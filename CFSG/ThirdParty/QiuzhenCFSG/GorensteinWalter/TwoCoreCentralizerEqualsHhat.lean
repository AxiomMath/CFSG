module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.TwoSubgroupCentralizingULeTwoCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FittingOddCoreEquality
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Equality of the two-cores of H and Hhat
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Theorem 2.6 implies `O2(H) = O2(Hhat)`. -/
public theorem twoCoreOf_H_eq_twoCoreOf_Hhat_of_centralizerStructure
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (h26 : CentralizerStructure c) :
    twoCoreOf c.H = twoCoreOf c.Hhat := by
  classical
  let P : Subgroup G := twoCoreOf c.H
  have hPp : IsPGroup 2 P := by
    change IsPGroup 2 ((pCore 2 c.H).map c.H.subtype)
    exact (pCore_isPGroup (p := 2) (G := c.H)).map c.H.subtype
  have hPleHhat : P ≤ c.Hhat := by
    intro p hp
    rcases Subgroup.mem_map.mp hp with ⟨pH, hpH, rfl⟩
    exact c.H_le_Hhat pH.2
  have hPcentU : P ≤ Subgroup.centralizer (c.U : Set G) := by
    simpa [P, CentralizerSetup.U] using twoCoreOf_centralizes_oddCoreOf c.H
  have hforward : P ≤ twoCoreOf c.Hhat :=
    twoSubgroup_le_twoCoreOf_Hhat_of_centralizes_U
      c h26 P hPp hPleHhat hPcentU
  let O : Subgroup G := twoCoreOf c.Hhat
  have hOleH : O ≤ c.H := by
    change twoCoreOf c.Hhat ≤ c.H
    rw [← h26.2.1]
    exact inf_le_left.trans (centralizerSetup_S_le_H c)
  have hOnormalHhat : IsNormalIn O c.Hhat := by
    refine ⟨?_, ?_⟩
    · exact Subgroup.map_subtype_le (pCore 2 c.Hhat)
    · intro z hz x hx
      rcases Subgroup.mem_map.mp hx with ⟨x0, hx0, rfl⟩
      exact Subgroup.mem_map.mpr
        ⟨(⟨z, hz⟩ : c.Hhat) * x0 * (⟨z, hz⟩ : c.Hhat)⁻¹,
          (pCore_normal (p := 2) (G := c.Hhat)).conj_mem
            x0 hx0 (⟨z, hz⟩ : c.Hhat), rfl⟩
  have hOnormalH : IsNormalIn O c.H := by
    refine ⟨hOleH, ?_⟩
    intro z hz x hx
    exact hOnormalHhat.2 z (c.H_le_Hhat hz) x hx
  let OH : Subgroup c.H := O.subgroupOf c.H
  have hOHnormal : OH.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hOleH]
    intro x z hx hz
    exact hOnormalH.2 z hz x hx
  have hOp : IsPGroup 2 O := by
    change IsPGroup 2 ((pCore 2 c.Hhat).map c.Hhat.subtype)
    exact (pCore_isPGroup (p := 2) (G := c.Hhat)).map c.Hhat.subtype
  have hOHp : IsPGroup 2 OH :=
    hOp.of_equiv (Subgroup.subgroupOfEquivOfLe hOleH).symm
  have hOHle : OH ≤ pCore 2 c.H := le_sSup ⟨hOHnormal, hOHp⟩
  have hmaple := Subgroup.map_mono (f := c.H.subtype) hOHle
  have hmapOH : OH.map c.H.subtype = O :=
    Subgroup.map_subgroupOf_eq_of_le hOleH
  have hreverse : O ≤ P := by
    simpa [P, O, twoCoreOf, hmapOH] using hmaple
  exact le_antisymm hforward hreverse

end CFSG.GorensteinWalter
