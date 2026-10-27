module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7UInterMIndex
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7SylowCardEight
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7UIsPGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseCentralizerSylow
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.IndexNormalSup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupOddCoreNormal
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # The index of `H ∩ M` in `H` in the A7 case -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the A7 case, `H ∩ M` has index three in `H`. -/
public theorem secondCase_a7_H_inter_M_relIndex_eq_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    (c.H ⊓ w.M).relIndex c.H = 3 := by
  classical
  obtain ⟨SM, hSMcent, _SE, _hSEamb⟩ :=
    secondCase_centralizer_contains_sylow c w d
  obtain ⟨SM0, hSM0card⟩ :=
    secondCase_a7_sylow_card hmin c w d hA7 hmodel
  have hSMcard : Nat.card (SM : Subgroup w.M) = 8 :=
    (Nat.card_congr (Sylow.equiv SM0 SM).toEquiv).symm.trans hSM0card
  let T : Subgroup G := (SM : Subgroup w.M).map w.M.subtype
  have hTcard : Nat.card T = 8 := by
    rw [Subgroup.card_map_of_injective w.M.subtype_injective, hSMcard]
  have hScard : Nat.card (c.S : Subgroup G) = 8 :=
    secondCase_a7_S_card_eq_eight hmin c w d hA7 hmodel
  have hTleM : T ≤ w.M := Subgroup.map_subtype_le (SM : Subgroup w.M)
  have hTleH : T ≤ c.H := by
    rw [c.H_eq_centralizer]
    exact hSMcent
  have hUnormalH : IsNormalIn c.U c.H := centralizerSetup_U_isNormalIn_H c
  have hUleH : c.U ≤ c.H := hUnormalH.1
  have hTnormU : T ≤ Subgroup.normalizer (c.U : Set G) :=
    hTleH.trans (le_normalizer_of_isNormalIn hUnormalH)
  have hSnormU : (c.S : Subgroup G) ≤
      Subgroup.normalizer (c.U : Set G) :=
    (centralizerSetup_S_le_H c).trans
      (le_normalizer_of_isNormalIn hUnormalH)
  have hUp : IsPGroup 3 c.U :=
    secondCase_a7_U_isPGroup_three hmin c w d hA7 hmodel
  have hTp : IsPGroup 2 T := SM.isPGroup'.map w.M.subtype
  have hSp : IsPGroup 2 (c.S : Subgroup G) := c.S.isPGroup'
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUTdisj : Disjoint c.U T :=
    IsPGroup.disjoint_of_ne 3 2 (by omega) c.U T hUp hTp
  have hUSdisj : Disjoint c.U (c.S : Subgroup G) :=
    IsPGroup.disjoint_of_ne 3 2 (by omega) c.U c.S hUp hSp
  have hUTcard : Nat.card (c.U ⊔ T : Subgroup G) =
      Nat.card c.U * Nat.card T :=
    card_sup_eq_mul_of_disjoint_of_le_normalizer c.U T hTnormU hUTdisj
  have hUScard : Nat.card (c.U ⊔ (c.S : Subgroup G) : Subgroup G) =
      Nat.card c.U * Nat.card (c.S : Subgroup G) :=
    card_sup_eq_mul_of_disjoint_of_le_normalizer
      c.U c.S hSnormU hUSdisj
  have hHSU : (c.S : Subgroup G) ⊔ c.U = c.H :=
    fact_2_preamble_H_eq_SU_proved hmin c
  have hHcard : Nat.card c.H =
      Nat.card c.U * Nat.card (c.S : Subgroup G) := by
    rw [← hHSU, sup_comm]
    exact hUScard
  have hcardEq : Nat.card c.H = Nat.card (c.U ⊔ T : Subgroup G) := by
    rw [hHcard, hUTcard, hScard, hTcard]
  have hUTeqH : c.U ⊔ T = c.H := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le hUleH hTleH)
    rw [← hcardEq]
  let C : Subgroup G := c.H ⊓ w.M
  have hTleC : T ≤ C := le_inf hTleH hTleM
  have hUCeqH : c.U ⊔ C = c.H := by
    apply le_antisymm
    · exact sup_le hUleH inf_le_left
    · rw [← hUTeqH]
      exact sup_le le_sup_left (hTleC.trans le_sup_right)
  let U0 : Subgroup c.H := c.U.subgroupOf c.H
  let C0 : Subgroup c.H := C.subgroupOf c.H
  have hU0normal : U0.Normal := by
    exact Subgroup.normal_subgroupOf_of_le_normalizer
      (le_normalizer_of_isNormalIn hUnormalH)
  have hsubSup : (c.U ⊔ C).subgroupOf c.H = ⊤ := by
    rw [hUCeqH]
    exact Subgroup.subgroupOf_self c.H
  have hU0C0top : U0 ⊔ C0 = ⊤ := by
    apply top_unique
    intro x _
    have hxUC : (x : G) ∈ c.U ⊔ C := by
      rw [hUCeqH]
      exact x.2
    have hxSub : x ∈ (c.U ⊔ C).subgroupOf c.H :=
      Subgroup.mem_subgroupOf.mpr hxUC
    rw [Subgroup.subgroupOf_sup hUleH inf_le_left] at hxSub
    exact hxSub
  have hindex :=
    index_eq_relIndex_inf_of_normal_sup U0 C0 hU0normal hU0C0top
  have hinter : U0 ⊓ C0 = (c.U ⊓ w.M).subgroupOf c.H := by
    ext x
    constructor
    · intro hx
      have hxU : (x : G) ∈ c.U := Subgroup.mem_subgroupOf.mp hx.1
      have hxC : (x : G) ∈ C := Subgroup.mem_subgroupOf.mp hx.2
      exact Subgroup.mem_subgroupOf.mpr ⟨hxU, hxC.2⟩
    · intro hx
      have hxUM : (x : G) ∈ c.U ⊓ w.M := Subgroup.mem_subgroupOf.mp hx
      refine ⟨Subgroup.mem_subgroupOf.mpr hxUM.1, ?_⟩
      exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hxUM.2⟩
  have hright : (U0 ⊓ C0).relIndex U0 =
      (c.U ⊓ w.M).relIndex c.U := by
    rw [hinter]
    simpa [U0] using
      (Subgroup.relIndex_subgroupOf
        (H := c.U ⊓ w.M) (K := c.U) (L := c.H) hUleH)
  calc
    (c.H ⊓ w.M).relIndex c.H = C0.index := by rfl
    _ = (U0 ⊓ C0).relIndex U0 := hindex
    _ = (c.U ⊓ w.M).relIndex c.U := hright
    _ = 3 := secondCase_a7_U_inter_M_relIndex_eq_three
      hmin c w d hA7 hmodel

end CFSG.GorensteinWalter
