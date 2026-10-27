module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7HInterMIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7KCenter
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7ANormalU
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.SupEqTopOfIndexEqNormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupOddCoreNormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18

namespace CFSG
end CFSG
open CFSG

/-! # Normality of the equation-(8) subgroup in the centralizer -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the A7 case, the order-nine subgroup `K F` is normal in
`H = C_G(t)`. -/
public theorem secondCase_a7_A_normal_H
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (od : SecondCaseA7OmegaData c w d) :
    IsNormalIn (od.K ⊔ od.F) c.H := by
  classical
  let A : Subgroup G := od.K ⊔ od.F
  let C : Subgroup G := c.H ⊓ w.M
  have hUnormalH : IsNormalIn c.U c.H := centralizerSetup_U_isNormalIn_H c
  have hUleH : c.U ≤ c.H := hUnormalH.1
  have hCleH : C ≤ c.H := inf_le_left
  let U0 : Subgroup c.H := c.U.subgroupOf c.H
  let C0 : Subgroup c.H := C.subgroupOf c.H
  have hU0normal : U0.Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    rw [Subgroup.le_normalizer_iff]
    intro h hh u hu
    exact hUnormalH.2 h hh u hu
  have hCindex : C0.index = 3 := by
    change C.relIndex c.H = 3
    exact secondCase_a7_H_inter_M_relIndex_eq_three hmin c w d hA7 hmodel
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
  have hUindex : (c.U ⊓ w.M).relIndex c.U = 3 :=
    secondCase_a7_U_inter_M_relIndex_eq_three hmin c w d hA7 hmodel
  have hindex : C0.index = (U0 ⊓ C0).relIndex U0 := by
    rw [hCindex, hright, hUindex]
  have hU0C0top : U0 ⊔ C0 = ⊤ :=
    sup_eq_top_of_index_eq_relIndex_inf_of_normal U0 C0 hU0normal hindex
  have hUCeqH : c.U ⊔ C = c.H := by
    apply le_antisymm
    · exact sup_le hUleH hCleH
    · intro h hh
      let h0 : c.H := ⟨h, hh⟩
      have hh0 : h0 ∈ U0 ⊔ C0 := by rw [hU0C0top]; trivial
      rw [← Subgroup.subgroupOf_sup hUleH hCleH] at hh0
      exact Subgroup.mem_subgroupOf.mp hh0
  have hAnormalU : IsNormalIn A c.U := by
    simpa [A] using secondCase_a7_A_normal_U hmin c w d hA7 hmodel od
  have hKnormalH : IsNormalIn od.K c.H := by
    rw [secondCase_a7_K_eq_center_U hmin c w d hA7 hmodel od]
    exact map_characteristic_isNormalIn_of_isNormalIn
      (K := Subgroup.center c.U) (hKchar := Subgroup.centerCharacteristic)
      hUnormalH
  have hUnormA : c.U ≤ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro u hu a ha
    exact hAnormalU.2 u hu a ha
  have hCnormK : C ≤ Subgroup.normalizer (od.K : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx k hk
    exact hKnormalH.2 x hx.1 k hk
  have hCnormF : C ≤ Subgroup.normalizer (od.F : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx f hf
    exact od.F_normal_M.2 x hx.2 f hf
  have hCnormA : C ≤ Subgroup.normalizer (A : Set G) := by
    change C ≤ Subgroup.normalizer ((od.K ⊔ od.F : Subgroup G) : Set G)
    exact (le_inf hCnormK hCnormF).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup od.K od.F)
  have hHnormA : c.H ≤ Subgroup.normalizer (A : Set G) := by
    rw [← hUCeqH]
    exact sup_le hUnormA hCnormA
  refine ⟨hAnormalU.1.trans hUleH, ?_⟩
  intro h hh a ha
  exact ((Subgroup.mem_normalizer_iff.mp (hHnormA hh)) a).mp ha

end CFSG.GorensteinWalter
