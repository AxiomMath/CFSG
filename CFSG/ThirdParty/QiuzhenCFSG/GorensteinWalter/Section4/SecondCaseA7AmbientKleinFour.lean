module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7KleinFourInComponent
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7EquationSix
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSup
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# An ambient Klein four centralizing the equation-(6) fixed subgroup
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the A7 branch there is a Klein four in `H ∩ M` that centralizes
`F(U) ∩ M`. -/
public theorem
    secondCase_a7_exists_ambient_kleinFour_centralizing_fitting_inter
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    ∃ V : Subgroup G, IsKleinFour V ∧
      V ≤ c.H ⊓ w.M ∧
      V ≤ Subgroup.centralizer
        ((c.FU ⊓ w.M : Subgroup G) : Set G) := by
  classical
  obtain ⟨K, B, s, _hsI, _hsH, hK_eq, hK_cyc, hB_def, hjoinX, hKcard, hKleE,
      K0, F, hK0_def, hF_def, hF_eq, hjoinY, hFnormalM,
      hFcentE, hFcyc, hK0card, hFcard⟩ :=
    secondCase_a7_equation6 hmin c w d hA7 hmodel
  obtain ⟨VE, hVEK, hVEcentUE, hVEcentt⟩ :=
    secondCase_a7_exists_kleinFour_centralizing_U_inter_E
      hmin c w d hA7 hmodel
  let E : Subgroup G := d.E
  let V : Subgroup G := VE.map E.subtype
  let eV : VE ≃* V :=
    Subgroup.equivMapOfInjective VE E.subtype E.subtype_injective
  have hVK : IsKleinFour V := {
    card_four := (Nat.card_congr eV.toEquiv).symm.trans hVEK.card_four
    exponent_two :=
      (Monoid.exponent_eq_of_mulEquiv eV.symm).trans hVEK.exponent_two
  }
  have hVleE : V ≤ E := Subgroup.map_subtype_le VE
  have hVleM : V ≤ w.M := hVleE.trans d.E_component.1
  have hVleH : V ≤ c.H := by
    intro v hv
    rcases Subgroup.mem_map.mp hv with ⟨vE, hvE, rfl⟩
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hVEcentt hvE)
    exact congrArg Subtype.val hcomm
  have hK0leE : K0 ≤ E := by
    rw [hK0_def]
    exact inf_le_right.trans hKleE
  have hK0leU : K0 ≤ c.U := by
    rw [hK0_def]
    exact inf_le_left.trans (fittingSubgroupOf_le c.U)
  have hVcentK0 : V ≤ Subgroup.centralizer (K0 : Set G) := by
    intro v hv
    rcases Subgroup.mem_map.mp hv with ⟨vE, hvVE, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    let kE : E := ⟨k, hK0leE hk⟩
    have hkUE : kE ∈ (c.U ⊓ E).subgroupOf E :=
      Subgroup.mem_subgroupOf.mpr ⟨hK0leU hk, hK0leE hk⟩
    have hcomm :=
      (Subgroup.mem_centralizer_iff.mp (hVEcentUE hvVE)) kE hkUE
    exact congrArg Subtype.val hcomm
  have hEcentF : E ≤ Subgroup.centralizer (F : Set G) :=
    Subgroup.le_centralizer_iff.mp hFcentE
  have hVcentF : V ≤ Subgroup.centralizer (F : Set G) :=
    hVleE.trans hEcentF
  have hVcentY : V ≤
      Subgroup.centralizer ((c.FU ⊓ w.M : Subgroup G) : Set G) := by
    have h : V ≤ Subgroup.centralizer
        ((fittingSubgroupOf c.U ⊓ w.M : Subgroup G) : Set G) := by
      rw [← hjoinY]
      exact le_centralizer_sup_of_le_centralizers hVcentK0 hVcentF
    simpa [CentralizerSetup.FU] using h
  have hVleC : V ≤ c.H ⊓ w.M := by
    intro v hv
    exact ⟨hVleH hv, hVleM hv⟩
  exact ⟨V, hVK, hVleC, hVcentY⟩

end CFSG.GorensteinWalter
