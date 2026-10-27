module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27IndexTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7FittingCentralizes
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public theorem secondCase_a7_fitting_centralizes_component
    {G : Type u} [Group G] [Finite G]
    (E M F : Subgroup G)
    (hEcomp : IsComponentOf E M)
    (hEnorm : IsNormalIn E M)
    (hFleM : F ≤ M)
    (hFodd : Odd (Nat.card F))
    (SE : Sylow 2 E)
    (hFcentSE : F ≤ Subgroup.centralizer
      (((SE : Subgroup E).map E.subtype : Subgroup G) : Set G))
    (eQ : Nonempty ((E ⧸ Subgroup.center E) ≃*
      alternatingGroup (Fin 7))) :
    F ≤ Subgroup.centralizer (E : Set G) := by
  let S : Subgroup G := (SE : Subgroup E).map E.subtype
  let SQ : Sylow 2 (E ⧸ Subgroup.center E) :=
    SE.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center E))
  let Sbar : Sylow 2 (alternatingGroup (Fin 7)) :=
    SQ.mapSurjective (f := eQ.some.toMonoidHom) eQ.some.surjective
  have hSsub : S.subgroupOf E = (SE : Subgroup E) := by
    ext x
    change (x : G) ∈ (SE : Subgroup E).map E.subtype ↔ x ∈ (SE : Subgroup E)
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : y = x := E.subtype_injective hxy
      subst y
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hSmap :
      ((S.subgroupOf E).map (QuotientGroup.mk' (Subgroup.center E))).map
          eQ.some.toMonoidHom = (Sbar : Subgroup (alternatingGroup (Fin 7))) := by
    rw [hSsub]
    rw [← Sylow.coe_mapSurjective
      (QuotientGroup.mk'_surjective (Subgroup.center E)) SE]
    exact Sylow.coe_mapSurjective (f := eQ.some.toMonoidHom)
      eQ.some.surjective SQ
  apply secondCase_a7_odd_subgroup_centralizes_component E M F S hEcomp hEnorm hFleM hFodd
    (by simpa [S] using hFcentSE) eQ Sbar hSmap

/-! Equation-(3) wrapper.  The fitting subgroup is contained in `U`, hence
centralizes `t`; its membership in the equation-(3) fixed part supplies
centralization of the selected reflection `s`. -/

/-- The `A₇` component-centralization endpoint from the equation-(3) data. -/
public theorem secondCase_a7_fitting_centralizes_component_of_reflection
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (F : Subgroup G)
    (hFleFU : F ≤ fittingSubgroupOf c.U)
    (hFleM : F ≤ w.M)
    (s : d.E)
    (hFcentS : F ≤ Subgroup.centralizer ({(s : G)} : Set G))
    (T : Subgroup (d.E ⧸ Subgroup.center d.E))
    (hTinv : ∀ x : d.E ⧸ Subgroup.center d.E, x ∈ T →
      QuotientGroup.mk' (Subgroup.center d.E) s * x *
        (QuotientGroup.mk' (Subgroup.center d.E) s)⁻¹ = x⁻¹)
    (hTcontain : ∀ X : Subgroup (d.E ⧸ Subgroup.center d.E),
      (∀ x : d.E ⧸ Subgroup.center d.E, x ∈ X → Odd (orderOf x)) →
        X ≤ Subgroup.centralizer
          ({(QuotientGroup.mk' (Subgroup.center d.E)
            ⟨c.t, d.t_mem_E⟩)} : Set (d.E ⧸ Subgroup.center d.E)) → X ≤ T)
    (eQ : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7))) :
    F ≤ Subgroup.centralizer (d.E : Set G) := by
  have hUleH : c.U ≤ c.H := by
    unfold CentralizerSetup.U oddCoreOf
    exact Subgroup.map_subtype_le (pPrimeCore 2 c.H)
  have hFoddU : Odd (Nat.card (↥c.U)) := by
    change Odd (Nat.card (↥(oddCoreOf c.H)))
    exact odd_card_oddCoreOf c.H
  have hFodd : Odd (Nat.card F) := by
    exact Odd.of_dvd_nat hFoddU
      (Subgroup.card_dvd_of_le (hFleFU.trans (fittingSubgroupOf_le c.U)))
  have hFcentT : F ≤ Subgroup.centralizer ({c.t} : Set G) := by
    intro f hf
    have hfH : f ∈ c.H := hUleH (fittingSubgroupOf_le c.U (hFleFU hf))
    rw [c.H_eq_centralizer] at hfH
    exact hfH
  exact secondCase_a7_odd_subgroup_centralizes_component_of_reflection
    d.E w.M F d.E_component d.E_normal hFleM hFodd
    ⟨c.t, d.t_mem_E⟩ s hFcentT hFcentS T hTinv hTcontain eQ


end CFSG.GorensteinWalter
