module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7FittingCentralizesSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFittingNormal
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The A₇ equation-(4) package: the equation-(3) fitting subgroup is
central in the selected component and normal in the maximal subgroup. -/
public theorem secondCase_a7_fitting_equation4
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (F : Subgroup G)
    (hFleFU : F ≤ fittingSubgroupOf c.U)
    (hFleM : F ≤ w.M)
    (s : d.E)
    (hFcentS : F ≤ Subgroup.centralizer ({(s : G)} : Set G))
    (hF_eq : F = centralizerIn
      (fittingSubgroupOf c.U ⊓ w.M) (s : G))
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
    IsNormalIn F w.M := by
  have hFcentE := secondCase_a7_fitting_centralizes_component_of_reflection
    c w d F hFleFU hFleM s hFcentS T hTinv hTcontain eQ
  have hU_normalH : IsNormalIn c.U c.H := by
    refine ⟨?_, ?_⟩
    · exact Subgroup.map_subtype_le (pPrimeCore 2 c.H)
    · intro h hh x hx
      rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
      have hconj : (⟨h, hh⟩ : c.H) * p * (⟨h, hh⟩ : c.H)⁻¹ ∈
          pPrimeCore 2 c.H :=
        (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem
          p hp (⟨h, hh⟩ : c.H)
      exact Subgroup.mem_map.mpr
        ⟨(⟨h, hh⟩ : c.H) * p * (⟨h, hh⟩ : c.H)⁻¹, hconj, by simp⟩
  have hFUnormalH : IsNormalIn (fittingSubgroupOf c.U) c.H := by
    change IsNormalIn ((fittingSubgroup (↥c.U)).map c.U.subtype) c.H
    exact map_characteristic_isNormalIn_of_isNormalIn
      (K := fittingSubgroup (↥c.U)) (hKchar := by infer_instance)
      (hHnormal := hU_normalH)
  have hUleH : c.U ≤ c.H := by
    exact Subgroup.map_subtype_le (pPrimeCore 2 c.H)
  have hFleC : F ≤ Subgroup.centralizer ({c.t} : Set G) ⊓ w.M := by
    intro f hf
    have hfH : f ∈ c.H := hUleH
      (fittingSubgroupOf_le c.U (hFleFU hf))
    rw [c.H_eq_centralizer] at hfH
    exact ⟨hfH, hFleM hf⟩
  have hFnormalC : IsNormalIn F
      (Subgroup.centralizer ({c.t} : Set G) ⊓ w.M) := by
    refine ⟨hFleC, ?_⟩
    intro z hz f hf
    have hzH : z ∈ c.H := by
      rw [c.H_eq_centralizer]
      exact hz.1
    have hzM : z ∈ w.M := hz.2
    have hfFU : f ∈ fittingSubgroupOf c.U := hFleFU hf
    have hfM : f ∈ w.M := hFleM hf
    have hconjFU : z * f * z⁻¹ ∈ fittingSubgroupOf c.U :=
      hFUnormalH.2 z hzH f hfFU
    have hconjM : z * f * z⁻¹ ∈ w.M :=
      w.M.mul_mem (w.M.mul_mem hzM hfM) (w.M.inv_mem hzM)
    have hconjY : z * f * z⁻¹ ∈ fittingSubgroupOf c.U ⊓ w.M :=
      ⟨hconjFU, hconjM⟩
    have hconjCentE : z * f * z⁻¹ ∈
        Subgroup.centralizer (d.E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have he' : z⁻¹ * e * z ∈ d.E :=
        by simpa using d.E_normal.2 z⁻¹ (w.M.inv_mem hzM) e he
      have hfe : f * (z⁻¹ * e * z) = (z⁻¹ * e * z) * f :=
        (Subgroup.mem_centralizer_iff.mp (hFcentE hf))
          (z⁻¹ * e * z) he' |>.symm
      calc
        e * (z * f * z⁻¹) = z * ((z⁻¹ * e * z) * f) * z⁻¹ := by group
        _ = z * (f * (z⁻¹ * e * z)) * z⁻¹ := by rw [hfe]
        _ = (z * f * z⁻¹) * e := by group
    have hconjS : z * f * z⁻¹ ∈
        Subgroup.centralizer ({(s : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.mp hconjCentE) (s : G) s.2).symm
    rw [hF_eq]
    exact Subgroup.mem_inf.mpr ⟨hconjY, hconjS⟩
  exact secondCase_fitting_normal_in_M_of_centralizes_component
    c w d F hFleC hFnormalC hFcentE

end CFSG.GorensteinWalter
