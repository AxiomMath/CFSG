module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFactorization
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The normality half of Section 4, equation (4)
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- If `F ≤ C_M(t)` is normalized there, and `F` centralizes the selected
component `E`, then the factorization `M = E C_M(t)` makes `F` normal in `M`.
This is the source-faithful normality half of equation (4); the separate
Fact 1.10(ii) model endpoint is not assumed here. -/
public theorem secondCase_fitting_normal_in_M_of_centralizes_component
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (F : Subgroup G)
    (hFleC : F ≤ Subgroup.centralizer ({c.t} : Set G) ⊓ w.M)
    (hFnormalC : IsNormalIn F
      (Subgroup.centralizer ({c.t} : Set G) ⊓ w.M))
    (hFcentE : F ≤ Subgroup.centralizer (d.E : Set G)) :
    IsNormalIn F w.M := by
  let E0 : Subgroup (↥w.M) := d.E.subgroupOf w.M
  let C0 : Subgroup (↥w.M) :=
    (Subgroup.centralizer ({c.t} : Set G) ⊓ w.M).subgroupOf w.M
  have hE0normal : E0.Normal := by
    rw [Subgroup.normal_subgroupOf_iff d.E_component.1]
    intro h k hh hk
    exact d.E_normal.2 k hk h hh
  have hsup0 : E0 ⊔ C0 = ⊤ := by
    have hM := secondCase_M_eq_component_sup_centralizer w d
    have hsub :
        (d.E ⊔ (Subgroup.centralizer ({c.t} : Set G) ⊓ w.M)).subgroupOf w.M = ⊤ := by
      rw [← hM]
      exact Subgroup.subgroupOf_self w.M
    simpa [E0, C0, Subgroup.subgroupOf_sup d.E_component.1 inf_le_right] using hsub
  refine ⟨hFleC.trans inf_le_right, ?_⟩
  intro m hm f hf
  let mM : w.M := ⟨m, hm⟩
  have hmSup : mM ∈ E0 ⊔ C0 := by
    rw [hsup0]
    trivial
  rcases (@Subgroup.mem_sup_of_normal_left (↥w.M) _ E0 C0 hE0normal mM).mp hmSup with
    ⟨e, he, z, hz, hmEq⟩
  have heE : (e : G) ∈ d.E := Subgroup.mem_subgroupOf.mp he
  have hzC : (z : G) ∈ Subgroup.centralizer ({c.t} : Set G) ⊓ w.M :=
    Subgroup.mem_subgroupOf.mp hz
  have hzNorm : (z : G) * f * (z : G)⁻¹ ∈ F :=
    hFnormalC.2 (z : G) hzC f hf
  have heComm : (e : G) * ((z : G) * f * (z : G)⁻¹) =
      ((z : G) * f * (z : G)⁻¹) * (e : G) :=
    (Subgroup.mem_centralizer_iff.mp (hFcentE hzNorm)) (e : G) heE
  have hconj : m * f * m⁻¹ =
      (e : G) * ((z : G) * f * (z : G)⁻¹) * (e : G)⁻¹ := by
    have hmEq' : m = (e : G) * (z : G) := by
      simpa [mM] using (congrArg Subtype.val hmEq).symm
    rw [hmEq']
    group
  rw [hconj]
  rw [heComm]
  simpa [mul_assoc] using hzNorm

end CFSG.GorensteinWalter
