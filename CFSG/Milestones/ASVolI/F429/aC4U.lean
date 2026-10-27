module

public import CFSG.Milestones.ASVolI.F429.aC4Gen
public import CFSG.Milestones.ASVolI.F429.aC7U5
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU4
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Main
import CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.H13.Sec53F.BA

section U4

open CFSG.ClassicalGroups.UnitaryFlag CFSG.Quasithin.H13.U4Par

theorem burnsideF429a_key_U4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U4 2 f Gp M₁ M₂) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ Gp ⊓ (M₁ ⊓ M₂), r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  haveI := hyp.normal
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U4) hyp.toHypF_4_4g
  obtain ⟨Φ, e1, e2⟩ := burnsideF4gU4_exists_equiv marking
  have hB : (M₁ ⊓ M₂).subgroupOf Gp =
      (parP (burnsideF4gU4_fieldData marking) ⊓ parP2 (burnsideF4gU4_fieldData marking)).map
        Φ.toMonoidHom := by
    rw [burnsideF429a_subgroupOf_inf, h1, h2, e1, e2, Subgroup.map_inf_eq _ _ _ Φ.injective]
  have hH : hypTorus (burnsideF4gU4_fieldData marking) 2 0 ≤
      parP (burnsideF4gU4_fieldData marking) ⊓ parP2 (burnsideF4gU4_fieldData marking) := by
    rw [burnsideF4gU4Inv_parP_inf_parP2]
    exact hypTorus_le_hypBorel _
  exact burnsideF429a_key_of_model hyp.centralizer_trivial Φ hB
    (burnsideF4gU4Inv_pCore_borel _) hH fun β _ _ hβ1 hβ2 =>
      burnsideF429a_inner_of_borelAutData
        (CFSG.Quasithin.H13.Sec53F.Unit.borelAutData_u4 (burnsideF4gU4_fieldData marking)) β
        hβ1 hβ2

end U4

section U5

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.Sec53F.Unit

theorem burnsideF429a_key_U5 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U5 2 f Gp M₁ M₂) :
    ∀ r ∈ M₁ ⊓ M₂, ∀ k : ℕ, r ^ 2 ^ k = 1 →
      (∀ b ∈ Gp ⊓ (M₁ ⊓ M₂), r * b * r⁻¹ * b⁻¹ ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) → r ∈ Gp := by
  haveI := hyp.normal
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U5) hyp.toHypF_4_4g
  obtain ⟨Ψ, e1, e2⟩ := burnsideF429a_U5_equiv marking
  have hB : (M₁ ⊓ M₂).subgroupOf Gp =
      (u5PtP (burnsideF429a_U5_fieldData marking) ⊓
        u5LnP (burnsideF429a_U5_fieldData marking)).map Ψ.toMonoidHom := by
    rw [burnsideF429a_subgroupOf_inf, h1, h2, e1, e2, Subgroup.map_inf_eq _ _ _ Ψ.injective]
  have hH : (hypTorus (burnsideF429a_U5_fieldData marking) 2 1).map
      (hypProj (burnsideF429a_U5_fieldData marking) 2 1) ≤
      u5PtP (burnsideF429a_U5_fieldData marking) ⊓
        u5LnP (burnsideF429a_U5_fieldData marking) := by
    rw [u5PtP_inf_u5LnP]
    exact Subgroup.map_mono (hypTorus_le_hypBorel _)
  exact burnsideF429a_key_of_model hyp.centralizer_trivial Ψ hB burnsideF429a_U5_pCoreOf_borel hH
    fun β k hk hβ1 hβ2 => burnsideF429a_inner_of_borelAutDiag
      (borelAutDiag_u5 (burnsideF429a_U5_fieldData marking)) β hβ1 hβ2 hk

end U5

end CFSG.ASVolI
