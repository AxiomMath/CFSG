module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityChief
import CFSG.GroupTheory.ABGLocalTools.PStabilityModule
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped IsMulCommutative
open CFSG.ABGLocalTools (IsChiefFactorUnder)
open CFSG.LocalAnalysis.UniquenessCase.UCK (fixV)

variable {G : Type} [Group G] [Finite G]

theorem exists_rep_of_chief_factor {K U W : Subgroup G} {r : ℕ} [Fact r.Prime]
    (hUW : IsChiefFactorUnder r K U W) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod r) V) (_ : Finite V) (_ : Nontrivial V)
      (ρ : Representation (ZMod r) ↥K V),
      (∀ V₀ : Submodule (ZMod r) V, (∀ g : ↥K, ∀ v ∈ V₀, ρ g v ∈ V₀) → V₀ = ⊥ ∨ V₀ = ⊤) ∧
      ∀ A : Subgroup ↥K,
        (∀ u ∈ U, (∀ a ∈ A, (a : G) * u * (a : G)⁻¹ * u⁻¹ ∈ W) → u ∈ W) → fixV ρ A = ⊥ := by
  classical
  haveI hWn : (W.subgroupOf U).Normal := hUW.normal
  haveI hEl : IsElementaryAbelian r (↥U ⧸ W.subgroupOf U) := hUW.isElementaryAbelian
  haveI hnt : Nontrivial (↥U ⧸ W.subgroupOf U) := by
    rw [QuotientGroup.nontrivial_iff]
    intro htop
    exact hUW.1.ne ((Subgroup.subgroupOf_eq_top.mp htop).antisymm hUW.1.le).symm
  let ρ : Representation (ZMod r) ↥K (Additive (↥U ⧸ W.subgroupOf U)) :=
    (Units.coeHom _).comp (CFSG.ABGLocalTools.chiefRep (p := r) hUW.2.1 hUW.2.2.1)
  have happ : ∀ (k : ↥K) (u : ↥U), ρ k (Additive.ofMul (u : ↥U ⧸ W.subgroupOf U)) =
      Additive.ofMul ((CFSG.ABGLocalTools.chiefConj hUW.2.1 k u : ↥U) : ↥U ⧸ W.subgroupOf U) :=
    fun k u => CFSG.ABGLocalTools.chiefRep_apply_mk (p := r) hUW.2.1 hUW.2.2.1 k u
  refine ⟨Additive (↥U ⧸ W.subgroupOf U), inferInstance, inferInstance, inferInstance,
    inferInstance, ρ, ?_, ?_⟩
  · intro V₀ hV₀
    exact CFSG.ABGLocalTools.chiefRep_irreducible hUW V₀ (fun k v hv => hV₀ k v hv)
  · intro A hA
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨u, rfl⟩ := CFSG.ABGLocalTools.exists_ofMul_mk v
    have huW : (u : G) ∈ W := by
      refine hA (u : G) u.2 fun a ha => ?_
      have hfixed := hv a ha
      rw [happ] at hfixed
      have hmem : ((CFSG.ABGLocalTools.chiefConj hUW.2.1 a u : ↥U) : G)⁻¹ * u ∈ W :=
        Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp (Additive.ofMul.injective hfixed))
      have hcoe : ((CFSG.ABGLocalTools.chiefConj hUW.2.1 a u : ↥U) : G) =
          (a : G) * u * (a : G)⁻¹ := by
        rw [CFSG.ABGLocalTools.chiefConj_apply_coe]
      rw [hcoe] at hmem
      have h2 := hUW.2.2.2.1 (u : G) u.2 _ (W.inv_mem hmem)
      rwa [show (u : G) * (((a : G) * u * (a : G)⁻¹)⁻¹ * u)⁻¹ * (u : G)⁻¹ =
        (a : G) * u * (a : G)⁻¹ * (u : G)⁻¹ by group] at h2
    have hq : ((u : ↥U) : ↥U ⧸ W.subgroupOf U) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr huW)
    rw [Submodule.mem_bot, hq]
    rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
