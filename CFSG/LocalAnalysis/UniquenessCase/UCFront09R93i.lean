module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityChief
public import CFSG.GroupTheory.ThreeTranspositions.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
import CFSG.GroupTheory.ABGLocalTools.PStabilityModule
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93g
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open Subgroup
open scoped MatrixGroups IsMulCommutative
open CFSG.GroupTheory.ThreeTranspositions (HasE9)
open CFSG.LocalAnalysis.UniquenessCase.UCK (fixV)

variable {G : Type} [Group G] [Finite G]

theorem normalClosure_subgroupOf_eq_top {K Z : Subgroup G} (hZK : Z ≤ K)
    (hKgen : ∀ B : Subgroup G, B ≤ K → K ≤ normalizer (B : Set G) → Z ≤ B → B = K) :
    normalClosure ((Z.subgroupOf K : Subgroup ↥K) : Set ↥K) = ⊤ := by
  set Nc : Subgroup ↥K := normalClosure ((Z.subgroupOf K : Subgroup ↥K) : Set ↥K) with hNc
  haveI : Nc.Normal := Subgroup.normalClosure_normal
  have hDNc : Z.subgroupOf K ≤ Nc := Subgroup.subset_normalClosure
  have hsub : (Nc.map K.subtype).subgroupOf K = Nc := by
    rw [← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective Nc
  have hMle : Nc.map K.subtype ≤ K := Subgroup.map_subtype_le Nc
  have hnorm : K ≤ normalizer ((Nc.map K.subtype : Subgroup G) : Set G) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hMle).mp ?_
    rw [hsub]
    infer_instance
  have hZM : Z ≤ Nc.map K.subtype := fun z hz =>
    ⟨⟨z, hZK hz⟩, hDNc (Subgroup.mem_subgroupOf.mpr hz), rfl⟩
  rw [← hsub, hKgen _ hMle hnorm hZM, Subgroup.subgroupOf_self]

theorem chief_quot_cases (hK461 : UCK.K461) (hK462 : UCK.K462) {K Z U W : Subgroup G} {r : ℕ}
    (hKK : CFSG.Open.IsKGroup ↥K) (hE9 : ¬ HasE9 ↥K) (hKperf : ⁅K, K⁆ = K) (hZK : Z ≤ K)
    (hZ3 : Nat.card Z = 3)
    (hKgen : ∀ B : Subgroup G, B ≤ K → K ≤ normalizer (B : Set G) → Z ≤ B → B = K)
    (hr : r.Prime) (hUW : CFSG.ABGLocalTools.IsChiefFactorUnder r K U W)
    (hfix : ∀ u ∈ U, (∀ x ∈ Z, x * u * x⁻¹ * u⁻¹ ∈ W) → u ∈ W) :
    ∃ (N : Subgroup ↥K) (_ : N.Normal), ¬ 3 ∣ Nat.card N ∧
      ((∃ (F : Type) (_ : Field F) (_ : Finite F), Nonempty (↥K ⧸ N ≃* SL(2, F))) ∨
        (∃ n : ℕ, CFSG.Blueprint.LieModel (↥K ⧸ N) .PSL 2 2 n) ∨
        CFSG.Quasithin.IsExt (↥K ⧸ N)
          (fun V _ => CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 (⊤ : Subgroup V))
          (fun Y _ => CFSG.Quasithin.IsAlt 5 Y)) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI hWn : (W.subgroupOf U).Normal := hUW.normal
  haveI hEl : IsElementaryAbelian r (↥U ⧸ W.subgroupOf U) := hUW.isElementaryAbelian
  haveI : Nontrivial (↥U ⧸ W.subgroupOf U) := by
    rw [QuotientGroup.nontrivial_iff]
    intro htop
    exact hUW.1.ne ((Subgroup.subgroupOf_eq_top.mp htop).antisymm hUW.1.le).symm
  let ρ : Representation (ZMod r) ↥K (Additive (↥U ⧸ W.subgroupOf U)) :=
    (Units.coeHom _).comp (CFSG.ABGLocalTools.chiefRep (p := r) hUW.2.1 hUW.2.2.1)
  have happ : ∀ (k : ↥K) (u : ↥U), ρ k (Additive.ofMul (u : ↥U ⧸ W.subgroupOf U)) =
      Additive.ofMul ((CFSG.ABGLocalTools.chiefConj hUW.2.1 k u : ↥U) : ↥U ⧸ W.subgroupOf U) :=
    fun k u => CFSG.ABGLocalTools.chiefRep_apply_mk (p := r) hUW.2.1 hUW.2.2.1 k u
  have hirr : ∀ V₀ : Submodule (ZMod r) (Additive (↥U ⧸ W.subgroupOf U)),
      (∀ g : ↥K, ∀ v ∈ V₀, ρ g v ∈ V₀) → V₀ = ⊥ ∨ V₀ = ⊤ := fun V₀ hV₀ =>
    CFSG.ABGLocalTools.chiefRep_irreducible hUW V₀ (fun k v hv => hV₀ k v hv)
  have hfixV : fixV ρ (Z.subgroupOf K) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨u, rfl⟩ := CFSG.ABGLocalTools.exists_ofMul_mk v
    have huW : (u : G) ∈ W := by
      refine hfix (u : G) u.2 fun x hx => ?_
      let k : ↥K := ⟨x, hZK hx⟩
      have hfixed := hv k (Subgroup.mem_subgroupOf.mpr hx)
      rw [happ] at hfixed
      have hmem : ((CFSG.ABGLocalTools.chiefConj hUW.2.1 k u : ↥U) : G)⁻¹ * u ∈ W :=
        Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp (Additive.ofMul.injective hfixed))
      have hcoe : ((CFSG.ABGLocalTools.chiefConj hUW.2.1 k u : ↥U) : G) = x * u * x⁻¹ := by
        rw [CFSG.ABGLocalTools.chiefConj_apply_coe]
      rw [hcoe] at hmem
      have h2 := hUW.2.2.2.1 (u : G) u.2 _ (W.inv_mem hmem)
      rwa [show (u : G) * ((x * u * x⁻¹)⁻¹ * u)⁻¹ * (u : G)⁻¹ = x * u * x⁻¹ * (u : G)⁻¹ by
        group] at h2
    have hq : ((u : ↥U) : ↥U ⧸ W.subgroupOf U) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr huW)
    rw [Submodule.mem_bot, hq]
    rfl
  have hD3 : Nat.card (Z.subgroupOf K) = 3 := by
    rw [← hZ3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv
  have hperf : commutator ↥K = ⊤ := by
    haveI : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hKperf
    exact Group.IsPerfect.commutator_eq_top
  obtain ⟨hN3, hcases⟩ := quot_ker_cases hK461 hK462 hKK hE9 hperf hD3
    (normalClosure_subgroupOf_eq_top hZK hKgen) ρ hirr hfixV
  exact ⟨ρ.ker, inferInstance, hN3, hcases⟩

theorem exists_quot_cases_of_not_le (hK461 : UCK.K461) (hK462 : UCK.K462)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) {K Z O M : Subgroup G}
    (hKG : CFSG.Open.IsKGroup ↥(O ⊔ K)) (hE9 : ¬ HasE9 ↥K) (hZK : Z ≤ K)
    (hZ3 : Nat.card Z = 3) (hKM : K ≤ M) (hCZ : centralizer (Z : Set G) ≤ M)
    (hKperf : ⁅K, K⁆ = K)
    (hKgen : ∀ B : Subgroup G, B ≤ K → K ≤ normalizer (B : Set G) → Z ≤ B → B = K)
    (hKO : K ≤ normalizer (O : Set G)) (hO3 : ¬ 3 ∣ Nat.card O) (hOM : ¬ O ≤ M) :
    ∃ (N : Subgroup ↥K) (_ : N.Normal), ¬ 3 ∣ Nat.card N ∧
      ((∃ (F : Type) (_ : Field F) (_ : Finite F), Nonempty (↥K ⧸ N ≃* SL(2, F))) ∨
        (∃ n : ℕ, CFSG.Blueprint.LieModel (↥K ⧸ N) .PSL 2 2 n) ∨
        CFSG.Quasithin.IsExt (↥K ⧸ N)
          (fun V _ => CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 (⊤ : Subgroup V))
          (fun Y _ => CFSG.Quasithin.IsAlt 5 Y)) := by
  obtain ⟨r, U, W, hr, -, hUW, -, -, -, hfix⟩ :=
    exists_chief_factor_not_le hSch hKG hZK hZ3 hKM hCZ hKperf hKgen hKO hO3 hOM
  exact chief_quot_cases hK461 hK462 (CFSG.Open.IsKGroup.of_le hKG le_sup_right) hE9 hKperf
    hZK hZ3 hKgen hr hUW hfix

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
