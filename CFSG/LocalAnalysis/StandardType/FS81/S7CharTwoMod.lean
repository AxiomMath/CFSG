module

public import CFSG.LocalAnalysis.StandardType.FS81.S7CentDefs
public import Mathlib.GroupTheory.Sylow
import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

private lemma fs81_mk_commutator_eq_one_iff {G : Type} [Group G] {H U : Subgroup G}
    [(U.subgroupOf H).Normal] (x y : ↥H) :
    ⁅(QuotientGroup.mk' (U.subgroupOf H) x), (QuotientGroup.mk' (U.subgroupOf H) y)⁆ = 1 ↔
      ⁅x, y⁆ ∈ U.subgroupOf H := by
  rw [← map_commutatorElement (QuotientGroup.mk' (U.subgroupOf H)) x y,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

private lemma fs81_mk_mem_centralizer_singleton_iff {G : Type} [Group G] {H U : Subgroup G}
    [(U.subgroupOf H).Normal] (x y : ↥H) :
    (QuotientGroup.mk' (U.subgroupOf H) x) ∈
        Subgroup.centralizer
          ({(QuotientGroup.mk' (U.subgroupOf H) y)} : Set (↥H ⧸ U.subgroupOf H)) ↔
      ⁅x, y⁆ ∈ U.subgroupOf H := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← commutatorElement_eq_one_iff_mul_comm,
    fs81_mk_commutator_eq_one_iff]

private lemma fs81_map_subgroupOf_sup_mk' {G : Type} [Group G] {H U P : Subgroup G}
    [(U.subgroupOf H).Normal] (hPH : P ≤ H) (hUH : U ≤ H) :
    ((P ⊔ U).subgroupOf H).map (QuotientGroup.mk' (U.subgroupOf H)) =
      (P.subgroupOf H).map (QuotientGroup.mk' (U.subgroupOf H)) := by
  have hUmap : (U.subgroupOf H).map (QuotientGroup.mk' (U.subgroupOf H)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    exact le_of_eq (QuotientGroup.ker_mk' (U.subgroupOf H)).symm
  rw [Subgroup.subgroupOf_sup hPH hUH, Subgroup.map_sup, hUmap, sup_bot_eq]

theorem charTwoMod_of_normal_pGroup_mod {G : Type} [Group G] [Finite G] {H U P : Subgroup G}
    [(U.subgroupOf H).Normal] {σ : G} (hUH : U ≤ H) (hσH : σ ∈ H) (hPH : P ≤ H)
    (hP : IsPGroup 2 P) (hPσ : ∀ x ∈ P, x * σ * x⁻¹ * σ⁻¹ ∈ U)
    (hnorm : ∀ x ∈ H, x * σ * x⁻¹ * σ⁻¹ ∈ U → ∀ y ∈ P, x * y * x⁻¹ ∈ P ⊔ U)
    (hcent : ∀ x ∈ H, (∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ U) → x ∈ P ⊔ U) :
    CharTwoMod H U ⟨σ, hσH⟩ := by
  let σH : ↥H := ⟨σ, hσH⟩
  let C : Subgroup (↥H ⧸ U.subgroupOf H) :=
    Subgroup.centralizer ({(QuotientGroup.mk σH : ↥H ⧸ U.subgroupOf H)} :
      Set (↥H ⧸ U.subgroupOf H))
  let Pq : Subgroup (↥H ⧸ U.subgroupOf H) :=
    (P.subgroupOf H).map (QuotientGroup.mk' (U.subgroupOf H))
  change CharTwo C
  have hPq_le_C : Pq ≤ C := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hz
    rw [Subgroup.mem_subgroupOf] at hp
    exact (fs81_mk_mem_centralizer_singleton_iff (U := U) p σH).mpr (by
      rw [Subgroup.mem_subgroupOf]
      simpa [σH, commutatorElement_def] using hPσ (p : G) hp)
  have hconj : ∀ c ∈ C, ∀ z ∈ Pq, c * z * c⁻¹ ∈ Pq := by
    intro c hc z hz
    obtain ⟨c₀, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf H) c
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hz
    rw [Subgroup.mem_subgroupOf] at hp
    have hc_comm : (c₀ : G) * σ * (c₀ : G)⁻¹ * σ⁻¹ ∈ U := by
      have h := (fs81_mk_mem_centralizer_singleton_iff (U := U) c₀ σH).mp hc
      rw [Subgroup.mem_subgroupOf] at h
      simpa [σH, commutatorElement_def] using h
    have hw_mem : (c₀ : G) * (p : G) * (c₀ : G)⁻¹ ∈ P ⊔ U :=
      hnorm (c₀ : G) c₀.2 hc_comm (p : G) hp
    have hmap : (QuotientGroup.mk' (U.subgroupOf H)) (c₀ * p * c₀⁻¹) ∈ Pq := by
      have hw : c₀ * p * c₀⁻¹ ∈ (P ⊔ U).subgroupOf H := by
        rw [Subgroup.mem_subgroupOf]
        simpa using hw_mem
      have h := (Subgroup.mem_map (f := QuotientGroup.mk' (U.subgroupOf H))).mpr
        ⟨c₀ * p * c₀⁻¹, hw, rfl⟩
      rwa [fs81_map_subgroupOf_sup_mk' (P := P) hPH hUH] at h
    simpa using hmap
  have hnorm_Pq : C ≤ Subgroup.normalizer (Pq : Set (↥H ⧸ U.subgroupOf H)) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · exact hconj c hc z
    · intro hz
      have h2 := hconj c⁻¹ (C.inv_mem hc) (c * z * c⁻¹) hz
      have h2' : c⁻¹ * (c * z * c⁻¹) * c⁻¹⁻¹ = z := by group
      rwa [h2'] at h2
  have hPq_normal : (Pq.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPq_le_C).mpr hnorm_Pq
  have hPq_two : IsPGroup 2 Pq := by
    have h1 : IsPGroup 2 (P.subgroupOf H) :=
      hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
    simpa [Pq] using h1.map (QuotientGroup.mk' (U.subgroupOf H))
  have hPq_le_pCore : Pq ≤ pCoreOf 2 C :=
    CFSG.LieType.BorelTits.le_pCoreOf (r := 2) hPq_le_C hPq_normal hPq_two
  intro c hc
  rw [Subgroup.mem_inf] at hc
  obtain ⟨hcC, hcCent⟩ := hc
  obtain ⟨c₀, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf H) c
  have hcomm_mem : ∀ y ∈ P, (c₀ : G) * y * (c₀ : G)⁻¹ * y⁻¹ ∈ U := by
    intro y hy
    have hy' : (⟨y, hPH hy⟩ : ↥H) ∈ P.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact hy
    have hyPq : (QuotientGroup.mk' (U.subgroupOf H)) ⟨y, hPH hy⟩ ∈ Pq := by
      simpa [Pq] using (Subgroup.mem_map (f := QuotientGroup.mk' (U.subgroupOf H))).mpr
        ⟨⟨y, hPH hy⟩, hy', rfl⟩
    have hcomm : ⁅(QuotientGroup.mk' (U.subgroupOf H)) c₀,
        (QuotientGroup.mk' (U.subgroupOf H)) ⟨y, hPH hy⟩⁆ = 1 :=
      (Subgroup.mem_centralizer_iff_commutator_eq_one'.mp hcCent) _
        (hPq_le_pCore hyPq)
    have h := (fs81_mk_commutator_eq_one_iff (U := U) c₀ ⟨y, hPH hy⟩).mp hcomm
    rw [Subgroup.mem_subgroupOf] at h
    simpa [commutatorElement_def] using h
  have hc₀_mem : (c₀ : G) ∈ P ⊔ U := hcent (c₀ : G) c₀.2 hcomm_mem
  have hc₀_sub : c₀ ∈ (P ⊔ U).subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    exact hc₀_mem
  have hcq : (QuotientGroup.mk' (U.subgroupOf H)) c₀ ∈ Pq := by
    have h := (Subgroup.mem_map (f := QuotientGroup.mk' (U.subgroupOf H))).mpr
      ⟨c₀, hc₀_sub, rfl⟩
    rwa [fs81_map_subgroupOf_sup_mk' (P := P) hPH hUH] at h
  exact hPq_le_pCore hcq

end CFSG.StandardType.FrameRoute.FS81

end
