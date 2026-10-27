module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveIc

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

private theorem barSub_conjClosure_le_normalClosure {K A : Subgroup G} (hAK : A ≤ K)
    {X : Type} [Group X] (φ : ↥K →* X) :
    SevenK.barSub K φ (CFSG.Quasithin.conjClosure A K) ≤
      Subgroup.normalClosure ((SevenK.barSub K φ A : Subgroup X) : Set X) := by
  let N : Subgroup X := Subgroup.normalClosure ((SevenK.barSub K φ A : Subgroup X) : Set X)
  have hNnorm : N.Normal := Subgroup.normalClosure_normal
  have hNle : SevenK.barSub K φ A ≤ N := Subgroup.le_normalClosure
  have hL : CFSG.Quasithin.conjClosure A K ≤ (N.comap φ).map K.subtype := by
    refine CFSG.Quasithin.conjClosure_le fun h hh a ha => ?_
    let hK : ↥K := ⟨h, hh⟩
    let aK : ↥K := ⟨a, hAK ha⟩
    have hφa : φ aK ∈ N := hNle (SevenK.mem_barSub.mpr ⟨aK, ha, rfl⟩)
    have hconj : φ hK * φ aK * (φ hK)⁻¹ ∈ N := hNnorm.conj_mem (φ aK) hφa (φ hK)
    refine Subgroup.mem_map.mpr ⟨hK * aK * hK⁻¹, ?_, rfl⟩
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hconj
  calc SevenK.barSub K φ (CFSG.Quasithin.conjClosure A K)
      = ((CFSG.Quasithin.conjClosure A K).subgroupOf K).map φ := rfl
    _ ≤ (((N.comap φ).map K.subtype).subgroupOf K).map φ :=
        Subgroup.map_mono (Subgroup.subgroupOf_mono K hL)
    _ = (N.comap φ).map φ := by
        rw [← Subgroup.comap_subtype ((N.comap φ).map K.subtype) K,
          Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    _ ≤ N := Subgroup.map_comap_le φ N

theorem IsMinFam16.normalClosure_barSub_eq_top (h1 : W16One G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (conjClosure V H) (pCoreOf 2 (conjClosure V H)) φ) :
    normalClosure ((SevenK.barSub (conjClosure V H) φ V : Subgroup X) : Set X) = ⊤ := by
  let K : Subgroup G := conjClosure V H
  let N : Subgroup X :=
    Subgroup.normalClosure ((SevenK.barSub K φ V : Subgroup X) : Set X)
  have hgen : conjClosure V K = K :=
    IsMinFam16.conjClosure_conjClosure_eq h1 hS h hH hV
  have hVK : V ≤ K := CFSG.Quasithin.le_conjClosure V H
  have hle : SevenK.barSub K φ K ≤ N := by
    have h := barSub_conjClosure_le_normalClosure (K := K) (A := V) hVK φ
    rwa [hgen] at h
  have hbarK : SevenK.barSub K φ K = ⊤ := by
    change (K.subgroupOf K).map φ = ⊤
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective φ hφ.surjective
  rw [hbarK] at hle
  exact top_le_iff.mp hle

end CFSG.LocalAnalysis.WeakClosure81

end
