module

public import CFSG.LocalAnalysis.WeakClosure81.EightThreeInHat
public import CFSG.LocalAnalysis.WeakClosure81.EightSixIn

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

namespace AmbientH

variable {V H T : Subgroup G}

private theorem conjClosure_eq_iSup_conjSubgroup (V H : Subgroup G) :
    conjClosure V H = ⨆ g : ↥H, conjSubgroup V (g : G) := by
  refine le_antisymm ?_ ?_
  · refine conjClosure_le fun x hx z hz => ?_
    refine le_iSup (fun g : ↥H => conjSubgroup V (g : G)) ⟨x⁻¹, H.inv_mem hx⟩ ?_
    rw [mem_conjSubgroup_iff]
    change x⁻¹ * (x * z * x⁻¹) * (x⁻¹)⁻¹ ∈ V
    have h : x⁻¹ * (x * z * x⁻¹) * (x⁻¹)⁻¹ = z := by group
    rwa [h]
  · exact iSup_le fun g => conjSubgroup_le_conjClosure V H g.2

private theorem subgroupOf_conjClosure_eq_iSup_conjSubgroup (hVH : V ≤ H) :
    (conjClosure V H).subgroupOf H =
      ⨆ g : ↥H, conjSubgroup (V.subgroupOf H) g := by
  apply Subgroup.map_injective (Subgroup.subtype_injective H)
  rw [Subgroup.map_subgroupOf_eq_of_le (conjClosure_le_of_le_H hVH)]
  rw [Subgroup.map_iSup]
  rw [iSup_congr fun g => map_conjSubgroup_subgroupOf hVH g.2]
  exact conjClosure_eq_iSup_conjSubgroup V H

private theorem kSub_eq_iSup_conjSubgroup (h : Hyp83 V H T) :
    kSub (V.subgroupOf H) (⊤ : Subgroup ↥H)
        (eSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H)) =
      ⨆ g : ↥H, conjSubgroup (V.subgroupOf H) g := by
  have h' := hyp83 h
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun U hU => ?_
    obtain ⟨g, hUg, -, -⟩ := mem_omegaSet.mp hU
    rw [hUg]
    exact le_iSup (fun g : ↥H => conjSubgroup (V.subgroupOf H) g) g
  · refine iSup_le fun g => le_kSub ?_
    exact h'.conjSubgroup_self_mem_omegaSet (Subgroup.mem_top g)

theorem kSub_eq (h : Hyp83 V H T) :
    kSub (V.subgroupOf H) (⊤ : Subgroup ↥H)
        (eSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H)) =
      (conjClosure V H).subgroupOf H := by
  rw [kSub_eq_iSup_conjSubgroup h, subgroupOf_conjClosure_eq_iSup_conjSubgroup h.le_H]

private theorem kGen_eq_iSup_conjSubgroup (h : Hyp83 V H T) :
    kGen (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H) =
      ⨆ k : ↥H, ⨆ (_ : k ∈ kSub (V.subgroupOf H) (⊤ : Subgroup ↥H)
          (eSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H))),
        conjSubgroup (V.subgroupOf H) k := by
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun U hU => ?_
    obtain ⟨k, hk, rfl⟩ := mem_omegaOrb.mp hU
    exact le_iSup₂_of_le k hk le_rfl
  · refine iSup_le fun k => iSup_le fun hk => ?_
    exact le_kGen (conjSubgroup_mem_omegaOrb hk)

private theorem subgroupOf_kGenIn_eq_iSup (h : Hyp83 V H T) :
    (kGenIn V H).subgroupOf H =
      ⨆ k : ↥H, ⨆ (_ : k ∈ kSub (V.subgroupOf H) (⊤ : Subgroup ↥H)
          (eSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H))),
        conjSubgroup (V.subgroupOf H) k := by
  have hkeq : kSub (V.subgroupOf H) (⊤ : Subgroup ↥H)
      (eSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H)) =
      (conjClosure V H).subgroupOf H := kSub_eq h
  apply Subgroup.map_injective (Subgroup.subtype_injective H)
  rw [Subgroup.map_subgroupOf_eq_of_le (kGenIn_le_H h.le_H)]
  simp only [Subgroup.map_iSup]
  rw [iSup_congr fun k => iSup_congr fun _ => map_conjSubgroup_subgroupOf h.le_H k.2]
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun k hk => ?_
    have hkH : k ∈ H := conjClosure_le_of_le_H h.le_H hk
    refine le_iSup₂_of_le (⟨k, hkH⟩ : ↥H) ?_ le_rfl
    rw [hkeq]
    exact Subgroup.mem_subgroupOf.mpr hk
  · refine iSup_le fun k => iSup_le fun hk => ?_
    exact le_iSup₂_of_le (k : G) (Subgroup.mem_subgroupOf.mp (hkeq ▸ hk)) le_rfl

theorem kGen_eq (h : Hyp83 V H T) :
    kGen (V.subgroupOf H) (⊤ : Subgroup ↥H) (T.subgroupOf H) = (kGenIn V H).subgroupOf H := by
  rw [kGen_eq_iSup_conjSubgroup h, subgroupOf_kGenIn_eq_iSup h]

end AmbientH

end CFSG.LocalAnalysis.WeakClosure81

end
