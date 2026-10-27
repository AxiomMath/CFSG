module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeRel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem iSup_conjSubgroup_subgroupOf_eq {A H : Subgroup G} (hAH : A ≤ H) :
    ⨆ g : ↥H, conjSubgroup (A.subgroupOf H) g = (conjClosure A H).subgroupOf H := by
  apply le_antisymm
  · refine iSup_le fun g x hx => ?_
    rw [mem_conjSubgroup_iff] at hx
    have h1 := mem_conjClosure (Z := A) (H.inv_mem g.2) (Subgroup.mem_subgroupOf.mp hx)
    rw [Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using h1
  · intro x hx
    have hle : conjClosure A H ≤
        (⨆ g : ↥H, conjSubgroup (A.subgroupOf H) g).map H.subtype := by
      refine conjClosure_le fun h hh a ha => ?_
      refine ⟨⟨h, hh⟩ * ⟨a, hAH ha⟩ * ⟨h, hh⟩⁻¹, ?_, rfl⟩
      refine Subgroup.mem_iSup_of_mem (⟨h, hh⟩⁻¹ : ↥H) ?_
      rw [mem_conjSubgroup_iff, Subgroup.mem_subgroupOf]
      simpa [mul_assoc] using ha
    obtain ⟨y, hy, hyx⟩ := hle hx
    rwa [show y = x from Subtype.ext hyx] at hy

variable {V H E : Subgroup G}

theorem omegaSet_subgroupOf_top (hVH : V ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hV : V ∈ omegaSet V H E) :
    omegaSet (V.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H) =
      {U | ∃ g : ↥H, U = conjSubgroup (V.subgroupOf H) g} := by
  ext U
  constructor
  · rintro ⟨g, hU, -, -⟩
    exact ⟨g, hU⟩
  · rintro ⟨g, rfl⟩
    exact conjSubgroup_mem_omegaSet (G := ↥H) (V := V.subgroupOf H) (H := ⊤)
      (E := E.subgroupOf H) (W := V.subgroupOf H) le_top (hEnorm.subgroupOf ⊤)
      (subgroupOf_mem_omegaSet hV hVH) (Subgroup.mem_top g)

theorem kSub_subgroupOf_top (hVH : V ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hV : V ∈ omegaSet V H E) :
    kSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H) =
      (conjClosure V H).subgroupOf H := by
  rw [← iSup_conjSubgroup_subgroupOf_eq hVH, kSub, omegaSet_subgroupOf_top hVH hEnorm hV]
  apply le_antisymm
  · refine iSup₂_le fun U ⟨g, hU⟩ => ?_
    rw [hU]
    exact le_iSup (fun g : ↥H => conjSubgroup (V.subgroupOf H) g) g
  · exact iSup_le fun g => le_iSup₂_of_le (conjSubgroup (V.subgroupOf H) g) ⟨g, rfl⟩ le_rfl

theorem iSub_subgroupOf_top (hVH : V ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hV : V ∈ omegaSet V H E) :
    iSub (V.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H) =
      (conjClosure (V ⊓ pCoreOf 2 H) H).subgroupOf H := by
  rw [← iSup_conjSubgroup_subgroupOf_eq (A := V ⊓ pCoreOf 2 H) (inf_le_left.trans hVH), iSub,
    omegaSet_subgroupOf_top hVH hEnorm hV, pCoreOf_top_subgroupOf]
  have hO : ∀ g : ↥H, ∀ x : G, (g : G) * x * (g : G)⁻¹ ∈ pCoreOf 2 H ↔ x ∈ pCoreOf 2 H :=
    fun g x => (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H g.2) x).symm
  apply le_antisymm
  · refine iSup₂_le fun U ⟨g, hU⟩ => le_trans ?_ (le_iSup _ g)
    intro x hx
    obtain ⟨hxV, hxO⟩ := Subgroup.mem_inf.mp hx
    rw [hU, mem_conjSubgroup_iff] at hxV
    rw [mem_conjSubgroup_iff, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_subgroupOf.mp hxV, (hO g _).2 (Subgroup.mem_subgroupOf.mp hxO)⟩
  · refine iSup_le fun g => le_iSup₂_of_le (conjSubgroup (V.subgroupOf H) g) ⟨g, rfl⟩ ?_
    intro x hx
    rw [mem_conjSubgroup_iff, Subgroup.mem_subgroupOf] at hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_conjSubgroup_iff, Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_inf.mp hx).1
    · exact Subgroup.mem_subgroupOf.mpr ((hO g _).1 (Subgroup.mem_inf.mp hx).2)

end CFSG.LocalAnalysis.WeakClosure81
