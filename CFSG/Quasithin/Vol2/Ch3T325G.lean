module

public import CFSG.Quasithin.Vol2.Ch3Sec2Conj
public import CFSG.Quasithin.Background.F918P6

public section

namespace CFSG.Quasithin.H13.T325

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative Pointwise

section Dictionary

variable {G : Type} [Group G] {A : Subgroup G}

theorem mem_irrPlusOn_of_isIrrPlusIn [IsMulCommutative ↥A] {X T I : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (A : Set G)) (hT : T ≤ Subgroup.normalizer (A : Set G))
    (hI : IsIrrPlusIn X A T I) :
    I.subgroupOf A ∈ IrrPlusOn (onA A X) ⊤ (onA A T) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
  have hbase : I.subgroupOf A ∈ IrrPlus (onA A X) ⊤ :=
    (isIrrPlusBase_iff hX h1).1 ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨hbase, ?_⟩
  have hI'map : (I.subgroupOf A).map A.subtype = I := Subgroup.map_subgroupOf_eq_of_le h1
  have hC : (modFix (onA A X) ⊤).map A.subtype = A ⊓ Subgroup.centralizer (X : Set G) := by
    rw [map_modFix hX, map_subtype_top]
  have hW : (⨆ y ∈ onA A T, y • I.subgroupOf A).map A.subtype = conjClosure I T := by
    rw [map_biSup_smul hT, hI'map]
  have hirrI := (isIrr_tilde hbase).1
  refine ⟨hirrI, tilde_mono ?_, fun L' hL'W hL'irr hL'iso => ?_⟩
  · have := le_biSup_smul (V := ↥A) (onA A T) (I.subgroupOf A) (onA A T).one_mem
    rwa [one_smul] at this
  · set π := QuotientGroup.mk' (modFix (V := ↥A) (onA A X) ⊤) with hπ
    have hL'eq : tilde (onA A X) ⊤ (L'.comap π) = L' :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) L'
    have hfix : modFix (V := ↥A) (onA A X) ⊤ ≤ L'.comap π := fun v hv => by
      rw [Subgroup.mem_comap, hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff v).mpr hv]
      exact L'.one_mem
    have hJinv : IsModInv (onA A X) (L'.comap π) := fun a v hv => by
      rw [Subgroup.mem_comap] at hv ⊢
      exact hL'irr.1 a _ hv
    have hCJ : A ⊓ Subgroup.centralizer (X : Set G) ≤ (L'.comap π).map A.subtype := by
      rw [← hC]
      exact Subgroup.map_mono hfix
    have hJW : (L'.comap π).map A.subtype ≤ conjClosure I T ⊔
        A ⊓ Subgroup.centralizer (X : Set G) := by
      have h1' : L'.comap π ≤ (⨆ y ∈ onA A T, y • I.subgroupOf A) ⊔ modFix (onA A X) ⊤ := by
        rw [← comap_tilde]
        exact Subgroup.comap_mono hL'W
      have h2' := Subgroup.map_mono (f := A.subtype) h1'
      rwa [Subgroup.map_sup, hW, hC] at h2'
    have hXJ : X ≤ Subgroup.normalizer (((L'.comap π).map A.subtype : Subgroup G) : Set G) :=
      (isModInv_iff hX _).1 hJinv
    have hKinv : IsModInv (onA A X) (I.subgroupOf A ⊔ modFix (onA A X) ⊤) :=
      XMod.IsInv.sup hbase.2.1 (XMod.isInv_fixed ⊤)
    have hti : XMod.Iso ↥(onA A X) (tilde (onA A X) ⊤ (L'.comap π))
        (tilde (onA A X) ⊤ (I.subgroupOf A ⊔ modFix (onA A X) ⊤)) := by
      rw [hL'eq, tilde_sup_modFix]
      exact hL'iso
    have hiso₂ := isXSectionIso₂_of_iso_tilde hX hti
    have hJA : (L'.comap π).map A.subtype ≤ A := Subgroup.map_subtype_le _
    have hJC : (L'.comap π).map A.subtype ⊓ Subgroup.centralizer (X : Set G) =
        A ⊓ Subgroup.centralizer (X : Set G) :=
      le_antisymm (inf_le_inf_right _ hJA) (le_inf hCJ inf_le_right)
    have hKmap : (I.subgroupOf A ⊔ modFix (onA A X) ⊤).map A.subtype =
        I ⊔ A ⊓ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.map_sup, hI'map, hC]
    have hKC : (I ⊔ A ⊓ Subgroup.centralizer (X : Set G)) ⊓ Subgroup.centralizer (X : Set G) =
        A ⊓ Subgroup.centralizer (X : Set G) :=
      le_antisymm (inf_le_inf_right _ (sup_le h1 inf_le_left)) (le_inf le_sup_right inf_le_right)
    rw [hJC, hKmap, hKC] at hiso₂
    have hle := h7 _ hCJ hJW hXJ hiso₂
    rw [← hKmap, Subgroup.map_le_map_iff_of_injective A.subtype_injective] at hle
    have hle' := tilde_mono (X := onA A X) (W := ⊤) hle
    rwa [hL'eq, tilde_sup_modFix] at hle'

theorem actCompat_autOn_onA [IsMulCommutative ↥A] (X : Subgroup G) :
    ActCompat (MonoidHom.id ↥A) (autOn X A) (onA A X) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, hg, fun p => rfl⟩
  · intro a ha
    exact ⟨conjAct A a, ⟨a, ha, rfl⟩, fun p => rfl⟩

theorem biSup_smul_eq_of_actCompat {G₁ G₂ P : Type*} [Group G₁] [Group G₂] [CommGroup P]
    [MulDistribMulAction G₁ P] [MulDistribMulAction G₂ P] {X₁ : Subgroup G₁} {X₂ : Subgroup G₂}
    (h : ActCompat (MonoidHom.id P) X₁ X₂) (J : Subgroup P) :
    (⨆ y ∈ X₁, y • J) = ⨆ y ∈ X₂, y • J := by
  have key : ∀ (y₁ : G₁) (y₂ : G₂), (∀ p : P, y₁ • p = y₂ • p) → y₁ • J = y₂ • J := by
    intro y₁ y₂ hy
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨j, hj, hx⟩ => ⟨j, hj, (hy j).symm.trans hx⟩,
      fun ⟨j, hj, hx⟩ => ⟨j, hj, (hy j).trans hx⟩⟩
  refine le_antisymm (iSup₂_le fun y hy => ?_) (iSup₂_le fun y hy => ?_)
  · obtain ⟨a, ha, hya⟩ := h.fwd y hy
    rw [key y a hya]
    exact le_iSup₂_of_le a ha le_rfl
  · obtain ⟨b, hb, hby⟩ := h.bwd y hy
    rw [← key b y hby]
    exact le_iSup₂_of_le b hb le_rfl

end Dictionary

end CFSG.Quasithin.H13.T325
