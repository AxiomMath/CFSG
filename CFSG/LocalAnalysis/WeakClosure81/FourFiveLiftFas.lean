module

public import CFSG.LocalAnalysis.WeakClosure81.FourFiveBridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open Subgroup
open scoped Pointwise

private theorem fourFive_subgroupOf_le_subgroupOf_iff {G : Type} [Group G] {X Y H : Subgroup G}
    (hX : X ≤ H) (hY : Y ≤ H) : X.subgroupOf H ≤ Y.subgroupOf H ↔ X ≤ Y := by
  constructor
  · intro h
    have h' := Subgroup.map_mono (f := H.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hX, Subgroup.map_subgroupOf_eq_of_le hY] at h'
  · exact Subgroup.subgroupOf_mono H

private theorem fourFive_conjSub_subgroupOf {G : Type} [Group G] {X H : Subgroup G}
    (hX : X ≤ H) (g : ↥H) :
    conjSub g (X.subgroupOf H) = (conjSub (g : G) X).subgroupOf H := by
  ext y
  simp only [mem_conjSub_iff, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]

theorem fourFive_le_of_fas {G : Type} [Group G] [Finite G] {H S C G₂ : Subgroup G} {j : ℕ}
    (hSH : IsSylowIn 2 S H) (hCS : C ≤ S) [(C.subgroupOf H).Normal]
    (hF : fourFiveFAS j (↥H ⧸ C.subgroupOf H))
    {Γ : Set (Subgroup G)} (hΓ : E1.IsInvColl H Γ) (hne : ∃ B ∈ Γ, ¬ B ≤ C)
    (hP : ∀ B ∈ Γ, B ≤ S → ¬ B ≤ C → ∀ P : Subgroup G, E1.IsE j H S B P → twoResidual P ≤ G₂)
    (hSG : S ≤ G₂) : H ≤ G₂ := by
  have hSHle : S ≤ H := hSH.le
  have hCH : C ≤ H := hCS.trans hSHle
  set π : ↥H →* (↥H ⧸ C.subgroupOf H) := QuotientGroup.mk' (C.subgroupOf H) with hπdef
  set T' : Subgroup ↥H := S.subgroupOf H with hT'def
  set C' : Subgroup ↥H := C.subgroupOf H with hC'def
  set G₂' : Subgroup ↥H := G₂.subgroupOf H with hG₂'def
  have hπ : Function.Surjective π := by
    rw [hπdef]
    exact QuotientGroup.mk'_surjective _
  have hker : π.ker = C' := by
    rw [hπdef, hC'def]
    exact QuotientGroup.ker_mk' _
  have hT' : IsSylowIn 2 T' (⊤ : Subgroup ↥H) := by
    rw [hT'def]
    simpa [Subgroup.subgroupOf_self] using
      (E1.isSylowIn_subgroupOf_iff (H := H) hSHle le_rfl).mpr hSH
  set Tb : Subgroup (↥H ⧸ C.subgroupOf H) := T'.map π with hTbdef
  have hTb : IsSylowIn 2 Tb (⊤ : Subgroup (↥H ⧸ C.subgroupOf H)) := by
    rw [hTbdef]
    exact E1.isSylowIn_two_map_top hπ hT'
  set Ωb : Set (Subgroup (↥H ⧸ C.subgroupOf H)) :=
    {X | ∃ B ∈ Γ, ¬ B ≤ C ∧ X = (B.subgroupOf H).map π} with hΩbdef
  have hΩb : E1.IsInvColl (⊤ : Subgroup (↥H ⧸ C.subgroupOf H)) Ωb := by
    refine ⟨fun _ _ => le_top, ?_, ?_⟩
    · rintro X ⟨B, hB, -, rfl⟩
      exact ((hΓ.isElemAbelian B hB).subgroupOf H).map π
    · rintro X ⟨B, hB, hBC, rfl⟩ x -
      obtain ⟨h, rfl⟩ := hπ x
      rw [← E1.map_conjSub π h (B.subgroupOf H)]
      have hB_le : B ≤ H := hΓ.le B hB
      refine ⟨conjSub (h : G) B, hΓ.conj B hB h h.2, ?_, ?_⟩
      ·
        intro hle
        have hsub : conjSub h (B.subgroupOf H) ≤ C' := by
          rw [fourFive_conjSub_subgroupOf hB_le h, hC'def]
          exact Subgroup.subgroupOf_mono H hle
        have h2 := conjSub_mono (h⁻¹) hsub
        rw [← conjSub_mul, inv_mul_cancel, conjSub_one, hC'def] at h2
        have hconj : conjSub h⁻¹ (C.subgroupOf H) = C.subgroupOf H :=
          Subgroup.Normal.map_conj_eq (C.subgroupOf H) h⁻¹
        rw [hconj] at h2
        exact hBC ((fourFive_subgroupOf_le_subgroupOf_iff hB_le hCH).mp h2)
      · exact by rw [fourFive_conjSub_subgroupOf hB_le h]
  obtain ⟨B₀, hB₀, hB₀C⟩ := hne
  have hΩb_ne : Ωb.Nonempty := ⟨(B₀.subgroupOf H).map π, B₀, hB₀, hB₀C, rfl⟩
  have hΩb_bot : ∀ A ∈ Ωb, A ≠ ⊥ := by
    rintro A ⟨B, hB, hBC, rfl⟩ hbot
    apply hBC
    have hle : B.subgroupOf H ≤ C' := by
      have h1 : B.subgroupOf H ≤ π.ker := (Subgroup.map_eq_bot_iff (B.subgroupOf H)).mp hbot
      rwa [hker] at h1
    exact (fourFive_subgroupOf_le_subgroupOf_iff (hΓ.le B hB) hCH).mp (hC'def ▸ hle)
  have hcov := hF Tb Ωb hTb hΩb hΩb_ne hΩb_bot
  have hT'G₂ : T' ≤ G₂' := by
    rw [hT'def, hG₂'def]
    exact Subgroup.subgroupOf_mono H hSG
  have hTb_le : Tb ≤ G₂'.map π := by
    rw [hTbdef]
    exact Subgroup.map_mono hT'G₂
  have hC'G₂ : C' ≤ G₂' := by
    rw [hC'def, hG₂'def]
    exact Subgroup.subgroupOf_mono H (hCS.trans hSG)
  have hEgen : E1.eGen j (⊤ : Subgroup (↥H ⧸ C.subgroupOf H)) Tb Ωb ≤ G₂'.map π := by
    refine iSup₂_le fun X hX => iSup_le fun hXT => iSup₂_le fun K hK => ?_
    obtain ⟨B, hB, hBC, rfl⟩ := hX
    have hB_le : B ≤ H := hΓ.le B hB
    have hXT' : (B.subgroupOf H).map π ≤ T'.map π := by
      rw [hTbdef] at hXT
      exact hXT
    have hBS : B ≤ S := by
      have h1 : B.subgroupOf H ≤ (T'.map π).comap π :=
        (Subgroup.map_le_iff_le_comap).mp hXT'
      rw [Subgroup.comap_map_eq, hker, hT'def, hC'def] at h1
      have h2 : (B.subgroupOf H).map H.subtype ≤ (T' ⊔ C').map H.subtype :=
        Subgroup.map_mono h1
      rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hB_le,
        Subgroup.map_subgroupOf_eq_of_le hSHle, Subgroup.map_subgroupOf_eq_of_le hCH,
        sup_eq_left.mpr hCS] at h2
    have hB'T : B.subgroupOf H ≤ T' := by
      rw [hT'def]
      exact Subgroup.subgroupOf_mono H hBS
    rw [hTbdef] at hK
    obtain ⟨J, hJ, hJK⟩ :=
      E1.ten_seven (Y := C') hT' hB'T ((hΓ.isElemAbelian B hB).subgroupOf H) hK
    have hPJ : E1.IsE j H S B (J.map H.subtype) := by
      have h1 := (E1.isE_map_subtype H (i := j) (T' := T') (A' := B.subgroupOf H)
        (K' := J)).mpr hJ
      rwa [Subgroup.map_subgroupOf_eq_of_le hSHle,
        Subgroup.map_subgroupOf_eq_of_le hB_le] at h1
    have hJ_G₂ : twoResidual J ≤ G₂' := by
      have hmap : (twoResidual J).map H.subtype ≤ G₂ := by
        rw [E1.map_twoResidual]
        exact hP B hB hBS hBC (J.map H.subtype) hPJ
      rw [Subgroup.map_le_iff_le_comap] at hmap
      show twoResidual J ≤ G₂.subgroupOf H
      exact hmap
    calc K ≤ twoResidual K ⊔ (Tb ⊓ K) := E1.le_twoResidual_sup_of_isSylowIn hK.2.2.1
      _ ≤ G₂'.map π := by
        refine sup_le ?_ (le_trans inf_le_left hTb_le)
        rw [hJK]
        exact Subgroup.map_mono hJ_G₂
  intro x hx
  let h : ↥H := ⟨x, hx⟩
  have hmem : π h ∈ (E1.eGen j (⊤ : Subgroup (↥H ⧸ C.subgroupOf H)) Tb Ωb :
      Set (↥H ⧸ C.subgroupOf H)) * (Tb : Set (↥H ⧸ C.subgroupOf H)) := by
    rw [hcov]
    exact Set.mem_univ _
  rw [Set.mem_mul] at hmem
  obtain ⟨e, he, t, ht, het⟩ := hmem
  have hπh : π h ∈ G₂'.map π := by
    have he' : e ∈ G₂'.map π := hEgen he
    have ht' : t ∈ G₂'.map π := hTb_le ht
    rw [← het]
    exact (G₂'.map π).mul_mem he' ht'
  obtain ⟨g, hgG₂, hg_eq⟩ := hπh
  have hker_mem : g⁻¹ * h ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hg_eq, inv_mul_cancel]
  rw [hker] at hker_mem
  have hgh : g * (g⁻¹ * h) = h := by group
  have hhG₂ : h ∈ G₂' := by
    have := G₂'.mul_mem hgG₂ (hC'G₂ hker_mem)
    rwa [hgh] at this
  exact Subgroup.mem_subgroupOf.mp hhG₂

end CFSG.LocalAnalysis.WeakClosure81
