module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveSix

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

theorem w16l_normalizer_preimage_le
    {G L : Type} [Group G] [Finite G] [Group L] [Finite L]
    {M U S H : Subgroup G} (hH : IsMinFam16 M U S H)
    (φ : ↥H →* L) (hφ : Function.Surjective φ)
    (A W : Subgroup L) (hA : A ≠ ⊥) (hAW : A ≤ W)
    (hAcore : A ⊓ CFSG.pCore 2 L = ⊥) (hW : IsPGroup 2 W)
    (hS : (S.subgroupOf H).map φ ≤ Subgroup.normalizer (W : Set L)) :
    (Subgroup.normalizer (W : Set L)).comap φ ≤ M.subgroupOf H := by
  let N : Subgroup ↥H := (Subgroup.normalizer (W : Set L)).comap φ
  let Y : Subgroup G := N.map H.subtype
  have hYH : Y ≤ H := Subgroup.map_subtype_le N
  have hSY : S ≤ Y := by
    intro s hs
    have hsH : s ∈ H := hH.1.1 hs
    have hmem : (⟨s, hsH⟩ : ↥H) ∈ N :=
      Subgroup.mem_comap.mpr (hS (Subgroup.mem_map.mpr
        ⟨⟨s, hsH⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩))
    exact Subgroup.mem_map.mpr ⟨⟨s, hsH⟩, hmem, rfl⟩
  have hYC : Y ≤ Subgroup.centralizer (U : Set G) := hYH.trans hH.1.2.1
  by_contra hNM
  obtain ⟨x, hxN, hxM⟩ := SetLike.not_le_iff_exists.mp hNM
  have hYM : ¬ Y ≤ M := by
    intro hle
    exact hxM (Subgroup.mem_subgroupOf.mpr
      (hle (Subgroup.mem_map.mpr ⟨x, hxN, rfl⟩)))
  have hYeq : Y = H := hH.2 Y hYH ⟨hSY, hYC, hYM⟩
  have hNtop : N = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    change Y = (⊤ : Subgroup ↥H).map H.subtype
    rw [hYeq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hnorm : Subgroup.normalizer (W : Set L) = ⊤ := by
    apply Subgroup.comap_injective hφ
    rw [Subgroup.comap_top]
    show N = ⊤
    exact hNtop
  have hWn : W.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm
  have hWle : W ≤ CFSG.pCore 2 L :=
    le_sSup (s := {K : Subgroup L | K.Normal ∧ IsPGroup 2 K}) ⟨hWn, hW⟩
  have hAle : A ≤ CFSG.pCore 2 L := hAW.trans hWle
  have hAbot : A = ⊥ := by
    rw [← hAcore, inf_eq_left.mpr hAle]
  exact hA hAbot

end CFSG.LocalAnalysis.WeakClosure81

end
