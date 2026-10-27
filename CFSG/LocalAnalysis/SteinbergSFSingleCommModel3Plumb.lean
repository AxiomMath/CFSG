module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3Conj

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup

section Transport

theorem model3Plumb_mem_center {G : Type*} [Group G] {Y V : Subgroup G} (hVY : V ≤ Y)
    (w : ↥(V.subgroupOf Y)) :
    w ∈ center ↥(V.subgroupOf Y) ↔ ((w : ↥Y) : G) ∈ centralizer (V : Set G) := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hw h hh
    have hk := hw ⟨⟨h, hVY hh⟩, hh⟩
    have hk' := congrArg (fun x : ↥(V.subgroupOf Y) => ((x : ↥Y) : G)) hk
    simpa using hk'
  · intro hw g
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hw ((g : ↥Y) : G) (Subgroup.mem_subgroupOf.mp g.2)

theorem model3Plumb_center_map {G : Type*} [Group G] {Y V : Subgroup G} (hVY : V ≤ Y) :
    ((center ↥(V.subgroupOf Y)).map (V.subgroupOf Y).subtype).map Y.subtype =
      V ⊓ centralizer (V : Set G) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_subgroupOf.mp w.2, (model3Plumb_mem_center hVY w).mp hw⟩
  · intro hx
    obtain ⟨hxV, hxC⟩ := Subgroup.mem_inf.mp hx
    have hw : (⟨⟨x, hVY hxV⟩, hxV⟩ : ↥(V.subgroupOf Y)) ∈ center ↥(V.subgroupOf Y) :=
      (model3Plumb_mem_center hVY ⟨⟨x, hVY hxV⟩, hxV⟩).mpr hxC
    exact Subgroup.mem_map.mpr ⟨(V.subgroupOf Y).subtype ⟨⟨x, hVY hxV⟩, hxV⟩,
      Subgroup.mem_map.mpr ⟨⟨⟨x, hVY hxV⟩, hxV⟩, hw, rfl⟩, rfl⟩

theorem model3Plumb_conj_map {G : Type*} [Group G] {Y : Subgroup G} (S : Subgroup ↥Y)
    (τ : ↥Y) :
    (S.map (MulAut.conj τ⁻¹).toMonoidHom).map Y.subtype =
      (S.map Y.subtype).map (MulAut.conj (τ : G)⁻¹).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem model3Plumb_map_top {G : Type*} [Group G] {Y : Subgroup G} :
    (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact z.2
  · intro hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩

theorem Model3Concl.map_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    {V : Subgroup Y} {q : ℕ} (h : Model3Concl Y V q) :
    Model3Concl Y' (V.map e.toMonoidHom) q :=
  ⟨model3Conj_A_map e h.a, model3Conj_B_map e h.b, model3Conj_C_map e h.c⟩

theorem Model3Concl.of_subgroupOf {G : Type*} [Group G] {H Y V : Subgroup G} (hYH : Y ≤ H)
    {R : Subgroup ↥(Y.subgroupOf H)} (hR : R.map (Y.subgroupOf H).subtype = V.subgroupOf H)
    {q : ℕ} (h : Model3Concl ↥(Y.subgroupOf H) R q) :
    Model3Concl ↥Y (V.subgroupOf Y) q := by
  have hcomp : Y.subtype.comp (subgroupOfEquivOfLe hYH).toMonoidHom =
      H.subtype.comp (Y.subgroupOf H).subtype :=
    MonoidHom.ext fun _ => rfl
  have hchain : V ⊓ H = (R.map (subgroupOfEquivOfLe hYH).toMonoidHom).map Y.subtype := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hR, subgroupOf_map_subtype]
  have hle : V ⊓ H ≤ Y := by
    rw [hchain]
    intro x hx
    obtain ⟨z, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact z.2
  have hV : V ⊓ H = V ⊓ Y :=
    le_antisymm (le_inf inf_le_left hle) (le_inf inf_le_left (inf_le_right.trans hYH))
  have he : R.map (subgroupOfEquivOfLe hYH).toMonoidHom = V.subgroupOf Y := by
    apply Subgroup.map_injective (f := Y.subtype) Y.subtype_injective
    rw [← hchain, subgroupOf_map_subtype]
    exact hV
  have h' := Model3Concl.map_mulEquiv (subgroupOfEquivOfLe hYH) h
  rw [he] at h'
  exact h'

theorem Model3Concl.toSub {G : Type*} [Group G] {Y V : Subgroup G} (hVY : V ≤ Y) {q : ℕ}
    (h : Model3Concl ↥Y (V.subgroupOf Y) q) : Model3Sub Y V q := by
  obtain ⟨ha, hb, hc⟩ := h
  obtain ⟨hcard, hsq⟩ := ha
  have hWV : (V.subgroupOf Y).map Y.subtype = V :=
    (subgroupOf_map_subtype V Y).trans (inf_eq_left.mpr hVY)
  refine ⟨hVY, ?_, ?_, ?_, ?_⟩
  · rw [← model3Plumb_center_map hVY,
      Subgroup.card_map_of_injective (f := Y.subtype) Y.subtype_injective,
      Subgroup.card_map_of_injective (f := (V.subgroupOf Y).subtype)
        (V.subgroupOf Y).subtype_injective]
    exact hcard
  · intro z hz
    rw [← model3Plumb_center_map hVY] at hz
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hm
    rw [← map_mul, ← map_mul, hsq w hw, map_one, map_one]
  · intro x hx hx2
    have hx' : (⟨x, hx⟩ : ↥Y) * ⟨x, hx⟩ = 1 := Subtype.ext hx2
    obtain ⟨y, hy⟩ := hb ⟨x, hx⟩ hx'
    refine ⟨(y : G), y.2, ?_⟩
    have h2 := Subgroup.mem_map_of_mem Y.subtype hy
    rw [model3Plumb_center_map hVY] at h2
    simpa using h2
  · intro τ hτ hnot
    have hmap : (((center ↥(V.subgroupOf Y)).map (V.subgroupOf Y).subtype) ⊔
        ((center ↥(V.subgroupOf Y)).map (V.subgroupOf Y).subtype).map
          (MulAut.conj (⟨τ, hτ⟩ : ↥Y)⁻¹).toMonoidHom).map Y.subtype =
        (V ⊓ centralizer (V : Set G)) ⊔
          (V ⊓ centralizer (V : Set G)).map (MulAut.conj τ⁻¹).toMonoidHom := by
      rw [Subgroup.map_sup, model3Plumb_conj_map, model3Plumb_center_map hVY]
    have hnot' : ¬ IsPGroup 2 ↥(((center ↥(V.subgroupOf Y)).map (V.subgroupOf Y).subtype) ⊔
        ((center ↥(V.subgroupOf Y)).map (V.subgroupOf Y).subtype).map
          (MulAut.conj (⟨τ, hτ⟩ : ↥Y)⁻¹).toMonoidHom) := by
      intro hP
      apply hnot
      rw [← hmap]
      exact hP.map Y.subtype
    have hW := hc ⟨τ, hτ⟩ hnot'
    have hW' := congrArg (Subgroup.map Y.subtype) hW
    rw [Subgroup.map_sup, model3Plumb_conj_map, hWV, model3Plumb_map_top] at hW'
    exact hW'

end Transport

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
