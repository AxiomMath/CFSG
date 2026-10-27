module

public import CFSG.Quasithin.Background.D2Basic
import CFSG.Quasithin.Background.StabSubBasics
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

section Lattice

variable {α : Type*} [CompleteLattice α] [IsModularLattice α]

theorem sSupIndep_biUnion_of_le {𝒲 : Set α} (h𝒲 : sSupIndep 𝒲) {𝒴 : α → Set α}
    (hle : ∀ Z ∈ 𝒲, ∀ Y ∈ 𝒴 Z, Y ≤ Z) (hind : ∀ Z ∈ 𝒲, sSupIndep (𝒴 Z)) :
    sSupIndep (⋃ Z ∈ 𝒲, 𝒴 Z) := by
  intro Y hY
  obtain ⟨Z₀, hZ₀, hY₀⟩ : ∃ Z₀ ∈ 𝒲, Y ∈ 𝒴 Z₀ := by simpa using hY
  have hA : sSup (𝒴 Z₀ \ {Y}) ≤ Z₀ := sSup_le fun Y' hY' => hle Z₀ hZ₀ Y' hY'.1
  have hsub : sSup ((⋃ Z ∈ 𝒲, 𝒴 Z) \ {Y}) ≤ sSup (𝒴 Z₀ \ {Y}) ⊔ sSup (𝒲 \ {Z₀}) := by
    refine sSup_le fun Y' hY' => ?_
    obtain ⟨hY'U, hY'ne⟩ := hY'
    obtain ⟨Z₁, hZ₁, hY₁⟩ : ∃ Z₁ ∈ 𝒲, Y' ∈ 𝒴 Z₁ := by simpa using hY'U
    by_cases h : Z₁ = Z₀
    · subst h
      exact le_sup_of_le_left (le_sSup ⟨hY₁, hY'ne⟩)
    · exact le_sup_of_le_right ((hle Z₁ hZ₁ Y' hY₁).trans (le_sSup ⟨hZ₁, h⟩))
  have h1 : Disjoint Y (sSup (𝒴 Z₀ \ {Y})) := hind Z₀ hZ₀ hY₀
  have h2 : Disjoint (Y ⊔ sSup (𝒴 Z₀ \ {Y})) (sSup (𝒲 \ {Z₀})) :=
    (h𝒲 hZ₀).mono_left (sup_le (hle Z₀ hZ₀ Y hY₀) hA)
  exact (h1.disjoint_sup_right_of_disjoint_sup_left h2).mono_right hsub

end Lattice

section Orbit

variable {V : Type*} [CommGroup V]

theorem sSupIndep_image_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {𝒞 : Set (Subgroup G)} (h : sSupIndep 𝒞) :
    sSupIndep ((Subgroup.map f) '' 𝒞) := by
  rintro _ ⟨a, ha, rfl⟩
  have hinj : Function.Injective (Subgroup.map f) := Subgroup.map_injective hf
  have hset : (Subgroup.map f) '' 𝒞 \ {Subgroup.map f a} = (Subgroup.map f) '' (𝒞 \ {a}) := by
    rw [Set.image_diff hinj, Set.image_singleton]
  rw [hset, sSup_image, ← (Subgroup.gc_map_comap f).l_sSup]
  exact Subgroup.disjoint_map hf (h ha)

private theorem map_subtype_map_resHom (W : Subgroup V) (C : Subgroup ↥W) (s : stabSub W) :
    (C.map (resHom W s).toMonoidHom).map W.subtype =
      (C.map W.subtype).map (s : MulAut V).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem orbit_fibre (H : Subgroup (MulAut V)) (W : Subgroup V) (C : Subgroup ↥W)
    {e₀ : MulAut V} (he₀ : e₀ ∈ H) :
    {Y : Subgroup V | ∃ e ∈ H, W.map e₀.toMonoidHom = W.map e.toMonoidHom ∧
        Y = (C.map W.subtype).map e.toMonoidHom} =
      (Subgroup.map (e₀.toMonoidHom.comp W.subtype)) ''
        {Y : Subgroup ↥W | ∃ n ∈ autSub H W, Y = C.map n.toMonoidHom} := by
  have key : ∀ s : stabSub W, ∀ e : MulAut V, e = e₀ * (s : MulAut V) →
      Subgroup.map (e₀.toMonoidHom.comp W.subtype) (C.map (resHom W s).toMonoidHom) =
        (C.map W.subtype).map e.toMonoidHom := by
    intro s e hes
    rw [← Subgroup.map_map, map_subtype_map_resHom, Subgroup.map_map, hes]
    rfl
  ext Y
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨e, he, hWe, rfl⟩
    have hs : e₀⁻¹ * e ∈ stabSub W := by
      intro u
      have h1 : ∀ x, e₀.symm x ∈ W ↔ e.symm x ∈ W := fun x => by
        rw [← Subgroup.mem_map_equiv, ← Subgroup.mem_map_equiv, hWe]
      show e₀.symm (e u) ∈ W ↔ u ∈ W
      rw [h1 (e u)]
      simp
    refine ⟨C.map (resHom W ⟨e₀⁻¹ * e, hs⟩).toMonoidHom,
      ⟨resHom W ⟨e₀⁻¹ * e, hs⟩, mem_autSub.2 ⟨⟨e₀⁻¹ * e, hs⟩, H.mul_mem (H.inv_mem he₀) he, rfl⟩,
        rfl⟩, ?_⟩
    exact key ⟨e₀⁻¹ * e, hs⟩ e (by simp)
  · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    obtain ⟨s, hsH, rfl⟩ := mem_autSub.1 hn
    refine ⟨e₀ * (s : MulAut V), H.mul_mem he₀ hsH, ?_, key s _ rfl⟩
    have h1 : (e₀ * (s : MulAut V)).toMonoidHom =
        e₀.toMonoidHom.comp (s : MulAut V).toMonoidHom := rfl
    rw [h1, ← Subgroup.map_map, StabLat.mem_stabSub_iff_map.1 s.2]

theorem sSupIndep_orbit_of_autSub (H : Subgroup (MulAut V)) (W : Subgroup V) (C : Subgroup ↥W)
    (hW : sSupIndep {Z : Subgroup V | ∃ e ∈ H, Z = W.map e.toMonoidHom})
    (hC : sSupIndep {Y : Subgroup ↥W | ∃ n ∈ autSub H W, Y = C.map n.toMonoidHom}) :
    sSupIndep {Y : Subgroup V | ∃ e ∈ H, Y = (C.map W.subtype).map e.toMonoidHom} := by
  let 𝒴 : Subgroup V → Set (Subgroup V) := fun Z =>
    {Y | ∃ e ∈ H, Z = W.map e.toMonoidHom ∧ Y = (C.map W.subtype).map e.toMonoidHom}
  have hunion : (⋃ Z ∈ {Z : Subgroup V | ∃ e ∈ H, Z = W.map e.toMonoidHom}, 𝒴 Z) =
      {Y : Subgroup V | ∃ e ∈ H, Y = (C.map W.subtype).map e.toMonoidHom} := by
    ext Y
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, 𝒴]
    constructor
    · rintro ⟨Z, -, e, he, -, hY⟩
      exact ⟨e, he, hY⟩
    · rintro ⟨e, he, hY⟩
      exact ⟨W.map e.toMonoidHom, ⟨e, he, rfl⟩, e, he, rfl, hY⟩
  rw [← hunion]
  refine sSupIndep_biUnion_of_le hW (fun Z _ Y hY => ?_) (fun Z hZ => ?_)
  · obtain ⟨e, he, rfl, rfl⟩ := hY
    exact Subgroup.map_mono (Subgroup.map_subtype_le C)
  · obtain ⟨e₀, he₀, rfl⟩ := hZ
    have hfib : 𝒴 (W.map e₀.toMonoidHom) =
        (Subgroup.map (e₀.toMonoidHom.comp W.subtype)) ''
          {Y : Subgroup ↥W | ∃ n ∈ autSub H W, Y = C.map n.toMonoidHom} := by
      rw [← orbit_fibre H W C he₀]
    rw [hfib]
    exact sSupIndep_image_map _ (e₀.injective.comp W.subtype_injective) hC

theorem sSup_orbit_of_autSub (H : Subgroup (MulAut V)) (W : Subgroup V) (C : Subgroup ↥W)
    (hW : sSup {Z : Subgroup V | ∃ e ∈ H, Z = W.map e.toMonoidHom} = ⊤)
    (hC : sSup {Y : Subgroup ↥W | ∃ n ∈ autSub H W, Y = C.map n.toMonoidHom} = ⊤) :
    sSup {Y : Subgroup V | ∃ e ∈ H, Y = (C.map W.subtype).map e.toMonoidHom} = ⊤ := by
  refine top_le_iff.1 ?_
  rw [← hW]
  refine sSup_le fun Z hZ => ?_
  obtain ⟨e₀, he₀, rfl⟩ := hZ
  have hgen : sSup ((Subgroup.map (e₀.toMonoidHom.comp W.subtype)) ''
      {Y : Subgroup ↥W | ∃ n ∈ autSub H W, Y = C.map n.toMonoidHom}) = W.map e₀.toMonoidHom := by
    rw [sSup_image, ← (Subgroup.gc_map_comap _).l_sSup, hC, ← Subgroup.map_map]
    congr 1
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← hgen, ← orbit_fibre H W C he₀]
  refine sSup_le_sSup ?_
  rintro Y ⟨e, he, -, hY⟩
  exact ⟨e, he, hY⟩

end Orbit

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
