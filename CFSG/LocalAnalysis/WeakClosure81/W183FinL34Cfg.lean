module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Fin

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W183L34

open CFSG.Open

@[expose] def CfgData {G : Type*} [Group G] (A₀ P : Subgroup G) (gA gS y : G) : Prop :=
  A₀ ≤ P ∧ A₀.map (MulAut.conj gA).toMonoidHom ≤ P ∧ A₀.map (MulAut.conj gS).toMonoidHom ≤ P ∧
    y ∈ P ∧ A₀.map (MulAut.conj y).toMonoidHom ≠ A₀ ∧
    (∀ s ∈ A₀, ∃ z ∈ A₀.map (MulAut.conj gS).toMonoidHom, y * s * y⁻¹ = s * z) ∧
    ¬ A₀ ≤ Subgroup.normalizer ((A₀.map (MulAut.conj gA).toMonoidHom : Subgroup G) : Set G) ∧
    (A₀.map (MulAut.conj gS).toMonoidHom = A₀.map (MulAut.conj gA).toMonoidHom ∨
      ∀ a ∈ A₀.map (MulAut.conj gA).toMonoidHom, ∀ x ∈ A₀.map (MulAut.conj gS).toMonoidHom,
        a * x = x * a)

theorem corConfigIn_of_cfgData {G : Type*} [Group G] {A₀ P : Subgroup G} {gA gS y : G}
    (h : CfgData A₀ P gA gS y) : CorConfigIn G A₀ P := by
  unfold CfgData at h
  obtain ⟨hA, hA', hS', hyP, hyne, hcomm, hnorm, hdisj⟩ := h
  have hgen : (A₀.map (MulAut.conj gS).toMonoidHom : Set G) ⊆
      Subgroup.closure (⋃ X ∈ ({A₀.map (MulAut.conj gS).toMonoidHom} : Set (Subgroup G)),
        (X : Set G)) := by
    refine (Set.subset_biUnion_of_mem (u := fun X : Subgroup G => (X : Set G)) ?_).trans
      Subgroup.subset_closure
    exact Set.mem_singleton _
  refine ⟨A₀.map (MulAut.conj gA).toMonoidHom,
    ({A₀.map (MulAut.conj gS).toMonoidHom} : Set (Subgroup G)), y,
    ⟨gA, rfl⟩, ?_, hyne, ?_, hnorm, ?_, hA', ?_, hyP⟩
  · intro X hX
    rw [Set.mem_singleton_iff] at hX
    subst X
    exact ⟨gS, rfl⟩
  · intro s hs
    obtain ⟨z, hz, hz'⟩ := hcomm s hs
    exact ⟨z, hgen hz, hz'⟩
  · intro X hX
    rw [Set.mem_singleton_iff] at hX
    subst X
    exact hdisj
  · intro X hX
    rw [Set.mem_singleton_iff] at hX
    subst X
    exact hS'

theorem cfgData_of_map {G₀ G : Type*} [Group G₀] [Group G] (ι : G₀ →* G)
    (hι : Function.Injective ι) (A₀ : Subgroup G₀) (P : Subgroup G) (gA gS y : G)
    (hP : P ≤ ι.range) (hgA : gA ∈ ι.range) (hgS : gS ∈ ι.range) (hy : y ∈ ι.range)
    (h : CfgData (A₀.map ι) P gA gS y) :
    ∃ (P₀ : Subgroup G₀) (gA₀ gS₀ y₀ : G₀), P₀.map ι = P ∧ CfgData A₀ P₀ gA₀ gS₀ y₀ := by
  unfold CfgData at h
  obtain ⟨hA, hA', hS', hyP, hyne, hcomm, hnorm, hdisj⟩ := h
  obtain ⟨gA₀, hgA₀⟩ := hgA
  obtain ⟨gS₀, hgS₀⟩ := hgS
  obtain ⟨y₀, hy₀⟩ := hy
  have hEqA : (A₀.map (MulAut.conj gA₀).toMonoidHom).map ι =
      (A₀.map ι).map (MulAut.conj gA).toMonoidHom := by
    rw [Subgroup.map_map_conj A₀ ι gA₀, hgA₀]
  have hEqS : (A₀.map (MulAut.conj gS₀).toMonoidHom).map ι =
      (A₀.map ι).map (MulAut.conj gS).toMonoidHom := by
    rw [Subgroup.map_map_conj A₀ ι gS₀, hgS₀]
  have hEqY : (A₀.map (MulAut.conj y₀).toMonoidHom).map ι =
      (A₀.map ι).map (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.map_map_conj A₀ ι y₀, hy₀]
  refine ⟨P.comap ι, gA₀, gS₀, y₀, Subgroup.map_comap_eq_self hP, ?_⟩
  unfold CfgData
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.map_le_iff_le_comap (f := ι)).mp hA
  · exact (Subgroup.map_le_iff_le_comap (f := ι)).mp (by rw [hEqA]; exact hA')
  · exact (Subgroup.map_le_iff_le_comap (f := ι)).mp (by rw [hEqS]; exact hS')
  · rw [Subgroup.mem_comap]
    rw [hy₀]
    exact hyP
  · intro heq
    have hthis : (A₀.map ι).map (MulAut.conj y).toMonoidHom = A₀.map ι := by
      have hmap := congrArg (Subgroup.map ι) heq
      rw [hEqY] at hmap
      exact hmap
    exact hyne hthis
  · intro s hs
    have hs' : ι s ∈ A₀.map ι := Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
    obtain ⟨z', hz', hz'eq⟩ := hcomm (ι s) hs'
    rw [← hEqS] at hz'
    obtain ⟨z, hz, hz_eq⟩ := Subgroup.mem_map.mp hz'
    refine ⟨z, hz, ?_⟩
    apply hι
    simp only [map_mul, map_inv, hy₀, hz_eq]
    exact hz'eq
  · intro hle
    apply hnorm
    have hmap : A₀.map ι ≤
        (Subgroup.normalizer (A₀.map (MulAut.conj gA₀).toMonoidHom : Set G₀)).map ι :=
      Subgroup.map_mono hle
    have hle' := hmap.trans (Subgroup.le_normalizer_map ι)
    rw [hEqA] at hle'
    exact hle'
  · rcases hdisj with heq | hcommG
    · left
      apply Subgroup.map_injective hι
      rw [hEqS, hEqA]
      exact heq
    · right
      intro a ha x hx
      apply hι
      have hia : ι a ∈ (A₀.map ι).map (MulAut.conj gA).toMonoidHom := by
        rw [← hEqA]
        exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
      have hix : ι x ∈ (A₀.map ι).map (MulAut.conj gS).toMonoidHom := by
        rw [← hEqS]
        exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      have hthis := hcommG (ι a) hia (ι x) hix
      simpa using hthis

theorem isElemAbelian_map {G H : Type*} [Group G] [Group H] (f : G →* H) {A : Subgroup G}
    (h : IsElemAbelian 2 A) : IsElemAbelian 2 (A.map f) := by
  exact IsElemAbelian.map h f

theorem tiS_map {G₀ G : Type*} [Group G₀] [Group G] (ι : G₀ →* G) (hι : Function.Injective ι)
    {A₀ : Subgroup G₀} (h : IsTISub G₀ A₀) :
    ∀ t ∈ A₀.map ι, t ≠ 1 → ∀ g ∈ ι.range, g * t = t * g →
      g ∈ Subgroup.normalizer ((A₀.map ι : Subgroup G) : Set G) := by
  rintro t ⟨t₀, ht₀, rfl⟩ ht1 g ⟨g₀, rfl⟩ hgt
  have ht1' : t₀ ≠ 1 := fun h1 => ht1 (by rw [h1, map_one])
  have hcomm : g₀ * t₀ = t₀ * g₀ := hι (by rw [map_mul, map_mul]; exact hgt)
  have hg₀ : g₀ ∈ Subgroup.normalizer (A₀ : Set G₀) := h t₀ ht₀ ht1' g₀ hcomm
  exact Subgroup.le_normalizer_map ι (Subgroup.mem_map.mpr ⟨g₀, hg₀, rfl⟩)

end CFSG.LocalAnalysis.WeakClosure81.W183L34

end
