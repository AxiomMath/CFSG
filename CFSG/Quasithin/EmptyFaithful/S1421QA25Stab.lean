module

public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace QA25

section Stab

variable {Y : Type} [Group Y]

@[expose] def StableMax (S A : Subgroup Y) : Prop :=
  ∃ P : Subgroup Y, IsMaxParabolic2 A P ∧
    A ⊓ Subgroup.normalizer ((S ⊓ A : Subgroup Y) : Set Y) ≤ P ∧
    S ≤ Subgroup.normalizer (P : Set Y)

theorem stableMax_iff {S A : Subgroup Y} :
    StableMax S A ↔ ¬ E2.IsDiagramNontrivial S A (S ⊓ A) := by
  constructor
  · rintro ⟨P, hP, hB, hN⟩ hD
    exact hD P hP hB hN
  · intro h
    by_contra hcon
    exact h fun P hP hB hN => hcon ⟨P, hP, hB, hN⟩

theorem map_map_symm {Y' : Type} [Group Y'] (f : Y ≃* Y') (H : Subgroup Y) :
    (H.map f.toMonoidHom).map f.symm.toMonoidHom = H := by
  rw [Subgroup.map_map]
  have : f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id Y := by
    ext x
    simp
  rw [this, Subgroup.map_id]

theorem mem_normalizer_map_equiv {Y' : Type} [Group Y'] (f : Y ≃* Y') (H : Subgroup Y) (x : Y) :
    f x ∈ Subgroup.normalizer ((H.map f.toMonoidHom : Subgroup Y') : Set Y') ↔
      x ∈ Subgroup.normalizer (H : Set Y) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have := h (f y)
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv] at this
    simpa using this
  · intro h y'
    obtain ⟨y, rfl⟩ := f.surjective y'
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    simpa using h y

theorem isSylowTwoOf_map_equiv {Y' : Type} [Group Y'] (f : Y ≃* Y') {S H : Subgroup Y}
    (h : IsSylowTwoOf S H) : IsSylowTwoOf (S.map f.toMonoidHom) (H.map f.toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map f.toMonoidHom, ?_⟩
  have h1 : ((S.map f.toMonoidHom).subgroupOf (H.map f.toMonoidHom)).index = S.relIndex H :=
    Subgroup.relIndex_map_map_of_injective S H f.injective
  rw [h1]
  exact h.2.2

theorem isParabolic2_map {Y' : Type} [Group Y'] (f : Y ≃* Y') {L P : Subgroup Y}
    (h : IsParabolic2 L P) : IsParabolic2 (L.map f.toMonoidHom) (P.map f.toMonoidHom) := by
  obtain ⟨hPL, S₀, hS₀, hB⟩ := h
  refine ⟨Subgroup.map_mono hPL, S₀.map f.toMonoidHom, isSylowTwoOf_map_equiv f hS₀, ?_⟩
  rintro x' ⟨hx'L, hx'N⟩
  obtain ⟨x, rfl⟩ := f.surjective x'
  have hxL : x ∈ L := by
    have := Subgroup.mem_map_equiv.mp hx'L
    simpa using this
  have hxN : x ∈ Subgroup.normalizer (S₀ : Set Y) := (mem_normalizer_map_equiv f S₀ x).mp hx'N
  exact ⟨x, hB ⟨hxL, hxN⟩, rfl⟩

theorem isMaxParabolic2_map {Y' : Type} [Group Y'] (f : Y ≃* Y') {L P : Subgroup Y}
    (h : IsMaxParabolic2 L P) : IsMaxParabolic2 (L.map f.toMonoidHom) (P.map f.toMonoidHom) := by
  obtain ⟨hpar, hne, hmax⟩ := h
  refine ⟨isParabolic2_map f hpar, fun h' => hne (Subgroup.map_injective f.injective h'), ?_⟩
  intro Q' hQ' hQ'ne hPQ'
  have hQ : IsParabolic2 L (Q'.map f.symm.toMonoidHom) := by
    have := isParabolic2_map f.symm hQ'
    rwa [map_map_symm] at this
  have hQne : Q'.map f.symm.toMonoidHom ≠ L := by
    intro h'
    apply hQ'ne
    have := congrArg (Subgroup.map f.toMonoidHom) h'
    rwa [Subgroup.map_map, show f.toMonoidHom.comp f.symm.toMonoidHom = MonoidHom.id Y' by
      ext x; simp, Subgroup.map_id] at this
  have hPQ : P ≤ Q'.map f.symm.toMonoidHom := by
    have := Subgroup.map_mono (f := f.symm.toMonoidHom) hPQ'
    rwa [map_map_symm] at this
  have h1 := hmax _ hQ hQne hPQ
  have h2 := congrArg (Subgroup.map f.toMonoidHom) h1
  rwa [Subgroup.map_map, show f.toMonoidHom.comp f.symm.toMonoidHom = MonoidHom.id Y' by
    ext x; simp, Subgroup.map_id] at h2

theorem StableMax.map {Y' : Type} [Group Y'] (f : Y ≃* Y') {S A : Subgroup Y}
    (h : StableMax S A) : StableMax (S.map f.toMonoidHom) (A.map f.toMonoidHom) := by
  obtain ⟨P, hP, hB, hN⟩ := h
  refine ⟨P.map f.toMonoidHom, isMaxParabolic2_map f hP, ?_, ?_⟩
  · rintro x' ⟨hx'A, hx'N⟩
    obtain ⟨x, rfl⟩ := f.surjective x'
    have hxA : x ∈ A := by
      have := Subgroup.mem_map_equiv.mp hx'A
      simpa using this
    have hxN : x ∈ Subgroup.normalizer ((S ⊓ A : Subgroup Y) : Set Y) := by
      refine (mem_normalizer_map_equiv f (S ⊓ A) x).mp ?_
      rwa [Subgroup.map_inf_eq _ _ _ f.injective]
    exact ⟨x, hB ⟨hxA, hxN⟩, rfl⟩
  · rintro s' hs'
    obtain ⟨s, hs, rfl⟩ := hs'
    exact (mem_normalizer_map_equiv f P s).mpr (hN hs)

end Stab

end QA25

end CFSG.Quasithin
