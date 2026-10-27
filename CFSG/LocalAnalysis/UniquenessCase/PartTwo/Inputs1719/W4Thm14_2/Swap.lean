module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup

variable {G H : Type} [Group G] [Group H]

theorem swapsParabolics_map_of_le {Y T X : Subgroup G}
    (f : ↥Y →* H) (hf : Function.Injective f) (hT : T ≤ Y) (hX : X ≤ Y)
    (h : S17.SwapsParabolics T X) :
    S17.SwapsParabolics ((T.subgroupOf Y).map f) ((X.subgroupOf Y).map f) := by
  classical
  obtain ⟨t, htT, P, hP, hmove⟩ := h
  have hPX : P ≤ X := hP.1
  have hPY : P ≤ Y := hPX.trans hX
  let tY : ↥Y := ⟨t, hT htT⟩
  let P' : Subgroup H := (P.subgroupOf Y).map f
  have hmem : f tY ∈ (T.subgroupOf Y).map f :=
    Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.mpr htT)
  refine ⟨f tY, hmem, P', ?_, ?_⟩
  · have hS : (T.subgroupOf Y).map f ⊓ (X.subgroupOf Y).map f =
        ((T ⊓ X).subgroupOf Y).map f := by
      rw [← Subgroup.map_inf (T.subgroupOf Y) (X.subgroupOf Y) f hf]
      rfl
    refine ⟨Subgroup.map_mono (Subgroup.subgroupOf_mono Y hPX), ?_, ?_, ?_⟩
    · rw [hS]
      intro z hz
      rw [Subgroup.mem_inf] at hz
      obtain ⟨hzX, hzN⟩ := hz
      obtain ⟨x, hxX, rfl⟩ := Subgroup.mem_map.mp hzX
      have hxN : x ∈ Subgroup.normalizer ((T ⊓ X).subgroupOf Y : Set ↥Y) := by
        have h1 : x ∈ (Subgroup.normalizer (((T ⊓ X).subgroupOf Y).map f)).comap f :=
          Subgroup.mem_comap.mpr hzN
        rwa [Subgroup.comap_normalizer_eq_of_le_range (Subgroup.map_le_range f _),
          Subgroup.comap_map_eq_self_of_injective hf] at h1
      have hxXG : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hxX
      have hxNG : (x : G) ∈ Subgroup.normalizer (T ⊓ X : Set G) := by
        have h2 : x ∈ (Subgroup.normalizer ((T ⊓ X : Subgroup G) : Set G)).subgroupOf Y := by
          rw [Subgroup.subgroupOf_normalizer_eq (H := T ⊓ X) (N := Y)
            ((inf_le_left : T ⊓ X ≤ T).trans hT)]
          exact hxN
        exact Subgroup.mem_subgroupOf.mp h2
      exact Subgroup.mem_map.mpr
        ⟨x, Subgroup.mem_subgroupOf.mpr (hP.2.1 ⟨hxXG, hxNG⟩), rfl⟩
    · intro hEq
      apply hP.2.2.1
      have hsub : P.subgroupOf Y = X.subgroupOf Y := Subgroup.map_injective hf hEq
      have h := congrArg (Subgroup.map Y.subtype) hsub
      rwa [Subgroup.map_subgroupOf_eq_of_le hPY,
        Subgroup.map_subgroupOf_eq_of_le hX] at h
    · intro Q' hPQ' hQ'X
      have hQ'range : Q' ≤ f.range :=
        hQ'X.trans (Subgroup.map_le_range f (X.subgroupOf Y))
      let Q : Subgroup G := (Q'.comap f).map Y.subtype
      have hQsub : Q.subgroupOf Y = Q'.comap f := by
        apply Subgroup.map_injective Y.subtype_injective
        rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le (K := Q'.comap f))]
      have hQ'eq : Q' = (Q.subgroupOf Y).map f := by
        calc Q' = (Q'.comap f).map f := (Subgroup.map_comap_eq_self hQ'range).symm
          _ = (Q.subgroupOf Y).map f := by rw [hQsub]
      have hPQ : P ≤ Q := by
        have h2 : P.subgroupOf Y ≤ Q.subgroupOf Y := by
          rw [hQsub]
          intro p hp
          exact hPQ' (Subgroup.mem_map_of_mem f hp)
        have h3 := Subgroup.map_mono h2 (f := Y.subtype)
        rwa [Subgroup.map_subgroupOf_eq_of_le hPY,
          Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le (K := Q'.comap f))] at h3
      have hQX : Q ≤ X := by
        have h2 : Q'.comap f ≤ X.subgroupOf Y := fun y hy =>
          (Subgroup.mem_map_iff_mem hf).mp (hQ'X hy)
        have h3 := Subgroup.map_mono h2 (f := Y.subtype)
        calc Q = (Q'.comap f).map Y.subtype := rfl
          _ ≤ (X.subgroupOf Y).map Y.subtype := h3
          _ = X := Subgroup.map_subgroupOf_eq_of_le hX
      rcases hP.2.2.2 Q hPQ hQX with hQP | hQX
      · left
        rw [hQ'eq, hQP]
      · right
        rw [hQ'eq, hQX]
  · intro hfix
    have h1 : ((P.subgroupOf Y).map (MulAut.conj tY).toMonoidHom).map f =
        (P.subgroupOf Y).map f := by
      rw [Subgroup.map_map_conj]
      exact hfix
    have h2 : (P.subgroupOf Y).map (MulAut.conj tY).toMonoidHom = P.subgroupOf Y :=
      Subgroup.map_injective hf h1
    have h3 : ((P.subgroupOf Y).map (MulAut.conj tY).toMonoidHom).map Y.subtype =
        P.map (MulAut.conj t).toMonoidHom := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨p, hp, hpy⟩ := Subgroup.mem_map.mp hy
        refine Subgroup.mem_map.mpr ⟨(p : G), Subgroup.mem_subgroupOf.mp hp, ?_⟩
        rw [← hpy]
        simp [MulAut.conj_apply, tY]
      · rintro ⟨p, hp, rfl⟩
        refine Subgroup.mem_map.mpr ⟨(MulAut.conj tY) ⟨p, hPY hp⟩, ?_, ?_⟩
        · exact Subgroup.mem_map.mpr
            ⟨⟨p, hPY hp⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
        · simp [MulAut.conj_apply, tY]
    have hPmap : P.map (MulAut.conj t).toMonoidHom = P := by
      rw [← h3, h2, Subgroup.map_subgroupOf_eq_of_le hPY]
    exact hmove hPmap

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
