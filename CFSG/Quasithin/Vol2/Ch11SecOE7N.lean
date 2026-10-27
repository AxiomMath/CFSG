module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual
public import CFSG.Quasithin.Background.E2Two
public import CFSG.Quasithin.Background.A1bGroups

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X6

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjSub_map_subtype {L : Subgroup G} [hL : L.Normal] (t : G) (M : Subgroup ↥L) :
    A1b.conjSub t (M.map L.subtype) =
      (M.map (MulAut.conjNormal t : MulAut ↥L).toMonoidHom).map L.subtype := by
  ext x
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨MulAut.conjNormal t m, ⟨m, hm, rfl⟩, ?_⟩
    simp [MulAut.conjNormal_apply]
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨m, ⟨m, hm, rfl⟩, ?_⟩
    simp [MulAut.conjNormal_apply]

theorem le_normalizer_parabolic_of_not_isDiagramNontrivial {L T : Subgroup G} [hLn : L.Normal]
    (hT : IsSylowIn 2 T ⊤) {P : Fin 2 → Subgroup ↥L}
    (hres : ResidualOvergroupsAt ↥L ((T ⊓ L).subgroupOf L) P)
    (hnorm : ∀ j, Subgroup.normalizer
      (((T ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) ≤ P j)
    (hun : ¬ E2.IsDiagramNontrivial T L (T ⊓ L)) (j : Fin 2) :
    T ≤ Subgroup.normalizer (((P j).map L.subtype : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hne, hUP, hmax, -, -, -⟩ := hres
  set U := (T ⊓ L).subgroupOf L with hUdef
  have hTL : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal (⟨hT.1, hT.2.1, hT.2.2⟩ : QuasithinUnique.IsSylowTwoOf T ⊤) le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hLn])
  have hpar : ∀ k, IsParabolic2 L ((P k).map L.subtype) := by
    intro k
    refine ⟨Subgroup.map_subtype_le _, T ⊓ L, hTL, fun x hx => ?_⟩
    obtain ⟨hxL, hxN⟩ := Subgroup.mem_inf.mp hx
    refine ⟨⟨x, hxL⟩, hnorm k ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hUdef, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hxN y
  have hPne : ∀ k, (P k).map L.subtype ≠ L := by
    intro k h
    have hc := ((hmax (P k) (hUP k)).mpr ⟨k, rfl⟩).isCoatom
    apply hc.1
    rw [eq_top_iff]
    intro x _
    have : (x : G) ∈ (P k).map L.subtype := by rw [h]; exact x.2
    obtain ⟨y, hy, hyx⟩ := this
    rwa [show y = x from Subtype.ext hyx] at hy
  have hun' : ∃ P' : Subgroup G, IsMaxParabolic2 L P' ∧
      L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ≤ P' ∧
      T ≤ Subgroup.normalizer (P' : Set G) := by
    by_contra hc
    push Not at hc
    exact hun fun P' h1 h2 => hc P' h1 h2
  obtain ⟨P', ⟨⟨hP'L, -⟩, hP'ne, hP'max⟩, hBP', hTP'⟩ := hun'
  have hUP' : U ≤ P'.subgroupOf L := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine hBP' ⟨x.2, ?_⟩
    rw [hUdef, Subgroup.mem_subgroupOf] at hx
    exact Subgroup.le_normalizer hx
  have hP'top : P'.subgroupOf L ≠ ⊤ := by
    intro h
    apply hP'ne
    refine le_antisymm hP'L fun x hx => ?_
    have : (⟨x, hx⟩ : ↥L) ∈ P'.subgroupOf L := h ▸ Subgroup.mem_top _
    exact this
  obtain ⟨M, hMc, hP'M⟩ := (eq_top_or_exists_le_coatom (P'.subgroupOf L)).resolve_left hP'top
  obtain ⟨i, rfl⟩ := (hmax M (hUP'.trans hP'M)).mp hMc.covBy_top
  have hP'i : (P i).map L.subtype = P' := by
    refine hP'max _ (hpar i) (hPne i) fun x hx => ?_
    exact ⟨⟨x, hP'L hx⟩, hP'M hx, rfl⟩
  intro t ht
  rw [← A1b.conjSub_eq_iff_mem_normalizer, conjSub_map_subtype]
  set φ : MulAut ↥L := MulAut.conjNormal t with hφ
  have hinj : Function.Injective (Subgroup.map (L.subtype)) :=
    Subgroup.map_injective L.subtype_injective
  have hφU : U.map φ.toMonoidHom = U := by
    refine (Subgroup.eq_of_le_of_card_ge ?_ ?_)
    · rintro _ ⟨u, hu, rfl⟩
      have hu' : (u : G) ∈ T ⊓ L := Subgroup.mem_subgroupOf.mp hu
      rw [hUdef, Subgroup.mem_subgroupOf]
      show ((φ u : ↥L) : G) ∈ T ⊓ L
      rw [hφ, MulAut.conjNormal_apply]
      exact ⟨T.mul_mem (T.mul_mem ht hu'.1) (T.inv_mem ht), hLn.conj_mem _ hu'.2 t⟩
    · exact (Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective).ge
  have hcoat : ∀ k, ∃ k', (P k).map φ.toMonoidHom = P k' := by
    intro k
    have hc : (P k).map φ.toMonoidHom ⋖ ⊤ := by
      have h1 := (hmax (P k) (hUP k)).mpr ⟨k, rfl⟩
      have h2 := (apply_covBy_apply_iff (MulEquiv.mapSubgroup φ)).mpr h1
      simpa [MulEquiv.mapSubgroup_apply, Subgroup.map_top_of_surjective _ φ.surjective] using h2
    refine (hmax _ ?_).mp hc
    rw [← hφU]
    exact Subgroup.map_mono (hUP k)
  have hφi : (P i).map φ.toMonoidHom = P i := by
    apply hinj
    rw [← conjSub_map_subtype, hP'i]
    exact A1b.conjSub_eq_iff_mem_normalizer.mpr (hTP' ht)
  suffices h : (P j).map φ.toMonoidHom = P j by rw [h]
  by_cases hji : j = i
  · rw [hji, hφi]
  · obtain ⟨k', hk'⟩ := hcoat j
    by_cases hk'i : k' = i
    · exfalso
      rw [hk'i, ← hφi] at hk'
      have hPji : P j = P i := Subgroup.map_injective φ.injective hk'
      apply hne
      fin_cases i <;> fin_cases j <;> simp_all
    · have hk'j : k' = j := by
        fin_cases i <;> fin_cases j <;> fin_cases k' <;> simp_all
      rw [hk', hk'j]

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
