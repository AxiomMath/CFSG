module

public import CFSG.Quasithin.H13.NQCatLieOverRank2

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup CFSG.QuasithinUnique

theorem map_mul_toMonoidHom {G : Type*} [Group G] (X : Subgroup G) (e f : MulAut G) :
    X.map (e * f).toMonoidHom = (X.map f.toMonoidHom).map e.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem map_pow_eq {G : Type*} [Group G] {X : Subgroup G} {e : MulAut G}
    (h : X.map e.toMonoidHom = X) (m : ℕ) : X.map (e ^ m).toMonoidHom = X := by
  induction m with
  | zero =>
    ext x
    simp
  | succ m ih =>
    rw [pow_succ, map_mul_toMonoidHom, h, ih]

theorem mem_normalizer_of_map_conj {G : Type*} [Group G] {X : Subgroup G} {g : G}
    (h : X.map (MulAut.conj g).toMonoidHom = X) : g ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← h]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← h] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have h1 : g * z * g⁻¹ = g * y * g⁻¹ := hzy
    rwa [← (mul_left_cancel (mul_right_cancel h1) : z = y)]

@[expose] def CartanConcl (Y : Type) [Group Y] (U : Subgroup Y) (L : Prop) : Prop :=
  ∀ α : MulAut Y, (∃ e : ℕ, α ^ 2 ^ e = 1) → U.map α.toMonoidHom = U →
    (∀ x ∈ Subgroup.normalizer (U : Set Y), α x * x⁻¹ ∈ U) →
    (∃ y : Y, α = MulAut.conj y) ∨
      (L ∧ (∃ y : Y, α ^ 2 = MulAut.conj y) ∧
        ∀ P : Subgroup Y, Subgroup.normalizer (U : Set Y) ≤ P → P ⋖ ⊤ →
          P.map α.toMonoidHom ≠ P)

theorem CartanConcl.mono {Y : Type} [Group Y] {U : Subgroup Y} {L L' : Prop}
    (h : CartanConcl Y U L) (hL : L → L') : CartanConcl Y U L' := by
  intro α hα hαU hN
  rcases h α hα hαU hN with h1 | ⟨h1, h2, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨hL h1, h2, h3⟩

theorem congr_conj {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (y : Y) :
    MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := by
  ext z
  simp [MulAut.congr_apply]

theorem CartanConcl.map {Y Y' : Type} [Group Y] [Group Y'] {U : Subgroup Y} {L : Prop}
    (h : CartanConcl Y U L) (e : Y ≃* Y') : CartanConcl Y' (U.map e.toMonoidHom) L := by
  intro α' hα' hU' hN'
  obtain ⟨α, rfl⟩ := (MulAut.congr e).surjective α'
  have hcomm : ∀ y, MulAut.congr e α (e y) = e (α y) := fun y => by
    simp [MulAut.congr_apply]
  have hmap : ∀ X : Subgroup Y, (X.map α.toMonoidHom).map e.toMonoidHom =
      (X.map e.toMonoidHom).map (MulAut.congr e α).toMonoidHom := fun X => by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    exact MonoidHom.ext fun y => (hcomm y).symm
  have hN : normalizer ((U.map e.toMonoidHom : Subgroup Y') : Set Y') =
      (normalizer (U : Set Y)).map e.toMonoidHom := (map_equiv_normalizer_eq U e).symm
  have hα : ∃ n : ℕ, α ^ 2 ^ n = 1 := by
    obtain ⟨n, hn⟩ := hα'
    exact ⟨n, (MulAut.congr e).injective (by rw [map_pow, hn, map_one])⟩
  have hαU : U.map α.toMonoidHom = U :=
    map_injective (f := e.toMonoidHom) e.injective (by rw [hmap, hU'])
  have hαN : ∀ x ∈ normalizer (U : Set Y), α x * x⁻¹ ∈ U := by
    intro x hx
    have h1 := hN' (e x) (by rw [hN]; exact mem_map_of_mem _ hx)
    rw [hcomm, ← map_inv, ← map_mul] at h1
    exact (mem_map_iff_mem e.injective).mp h1
  rcases h α hα hαU hαN with ⟨y, rfl⟩ | ⟨hL, ⟨y, hy⟩, hP⟩
  · exact Or.inl ⟨e y, congr_conj e y⟩
  refine Or.inr ⟨hL, ⟨e y, by rw [← map_pow, hy, congr_conj]⟩, fun P' hNP' hP' hmap' => ?_⟩
  have hPe : (P'.comap e.toMonoidHom).map e.toMonoidHom = P' :=
    map_comap_eq_self_of_surjective e.surjective P'
  have htop : (⊤ : Subgroup Y).map e.toMonoidHom = ⊤ := map_top_of_surjective _ e.surjective
  refine hP (P'.comap e.toMonoidHom) ?_ ?_ (map_injective (f := e.toMonoidHom) e.injective ?_)
  · rw [← map_le_iff_le_comap, ← hN]
    exact hNP'
  · rw [← apply_covBy_apply_iff (MulEquiv.mapSubgroup e)]
    change (P'.comap e.toMonoidHom).map e.toMonoidHom ⋖ (⊤ : Subgroup Y).map e.toMonoidHom
    rw [hPe, htop]
    exact hP'
  · rw [hmap, hPe, hmap']

theorem cartanConcl_of_sylow {Y₀ Y : Type} [Group Y₀] [Group Y] [Finite Y] {L : Prop}
    {U₀ : Subgroup Y₀} (h : CartanConcl Y₀ U₀ L) (hU₀ : IsSylowTwoOf U₀ ⊤) (e : Y₀ ≃* Y)
    {U : Subgroup Y} (hU : IsSylowTwoOf U ⊤) : CartanConcl Y U L := by
  have : Finite Y₀ := Finite.of_equiv _ e.symm.toEquiv
  have hU₁ : IsSylowTwoOf (U₀.map e.toMonoidHom) ⊤ := by
    refine ⟨le_top, hU₀.2.1.map _, ?_⟩
    have h1 := hU₀.2.2
    rw [show (U₀.subgroupOf ⊤).index = U₀.index from relIndex_top_right _] at h1
    rwa [show ((U₀.map e.toMonoidHom).subgroupOf ⊤).index = (U₀.map e.toMonoidHom).index from
      relIndex_top_right _, MulEquiv.toMonoidHom_eq_coe, index_map_equiv]
  obtain ⟨g, rfl⟩ := exists_conj_map_eq hU₁ hU
  exact (h.map e).map (MulAut.conj g)

end CFSG.Quasithin.H13.NQCat
