module

public import CFSG.Quasithin.EmptyFaithful.R3c11L3b

public section

namespace CFSG.Quasithin.R3c14

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {X X' : Type} [Group X] [Group X']

structure ElData (T V H : Subgroup X) (ζ : MulAut X) : Prop where
  VT : V ≤ T
  V4 : Nat.card V = 4
  V2 : ∀ v ∈ V, v * v = 1
  TV : T ≤ Subgroup.normalizer (V : Set X)
  VH : V ≤ H
  HV : H ≤ Subgroup.normalizer (V : Set X)
  TH : T ≤ Subgroup.normalizer (H : Set X)
  y3 : ∃ y ∈ H, y ^ 3 = 1 ∧ ¬ ∀ v ∈ V, y * v = v * y
  fix : ∀ v ∈ V, (∀ h ∈ H, h * v = v * h) → v = 1
  ne : ζ ≠ 1
  fixT : ∀ t ∈ T, ζ t = t
  fixH : ∀ h ∈ H, ζ h = h

@[expose] def ElConfig (X : Type) [Group X] : Prop :=
  ∃ (T V H : Subgroup X) (ζ : MulAut X), IsSylowTwoOf T ⊤ ∧ ElData T V H ζ

theorem ElData.map {T V H : Subgroup X} {ζ : MulAut X} (φ : X ≃* X') (h : ElData T V H ζ) :
    ElData (T.map φ.toMonoidHom) (V.map φ.toMonoidHom) (H.map φ.toMonoidHom)
      (MulAut.congr φ ζ) where
  VT := Subgroup.map_mono h.VT
  V4 := by
    rw [← h.V4]
    exact (Nat.card_congr (V.equivMapOfInjective φ.toMonoidHom φ.injective).toEquiv).symm
  V2 := by
    rintro _ ⟨v, hv, rfl⟩
    show φ v * φ v = 1
    rw [← map_mul, h.V2 v hv, map_one]
  TV := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    exact (R3c11.mem_normalizer_map_equiv_iff φ V t₀).mpr (h.TV ht₀)
  VH := Subgroup.map_mono h.VH
  HV := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    exact (R3c11.mem_normalizer_map_equiv_iff φ V t₀).mpr (h.HV ht₀)
  TH := by
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    exact (R3c11.mem_normalizer_map_equiv_iff φ H t₀).mpr (h.TH ht₀)
  y3 := by
    obtain ⟨y, hyH, hy3, hyn⟩ := h.y3
    refine ⟨φ y, ⟨y, hyH, rfl⟩, by rw [← map_pow, hy3, map_one], fun hall => hyn fun v hv => ?_⟩
    have := hall (φ v) ⟨v, hv, rfl⟩
    exact φ.injective (by rw [map_mul, map_mul]; exact this)
  fix := by
    rintro _ ⟨v, hv, rfl⟩ hc
    have : v = 1 := h.fix v hv fun k hk =>
      φ.injective (by rw [map_mul, map_mul]; exact hc (φ k) ⟨k, hk, rfl⟩)
    rw [this, map_one]
  ne := by
    intro h1
    apply h.ne
    ext x
    have h2 := DFunLike.congr_fun h1 (φ x)
    simpa [MulAut.congr_apply] using h2
  fixT := by
    rintro _ ⟨t, ht, rfl⟩
    simp [MulAut.congr_apply, h.fixT t ht]
  fixH := by
    rintro _ ⟨k, hk, rfl⟩
    simp [MulAut.congr_apply, h.fixH k hk]

theorem ElConfig.map (φ : X ≃* X') (h : ElConfig X) : ElConfig X' := by
  obtain ⟨T, V, H, ζ, hT, hd⟩ := h
  have hT' : IsSylowTwoOf (T.map φ.toMonoidHom) ⊤ := by
    obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT
    refine K1.isSylowTwoOf_top_iff.mpr ⟨hp.map φ.toMonoidHom, ?_⟩
    rw [Subgroup.index_map_of_bijective (f := φ.toMonoidHom) φ.bijective]
    exact hi
  exact ⟨_, _, _, _, hT', hd.map φ⟩

theorem ElConfig.of_sylow [Finite X] {T₀ : Subgroup X} (hT₀ : IsSylowTwoOf T₀ ⊤) (h : ElConfig X) :
    ∃ (V H : Subgroup X) (ζ : MulAut X), ElData T₀ V H ζ := by
  obtain ⟨T, V, H, ζ, hT, hd⟩ := h
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top hT hT₀
  subst hg
  exact ⟨_, _, _, hd.map (MulAut.conj g)⟩

end CFSG.Quasithin.R3c14
