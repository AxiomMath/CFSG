module

public import CFSG.Quasithin.EmptyFaithful.R3c11L3b

public section

namespace CFSG.Quasithin.R3c12

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {X X' : Type} [Group X] [Group X']

@[expose] def ClConfig (X : Type) [Group X] : Prop :=
  ∃ (T V : Subgroup X) (e : X), IsSylowTwoOf T ⊤ ∧ V ≤ T ∧ Nat.card V = 4 ∧
    (∀ v ∈ V, v * v = 1) ∧ T ≤ Subgroup.normalizer (V : Set X) ∧ e ≠ 1 ∧ e ^ 3 = 1 ∧
    ∀ v ∈ V, e * v = v * e

theorem ClConfig.map (φ : X ≃* X') (h : ClConfig X) : ClConfig X' := by
  obtain ⟨T, V, e, hT, hVT, hV4, hV2, hTN, he1, he3, hec⟩ := h
  have hT' : IsSylowTwoOf (T.map φ.toMonoidHom) ⊤ := by
    obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT
    refine K1.isSylowTwoOf_top_iff.mpr ⟨hp.map φ.toMonoidHom, ?_⟩
    rw [Subgroup.index_map_of_bijective (f := φ.toMonoidHom) φ.bijective]
    exact hi
  refine ⟨T.map φ.toMonoidHom, V.map φ.toMonoidHom, φ e, hT', Subgroup.map_mono hVT, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [← hV4]
    exact (Nat.card_congr (V.equivMapOfInjective φ.toMonoidHom φ.injective).toEquiv).symm
  · rintro _ ⟨v, hv, rfl⟩
    show φ v * φ v = 1
    rw [← map_mul, hV2 v hv, map_one]
  · intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    exact (R3c11.mem_normalizer_map_equiv_iff φ V t₀).mpr (hTN ht₀)
  · intro h1
    exact he1 (φ.injective (by rw [h1, map_one]))
  · rw [← map_pow, he3, map_one]
  · rintro _ ⟨v, hv, rfl⟩
    show φ e * φ v = φ v * φ e
    rw [← map_mul, ← map_mul, hec v hv]

end CFSG.Quasithin.R3c12
