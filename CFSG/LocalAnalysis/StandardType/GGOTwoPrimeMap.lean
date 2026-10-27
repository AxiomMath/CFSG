module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentralizerBasic

public section

namespace CFSG.StandardType

theorem ggOTwoPrime_map_of_injective {H G : Type} [Group H] [Group G] (φ : H →* G)
    (hφ : Function.Injective φ) (Y : Subgroup H) :
    (ggOTwoPrime Y).map φ = ggOTwoPrime (Y.map φ) := by
  rw [ggOTwoPrime, ggOTwoPrime, MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨y, ⟨hyY, k, hk⟩, rfl⟩
    exact ⟨⟨y, hyY, rfl⟩, k, by rw [← map_pow, hk, map_one]⟩
  · rintro ⟨hyY, k, hk⟩
    obtain ⟨w, hwY, hwy⟩ := Subgroup.mem_map.mp hyY
    refine ⟨w, ⟨hwY, k, ?_⟩, hwy⟩
    apply hφ
    rw [map_pow, hwy, hk, map_one]

theorem ggOTwoPrime_top_map_subtype {G : Type} [Group G] {C : Subgroup G} :
    (ggOTwoPrime (⊤ : Subgroup ↥C)).map C.subtype = ggOTwoPrime C := by
  rw [ggOTwoPrime_map_of_injective C.subtype C.subtype_injective ⊤]
  congr 1
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem ggOTwoPrime_top_map_mulEquiv {C D : Type} [Group C] [Group D] (e : C ≃* D) :
    (ggOTwoPrime (⊤ : Subgroup C)).map e.toMonoidHom = ggOTwoPrime (⊤ : Subgroup D) := by
  rw [ggOTwoPrime_map_of_injective e.toMonoidHom e.injective ⊤,
    Subgroup.map_top_of_surjective _ e.surjective]

end CFSG.StandardType

end
