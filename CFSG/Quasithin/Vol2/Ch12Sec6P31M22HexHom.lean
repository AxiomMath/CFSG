module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13.P31Sec.M22Hex

theorem exists_cover_hom {X : Type} [Group X]
    (hX : CFSG.Quasithin.IsSporadic .M22 X ∨
      CFSG.Quasithin.IsHat X (CFSG.Blueprint.NativeSporadic.Carrier .M22)) :
    ∃ π : X →* ↥CFSG.Blueprint.NativeSporadic.M22, Function.Surjective π ∧
      (∀ z ∈ π.ker, ∀ g : X, g * z = z * g) ∧
      (∀ α : X ≃* X, π.ker.map α.toMonoidHom = π.ker) := by
  rcases hX with h | h
  ·
    obtain ⟨e⟩ := h
    let e' : X ≃* ↥CFSG.Blueprint.NativeSporadic.M22 := e
    have hker : e'.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 e'.injective
    refine ⟨e'.toMonoidHom, e'.surjective, ?_, ?_⟩
    · intro z hz g
      rw [hker, Subgroup.mem_bot] at hz
      rw [hz, mul_one, one_mul]
    · intro α
      rw [hker, Subgroup.map_bot]
  ·
    obtain ⟨-, -, ⟨e⟩⟩ := h
    let e' : X ⧸ Subgroup.center X ≃* ↥CFSG.Blueprint.NativeSporadic.M22 := e
    have hker : (e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))).ker
        = Subgroup.center X := by
      rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center X))
        e'.toMonoidHom e'.injective, QuotientGroup.ker_mk']
    refine ⟨e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)), ?_, ?_, ?_⟩
    · exact e'.surjective.comp (QuotientGroup.mk'_surjective _)
    · intro z hz g
      rw [hker] at hz
      exact Subgroup.mem_center_iff.mp hz g
    · intro α
      rw [hker]
      exact Subgroup.map_center_eq α

theorem isSylowTwoOf_map {G M : Type} [Group G] [Group M] (π : G →* M)
    (hπ : Function.Surjective π) {S : Subgroup G} (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    CFSG.QuasithinUnique.IsSylowTwoOf (S.map π) ⊤ := by
  obtain ⟨-, hp, hodd⟩ := hS
  have h1 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right (H := S)
  have h2 : ((S.map π).subgroupOf ⊤).index = (S.map π).index :=
    Subgroup.relIndex_top_right (H := S.map π)
  refine ⟨le_top, hp.map π, ?_⟩
  rw [h2]
  rw [h1] at hodd
  intro h
  exact hodd (h.trans (S.index_map_dvd hπ))

end CFSG.Quasithin.H13.P31Sec.M22Hex
