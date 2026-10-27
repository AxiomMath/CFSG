module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']

theorem nonempty_bar2_hinf_map (e : G ≃* G') (P : Subgroup G) :
    Nonempty (Bar2 (Hinf P) ≃* Bar2 (Hinf (P.map e.toMonoidHom))) := by
  obtain ⟨f⟩ := nonempty_bar2_mulEquiv_map (Hinf P) e
  rw [← Hinf_map e.toMonoidHom P]
  exact ⟨f⟩

theorem hinf_map_mulEquiv_eq_bot_iff (e : G ≃* G') (P : Subgroup G) :
    Hinf (P.map e.toMonoidHom) = ⊥ ↔ Hinf P = ⊥ := by
  constructor
  · intro h
    have h1 : (Hinf P).map e.toMonoidHom = ⊥ := by
      rw [Hinf_map e.toMonoidHom P, h]
    exact (Subgroup.map_eq_bot_iff_of_injective (Hinf P) e.injective).mp h1
  · intro h
    rw [← Hinf_map e.toMonoidHom P, h, Subgroup.map_bot]

theorem map_mulEquiv_eq_top_iff (e : G ≃* G') (P : Subgroup G) :
    P.map e.toMonoidHom = ⊤ ↔ P = ⊤ := by
  constructor
  · intro h
    have h' : P.map e.toMonoidHom = (⊤ : Subgroup G).map e.toMonoidHom := by
      rw [h, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
    exact Subgroup.map_injective e.injective h'
  · rintro rfl
    exact Subgroup.map_top_of_surjective e.toMonoidHom e.surjective

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
