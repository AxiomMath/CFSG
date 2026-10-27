module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

theorem isMaxParabolicOver_map_conj {G : Type} [Group G] {X S P : Subgroup G} {g : G}
    (hP : IsMaxParabolicOver X S P) :
    IsMaxParabolicOver (X.map (MulAut.conj g).toMonoidHom)
      (S.map (MulAut.conj g).toMonoidHom) (P.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hPX, hNP, hne, hmax⟩ := hP
  refine ⟨Subgroup.map_mono hPX, ?_, ?_, ?_⟩
  · calc
      X.map (MulAut.conj g).toMonoidHom ⊓
          Subgroup.normalizer ((S.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)
          = X.map (MulAut.conj g).toMonoidHom ⊓
              (Subgroup.normalizer (S : Set G)).map (MulAut.conj g).toMonoidHom := by
            rw [Subgroup.map_equiv_normalizer_eq]
      _ = (X ⊓ Subgroup.normalizer (S : Set G)).map (MulAut.conj g).toMonoidHom := by
            rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
      _ ≤ P.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hNP
  · intro h
    exact hne ((Subgroup.map_injective (MulAut.conj g).injective) h)
  · intro Q hPQ hQX
    let e : MulAut G := MulAut.conj g
    have hPQ' : P ≤ (e.mapSubgroup).symm Q := by
      rw [← (e.mapSubgroup).apply_symm_apply Q] at hPQ
      exact (e.mapSubgroup).le_iff_le.mp hPQ
    have hQX' : (e.mapSubgroup).symm Q ≤ X := by
      rw [← (e.mapSubgroup).apply_symm_apply Q,
        show X.map e.toMonoidHom = e.mapSubgroup X from rfl] at hQX
      exact (e.mapSubgroup).le_iff_le.mp hQX
    rcases hmax ((e.mapSubgroup).symm Q) hPQ' hQX' with h | h
    · left
      rw [← (e.mapSubgroup).apply_symm_apply Q, h]
      rfl
    · right
      rw [← (e.mapSubgroup).apply_symm_apply Q, h,
        show X.map e.toMonoidHom = e.mapSubgroup X from rfl]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
