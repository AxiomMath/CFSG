module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPShapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L3CartanThreeHolds

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsSL3)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def HasSL3Cover (G : Type) [Group G] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    ∃ α : Matrix.SpecialLinearGroup (Fin 3) F →* G,
      Function.Surjective α ∧ α.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)

theorem hasSL3Cover_of_shapeSL3
    {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} (h : ShapeSL3 L) : HasSL3Cover ↥L := by
  obtain ⟨hq, hodd, -⟩ := h.1
  obtain ⟨F, hF, hFin, hcard, α, hsurj, hker⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.exists_sl3_cover (K := ↥L) (f := 2)
      (by norm_num [StatedLieAdmissible]) even_two h.2.2 hq hodd
  exact ⟨F, hF, hFin, by rw [hcard]; norm_num, α, hsurj, hker⟩

theorem hasSL3Cover_of_shapeL3 {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (h : ShapeL3 L) : HasSL3Cover ↥L := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
      (n := 3) h.2
  refine ⟨F, hF, hFin, by rw [hcard]; norm_num,
    e.symm.toMonoidHom.comp (proj 3 F), ?_, ?_⟩
  · exact e.symm.surjective.comp (proj_surjective 3 F)
  · rw [MonoidHom.ker_comp_of_injective (proj 3 F) e.symm.toMonoidHom
      e.symm.injective, ker_proj]
    exact scalars_le_center 3 F

end CFSG.LocalAnalysis.WeakClosure81

end
