module

public import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.Sec4.T444.Item434L34Seitz

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.Assembly.RankThreeEven (projSL)

theorem ks18L34Gen :
    ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* projSL 3 (GaloisField 2 2)) →
      ∀ F : Subgroup (MulAut X), CFSG.Assembly.IsElemAbelian 3 F → Nat.card F = 9 →
        Subgroup.closure {x : X | ∃ φ ∈ F, φ ≠ 1 ∧ φ x = x} = ⊤ ∨
        F ≤ (MulAut.conj : X →* MulAut X).range := by
  intro X _ _ ⟨e⟩ F hF hF9
  by_cases hin : F ≤ (MulAut.conj : X →* MulAut X).range
  · exact Or.inr hin
  left
  set ψ : X ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 2) :=
    e.trans (L34.projSLEquivProjectiveSL 3 _) with hψ
  have h := Sec4.Item434L34Seitz.fixClosure_eq_top_of_mulEquiv ψ
    (Sec4.Item434L34Seitz.fixClosure_eq_top_psl L34.card_galoisField_two_two
      (Sec4.isElemAbelian_map _ hF)
      (by
        rw [Subgroup.card_map_of_injective (f := (MulAut.congr ψ).toMonoidHom)
          (MulAut.congr ψ).injective, hF9])
      (Sec4.Item434L34Seitz.not_le_range_conj_map ψ hin))
  exact h

end CFSG.RankThree.PartTwo.KFacts
