module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row2.Facts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row2.Pos
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row2.Size
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row2.Class
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row2.Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open

theorem row2_holds (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Fintype.card F = 4 → ∀ ω : F, ω ^ 2 + ω + 1 = 0 → ∀ z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F,
      (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
        Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]) →
      (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
        Matrix.diagonal (Sum.elim ![ω, ω ^ 2, 1] ![ω ^ 2, ω, 1]) →
      MatrixRowData (StatedSp 3 F) z₀ t₀ (stdComp (StatedSp 3 F) z₀) := by
  intro hF ω hω z₀ t₀ hz ht
  exact matrixRowData_stdComp
    (row2_facts F hF ω hω z₀ t₀ hz ht)
    (row2_pos F hF ω hω z₀ t₀ hz ht)
    (row2_size F hF ω hω z₀ t₀ hz ht)
    (row2_class F hF ω hω z₀ t₀ hz ht)
    (row2_gen F hF ω hω z₀ t₀ hz ht)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
