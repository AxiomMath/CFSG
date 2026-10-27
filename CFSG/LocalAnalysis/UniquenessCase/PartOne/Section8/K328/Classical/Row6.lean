module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row6.Facts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row6.Pos
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row6.Size
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row6.Class
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row6.Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open

theorem row6_holds (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Fintype.card F = 64 → ∀ ω : F, ω ^ 2 + ω + 1 = 0 → ∀ z₀ t₀ : GL (Fin 4) F,
      (z₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω, ω, 1] →
      (t₀ : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![ω, ω ^ 2, 1, 1] →
      MatrixRowData (StatedSU 4 8 F) z₀ t₀ (stdComp (StatedSU 4 8 F) z₀) := by
  intro hF ω hω z₀ t₀ hz ht
  exact matrixRowData_stdComp
    (row6_facts F hF ω hω z₀ t₀ hz ht)
    (row6_pos F hF ω hω z₀ t₀ hz ht)
    (row6_size F hF ω hω z₀ t₀ hz ht)
    (row6_class F hF ω hω z₀ t₀ hz ht)
    (row6_gen F hF ω hω z₀ t₀ hz ht)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
