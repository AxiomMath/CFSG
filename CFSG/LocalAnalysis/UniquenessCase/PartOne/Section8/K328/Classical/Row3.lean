module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row3.Facts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row3.Pos
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row3.Size
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row3.Class
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row3.Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open

theorem row3_holds (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Fintype.card F = 4 → ∀ b c : F, (∀ s : F, s ^ 2 + b * s + c ≠ 0) →
      ∀ ω : F, ω ^ 2 + ω + 1 = 0 → ∀ z₀ t₀ : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F,
      (z₀ : Matrix _ _ F) =
        Matrix.diagonal (Sum.elim ![ω, ω, ω] (Sum.elim ![ω ^ 2, ω ^ 2, ω ^ 2] ![1, 1])) →
      (t₀ : Matrix _ _ F) =
        Matrix.diagonal (Sum.elim ![ω, ω ^ 2, 1] (Sum.elim ![ω ^ 2, ω, 1] ![1, 1])) →
      MatrixRowData (StatedOmega (StatedQuadMinus 4 F b c)) z₀ t₀
        (stdComp (StatedOmega (StatedQuadMinus 4 F b c)) z₀) := by
  intro hF b c hbc ω hω z₀ t₀ hz ht
  exact matrixRowData_stdComp
    (row3_facts F hF b c hbc ω hω z₀ t₀ hz ht)
    (row3_pos F hF b c hbc ω hω z₀ t₀ hz ht)
    (row3_size F hF b c hbc ω hω z₀ t₀ hz ht)
    (row3_class F hF b c hbc ω hω z₀ t₀ hz ht)
    (row3_gen F hF b c hbc ω hω z₀ t₀ hz ht)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
