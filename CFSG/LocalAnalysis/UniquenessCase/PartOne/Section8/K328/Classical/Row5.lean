module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row5.Facts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row5.Pos
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row5.Size
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row5.Class
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row5.Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open

theorem row5_holds (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Fintype.card F = 2 → ∀ z₀ t₀ : GL (Fin 7) F,
      (z₀ : Matrix (Fin 7) (Fin 7) F) = blockDiag3 F 7 (rhoOmega F) (rhoOmega F) (rhoOmega F) →
      (t₀ : Matrix (Fin 7) (Fin 7) F) = blockDiag3 F 7 (rhoOmega F) (rhoOmega F ^ 2) 1 →
      MatrixRowData (StatedSL 7 F) z₀ t₀ (stdComp (StatedSL 7 F) z₀) := by
  intro hF z₀ t₀ hz ht
  exact matrixRowData_stdComp
    (row5_facts F hF z₀ t₀ hz ht)
    (row5_pos F hF z₀ t₀ hz ht)
    (row5_size F hF z₀ t₀ hz ht)
    (row5_class F hF z₀ t₀ hz ht)
    (row5_gen F hF z₀ t₀ hz ht)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
