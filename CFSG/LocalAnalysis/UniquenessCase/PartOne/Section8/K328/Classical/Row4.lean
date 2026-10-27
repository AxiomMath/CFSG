module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row4.Facts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row4.Pos
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row4.Size
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row4.Class
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row4.Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open

theorem row4_holds (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Fintype.card F = 2 → ∀ z₀ t₀ : GL (Fin 6) F,
      (z₀ : Matrix (Fin 6) (Fin 6) F) = blockDiag3 F 6 (rhoOmega F) (rhoOmega F) (rhoOmega F) →
      (t₀ : Matrix (Fin 6) (Fin 6) F) = blockDiag3 F 6 (rhoOmega F) (rhoOmega F ^ 2) 1 →
      MatrixRowData (StatedSL 6 F) z₀ t₀ (stdComp (StatedSL 6 F) z₀) := by
  intro hF z₀ t₀ hz ht
  exact matrixRowData_stdComp
    (row4_facts F hF z₀ t₀ hz ht)
    (row4_pos F hF z₀ t₀ hz ht)
    (row4_size F hF z₀ t₀ hz ht)
    (row4_class F hF z₀ t₀ hz ht)
    (row4_gen F hF z₀ t₀ hz ht)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
