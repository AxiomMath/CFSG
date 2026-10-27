module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row7.Facts
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row7.Pos
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row7.Size
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row7.Class
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Classical.Row7.Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open

theorem row7_holds (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Fintype.card F = 8 → ∀ z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F,
      (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = rhoL F 0 1 →
      (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
        rhoL F (Matrix.diagonal ![0, 1, 1]) (Matrix.diagonal ![1, 1, 0]) →
      MatrixRowData (StatedSp 3 F) z₀ t₀ (stdComp (StatedSp 3 F) z₀) := by
  intro hF z₀ t₀ hz ht
  exact matrixRowData_stdComp
    (row7_facts F hF z₀ t₀ hz ht)
    (row7_pos F hF z₀ t₀ hz ht)
    (row7_size F hF z₀ t₀ hz ht)
    (row7_class F hF z₀ t₀ hz ht)
    (row7_gen F hF z₀ t₀ hz ht)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
