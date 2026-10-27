module

public import CFSG.Sporadic.Schreier.LyMatrixSchreier
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingOuterBound

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms

theorem model_schreier
    (K : Type*) [Group K] (hK : Nonempty (K ≃* NativeSporadic.Ly)) :
    Group.IsSolvable (Outer K) := by
  obtain ⟨e⟩ := hK
  have hLy : Group.IsSolvable (Outer NativeSporadic.Ly) :=
    (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism (G := NativeSporadic.Ly) (H := J)
      (by exact lyEquivJ)).2.2 matrix_schreier
  exact (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism (G := K) (H := NativeSporadic.Ly)
    (by exact e)).2.2 hLy

end CFSG.Sporadic.LySchreier
