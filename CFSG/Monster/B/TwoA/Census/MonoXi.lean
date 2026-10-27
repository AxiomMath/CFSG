module

public import CFSG.Monster.B.TwoA.Census.MonoData
public import CFSG.Monster.CodeAut.BridgeData

public section

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts Matrix

@[expose] def xiLetter (l : ℕ) : Equiv.Perm (Fin 24) := if l = 0 then bridgePA else bridgePB

@[expose] def xiWordPerm (w : List ℕ) : Equiv.Perm (Fin 24) := (w.map xiLetter).reverse.prod

theorem Pmat_xiWordPerm (w : List ℕ) :
    Pmat (xiWordPerm w) = (w.map fun l => Pmat (xiLetter l)).prod := by
  induction w with
  | nil => simp [xiWordPerm, Pmat]
  | cons a w ih =>
    have e : xiWordPerm (a :: w) = xiWordPerm w * xiLetter a := by simp [xiWordPerm]
    simp only [Pmat] at ih ⊢
    rw [e, Matrix.permMatrix_mul, ih, List.map_cons, List.prod_cons]

@[expose] noncomputable def xiConjMat (e : XiEdge) : Matrix (Fin 24) (Fin 24) ℚ :=
  diagonal (fun k => sgn (bvec 24 e.conjSign k)) * Pmat (xiWordPerm e.word)

end CFSG.Monster.B.TwoA.Census
