module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelF

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType CFSG.Open CFSG.Assembly SpCoord

variable {G : Type} [Group G] [Finite G]

@[expose] def hdRo7CLCoordAux_piFinSuccEquiv (M : Type) [Monoid M] (k : ℕ) :
    (Fin (k + 1) → M) ≃* ((Fin k → M) × M) where
  toFun f := (Fin.tail f, f 0)
  invFun q := Fin.cons q.2 q.1
  left_inv f := by
    funext i
    cases i using Fin.cases <;> simp [Fin.cons, Fin.tail]
  right_inv q := by
    obtain ⟨g, a⟩ := q
    apply Prod.ext
    · funext i; simp [Fin.cons, Fin.tail]
    · simp [Fin.cons, Fin.tail]
  map_mul' f g := by
    apply Prod.ext
    · funext i
      show (f * g) i.succ = f i.succ * g i.succ
      simp [Pi.mul_apply]
    · simp [Pi.mul_apply]

end CFSG.StandardType.HdRo7C

end
