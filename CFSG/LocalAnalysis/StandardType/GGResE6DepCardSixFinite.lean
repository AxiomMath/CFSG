module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepCardSixDefs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def cs6TypeCartan : Fin 4 → Matrix (Fin 5) (Fin 5) ℤ :=
  ![CartanMatrix.A 5, CartanMatrix.B 5, CartanMatrix.C 5, CartanMatrix.D 5]

@[expose] def cs6TypeDet : Fin 4 → Nat := ![6, 2, 2, 4]

theorem cs6_y_cases (jj : Fin 5) (v : CS6E)
    (hv : ∀ i : Fin 4, ggDepAdot (cs6Alpha (cs6J jj i)) v = 0)
    (hvx : ∃ j : Fin 5, v j.castSucc ≠ 0) :
    ∃ r ∈ cs6Ys jj, v = r ∨ v = -r := by
  revert jj v
  decide +kernel

theorem cs6_pattern_bridge (jj : Fin 5) (X : Fin 4) (σ : Equiv.Perm (Fin 5))
    (hJ : ∀ i j : Fin 4,
      ((cs6TypeCartan X (σ.symm i.castSucc) (σ.symm j.castSucc) : ℤ) : ZMod 3) =
        ((CartanMatrix.E 6 (cs6J jj i) (cs6J jj j) : ℤ) : ZMod 3)) :
    ∃ pi < cs6NumPat jj, cs6PatDet jj pi = cs6TypeDet X ∧
      ∀ i : Fin 4,
        ((cs6TypeCartan X (σ.symm i.castSucc) (σ.symm (Fin.last 4)) : ℤ) : ZMod 3) =
            (cs6PatPair jj pi i).1 ∧
          ((cs6TypeCartan X (σ.symm (Fin.last 4)) (σ.symm i.castSucc) : ℤ) : ZMod 3) =
            (cs6PatPair jj pi i).2 := by
  revert jj X σ
  decide +kernel

end CFSG.StandardType
