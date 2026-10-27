module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.A8Model

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4K

open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA.CatB

@[expose] def cenA8cExt (a b : Fin 8) : Fin 8 → Fin 8 :=
  ![a, a8c a, a8c (a8c a), b, a8d b, a8d (a8d b),
    (swap 4 5 * swap 5 6 : Perm (Fin 8)) (a8d (a8d b)),
    (swap 5 6 * swap 6 7 : Perm (Fin 8)) ((swap 4 5 * swap 5 6 : Perm (Fin 8)) (a8d (a8d b)))]

theorem cenA8cExt_check : ∀ a b : Fin 8,
    (∀ x, cenA8cExt a b (a8c x) = a8c (cenA8cExt a b x)) →
    (∀ x, cenA8cExt a b (a8d x) = a8d (cenA8cExt a b x)) →
    (∀ x, cenA8cExt a b ((swap 4 5 * swap 5 6 : Perm (Fin 8)) x) =
      (swap 4 5 * swap 5 6 : Perm (Fin 8)) (cenA8cExt a b x)) →
    (∀ x, cenA8cExt a b ((swap 5 6 * swap 6 7 : Perm (Fin 8)) x) =
      (swap 5 6 * swap 6 7 : Perm (Fin 8)) (cenA8cExt a b x)) →
    (∀ x, cenA8cExt a b x = x) ∨ (∀ x, cenA8cExt a b x = a8c x) ∨
      (∀ x, cenA8cExt a b x = a8c⁻¹ x) := by
  decide +kernel

end CFSG.RankThree.PartTwo.Sec21.FF84.S4K
