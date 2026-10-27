
module

public import CFSG.RankThree.Chevalley.SteinbergBIWE8Reps
import Certificates.Kernel.WE8K.Glue
public import CFSG.RankThree.Chevalley.SteinbergBIWE8Enum
import CFSG.Certificates.Kernel.WE8KCount

public section

namespace Certificates

open CFSG.KD.WE8K CFSG.RankThree.Chevalley.WeylE8

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint in
open CFSG.LieType.Chevalley.WE8.Native CFSG.RankThree.Chevalley.WeylE8 in
theorem certificate18004 :
    (∀ i < 9, Nat.card {u : W8 // IsConj (rep i) u} = classSizes.getD i 0) ∧
    (∀ i < 8, IsConj (rep (zClass.getD i 0)) (rep 8 * rep i)) ∧
    (∀ j : Fin Tag.E8.rank, IsConj (rep 0) (simple .E8 j)) ∧
    Nat.card {u : W8 // IsConj y0 u} = 15120 ∧
    Nat.card {w : W8 // SgnSym 1 w} ≤ 199952 ∧ Nat.card {w : W8 // SgnSym (-1) w} ≤ 15120 :=
  have hl := ch18004_lower
  have hu := ch18004_upper
  cert18004_of_bounds hl.1 hl.2 hu.1 hu.2

end Certificates
