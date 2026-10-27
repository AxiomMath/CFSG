module

public import Certificates.Data.J4M3.Native

public section

namespace CFSG.Quasithin.J4M3

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

@[expose] def g3Word : List Int := [2, 3, -1, -1, -3, -2, -3, 1, 2, 1, 1, 2, 2, 1, -2, -2]

@[expose] def y3Word : List Int := g3Word ++ g3Word

@[expose] def a3Masks : List Nat := [3, 1, 13, 7, 53, 30, 3770, 723, 2313, 3597, 781, 260]

@[expose] def v3Masks : List Nat := [911, 1131, 911, 1602, 2020, 1485, 1602, 1131, 911, 553, 0, 422]

@[expose] def a3Rows (Q : Array (Array V2)) (c : Nat) : Array V2 :=
  (List.range 12).foldl (fun acc j => if c.testBit j then mulRows acc (Q[j]?.getD idRows) else acc)
    idRows

@[expose] def chkY3With (T Q : Array (Array V2)) (Y : Array V2) : Bool :=
  eqRows (mulRows (mulRows Y Y) Y) idRows && centV0 T Y &&
    (List.range 12).all fun i =>
      eqRows (mulRows (a3Rows Q (a3Masks.getD i 0)) Y)
        (mulRows (mulRows (mulRows (Q[i]?.getD idRows) (eR T (v3Masks.getD i 0))) Y)
          (a3Rows Q (a3Masks.getD i 0)))

@[expose] def chkY3 (_ : Unit := ()) : Bool :=
  let loc := locMats ()
  let inv := locInvs ()
  let T := uTab loc inv
  let X := wordRows loc inv xWord
  let Xi := wordRows loc inv (invWord xWord)
  let Q := ((List.range 12).map fun j =>
    commRows (pRows loc inv T j) (pInvRows loc inv T j) X Xi).toArray
  chkY3With T Q (wordRows loc inv y3Word)

end CFSG.Quasithin.J4M3
