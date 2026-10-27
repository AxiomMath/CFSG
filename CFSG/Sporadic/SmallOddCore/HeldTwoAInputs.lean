module

public import CFSG.Sporadic.SmallOddCore.HeLocal

public section

namespace CFSG.Sporadic.SmallOddCore

open CFSG.Sporadic.HeldB

@[expose] def heU105Arr : Array Nat :=
  #[94, 19, 41, 76, 70, 7, 71, 5, 88, 45, 67, 47, 54, 48, 57, 30, 56, 23, 63, 1, 93, 60, 22, 17,
    65, 97, 72, 74, 32, 84, 15, 40, 28, 69, 85, 87, 78, 86, 89, 83, 31, 2, 66, 101, 79, 9, 100,
    11, 13, 61, 102, 98, 82, 81, 12, 90, 16, 14, 75, 95, 21, 49, 62, 18, 77, 24, 42, 10, 80, 33,
    4, 6, 26, 73, 27, 58, 3, 64, 36, 44, 68, 53, 52, 39, 29, 34, 37, 35, 8, 38, 55, 96, 92, 20,
    0, 59, 91, 25, 51, 103, 46, 43, 50, 99, 104]

@[expose] def heU105 (_ : Unit := ()) : Equiv.Perm (Fin 105) := permOrId 105 heU105Arr


@[irreducible] def heUArrProof (_ : Unit := ()) : Array Nat := heUArr

theorem heUArrProof_eq : heUArrProof () = heUArr := by
  unfold heUArrProof
  rfl

@[expose] def commutesAllD (p : Equiv.Perm (Fin 105)) : Bool :=
  (List.range 5).all fun j => decide (p * heDPerm j = heDPerm j * p)

@[expose] def checkAPred (i : Nat) : Bool :=
  decide (heOmega0.toList.idxOf? ((heUArrProof ())[heOmega0[i]!]!) = some (heU105Arr[i]!))

@[expose] def checkA (_ : Unit := ()) : Bool :=
  (List.range 105).all checkAPred

@[expose] def checkB (_ : Unit := ()) : Bool :=
  heKEnum.tabs.all fun q =>
    let p := permOrId 105 q
    !(commutesAllD p) || decide (p = 1)

@[expose] def checkC (_ : Unit := ()) : Bool :=
  let u := heU105 ()
  heKEnum.tabs.all fun q =>
    !(commutesAllD (permOrId 105 q * u))

end CFSG.Sporadic.SmallOddCore
