module

public import CFSG.Sporadic.J4.QT2LocNative

public section

namespace CFSG.Quasithin.J4M3

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

@[expose] def nWordL : List Int := [
    -1, -3, 1, 2, -3, 1, 2, 3, 2, -1, -3, 1, -2, -2, -3, 1, 2, -3, -1, -3, -1, -2, 3, 1, 1, -2,
    -1, 3, 2, 2, -1, -3, -1, -3, -2, -3, 2, 1, -2, -1, 2, 3, -1, -2, -1, 2]

@[expose] def nWordR : List Int := [
    1, 3, 3, 1, -3, 2, -1, -3, 1, 3, -2, 3, -1, 2, 1, -2, -1, 2, 3, -1, -2, -1, 2]

@[expose] def ptMasks : List Nat := [0, 1, 16, 17]

@[expose] def extraMasks : List Nat := [3, 5, 8, 49, 81, 128]

@[expose] def sWords : List (List Int) := [
  [
    1, 1, -1, -2, -1, 2, 1, 1, 2, -1, -1, -2, -1, 2, 1, 1, 2, -1, -1, -2, -1, 2, 1, 1, 2, -1,
    -1, -2, -1, 2, 1, 1, 2, -1, -1, -2, -1, 2, 1, 1, 2, -1, -1, -2, -1, 2, 1, 1, 2, -1, -1, -2,
    -1, 2, 1, 1, 2, -1, -1, -1, 1, -3, -3, -3, -1, 2, 1, -3, -3, -3, -2, 1, -2, -1, -2, -1, -1,
    -1, 3, -1, -3, -2, 3, 3, -2, -3, 1, 2, -1, 2, 1, -2, -1, 2, 3, -1, -2, -1, 2, 1, -3, -1, -3,
    1, 2, -1, -1, -2, -3, -1, -2, -1, 2, -1, -3, -1, -3, 1, -3, -1, -3, -2, 1, -2, -2, 3, 3, 3,
    -2, -3, 1, 2, -1, 1, -2, -1, -1, -2, 1, 2, 1, 1, -2, -1, -1, -2, 1, 2, 1, 1, -2, -1, -1, -2,
    1, 2, 1, 1, -2, -1, -1, -2, 1, 2, 1, 1, -2, -1, -1, -2, 1, 2, 1, 1, -2, -1, -1, -2, 1, 2, 1,
    1, -2, -1, -1, -2, 1, 2, 1],
  [
    3, 1, -3, -2, -3, 2, 3, 3, 1, -2, -1, -3, 1, -3, -1, -3, -2, 1, -2, -2, 3, 3, 3, -2, -3, 1,
    2, -1, 2, -1, 2, -1, -1, 2, 2, -3, -2, -3, -2, -2, 1, 3, 1, -3, -2, -3, 2, 3, 3, 1, -2, -1,
    -3, 1, -3, -1, -3, -2, 1, -2, -2, 3, 3, 3, -2, -3, 1, 2, -1, 2, -1, 2, -1, -1, 2, 2, -3, -2,
    -3, -2, -2, 1],
  [
    1, -3, -3, -3, -1, 2, 1, -3, -3, -3, -2, 1, -2, -1, -2, -1, -1, -1, 3, -1, -3, -2, 3, 3, -2,
    -3, 1, 2, -1, 2, 1, -2, -1, 2, 3, -1, -2, -1, 2, 1, -3, -3, -3, -1, 2, 1, -3, -3, -3, -2, 1,
    -2, -1, -2, -1, -1, -1, 3, -1, -3, -2, 3, 3, -2, -3, 1, 2, -1, 2, 1, -2, -1, 2, 3, -1, -2,
    -1, 2],
  [
    1, -3, -3, -3, -1, 2, 1, -3, -3, -3, -2, 1, -2, -1, -2, -1, -1, -1, 3, -1, -3, -2, 3, 3, -2,
    -3, 1, 2, -1, 2, 1, -2, -1, 2, 3, -1, -2, -1, 2, 1, -2, -1, 3, 2, -3, -3, -3, 2, 2, -1, 2,
    3, 1, 3, -1, 3, 1, 3, 1, -2, 1, 2, 1, 3, 2, 1, 1, -2, -1, 3, 1, 3, -1, 1, -2, -1, -1, -2, 1,
    2, 1, 1, -2, -1, -1, -2, 1, 2, 1, 1, -2, -1, -1, -2, 1, 2, 1, 1, -2, -1, -1, -2, 1, 2, 1, 1,
    -2, -1, -1, -2, 1, 2, 1, 1, -2, -1, -1, -2, 1, 2, 1, 1, -2, -1, -1, -2, 1, 2, 1],
  [
    1, 1, -1, -2, -1, 2, 1, 1, 2, -1, -1, -2, -1, 2, 1, 1, 2, -1, -1, -2, -1, 2, 1, 1, 2, -1,
    -1, -2, -1, 2, 1, 1, 2, -1, -1, -2, -1, 2, 1, 1, 2, -1, -1, -2, -1, 2, 1, 1, 2, -1, -1, -2,
    -1, 2, 1, 1, 2, -1, -1, -1, 3, 1, -3, -2, -3, 2, 3, 3, 1, -2, -1, -3, 1, -3, -1, -3, -2, 1,
    -2, -2, 3, 3, 3, -2, -3, 1, 2, -1, 2, -1, 2, -1, -1, 2, 2, -3, -2, -3, -2, -2, 1, 1, -3, -3,
    -3, -1, 2, 1, -3, -3, -3, -2, 1, -2, -1, -2, -1, -1, -1, 3, -1, -3, -2, 3, 3, -2, -3, 1, 2,
    -1, 2, 1, -2, -1, 2, 3, -1, -2, -1, 2, 1, -3, -1, -3, 1, 2, -1, -1, -2, -3, -1, -2, -1, 2,
    -1, -3, -1, -3, 1, -3, -1, -3, -2, 1, -2, -2, 3, 3, 3, -2, -3, 1, 2, -1, -1, 2, 2, 3, 2, 3,
    -2, -2, 1, 1, -2, 1, -2, 1, -2, -1, 3, 2, -3, -3, -3, 2, 2, -1, 2, 3, 1, 3, -1, 3, 1, 2, -1,
    -3, -3, -2, 3, 2, 3, -1, -3],
  [
    3, 1, -3, -2, -3, 2, 3, 3, 1, -2, -1, -3, 1, -3, -1, -3, -2, 1, -2, -2, 3, 3, 3, -2, -3, 1,
    2, -1, 2, -1, 2, -1, -1, 2, 2, -3, -2, -3, -2, -2, 1, 1, -3, -3, -3, -1, 2, 1, -3, -3, -3,
    -2, 1, -2, -1, -2, -1, -1, -1, 3, -1, -3, -2, 3, 3, -2, -3, 1, 2, -1, 2, 1, -2, -1, 2, 3,
    -1, -2, -1, 2, 1, -3, -3, -3, -1, 2, 1, -3, -3, -3, -2, 1, -2, -1, -2, -1, -1, -1, 3, -1,
    -3, -2, 3, 3, -2, -3, 1, 2, -1, 2, 1, -2, -1, 2, 3, -1, -2, -1, 2, -1, 2, 2, 3, 2, 3, -2,
    -2, 1, 1, -2, 1, -2, 1, -2, -1, 3, 2, -3, -3, -3, 2, 2, -1, 2, 3, 1, 3, -1, 3, 1, 2, -1, -3,
    -3, -2, 3, 2, 3, -1, -3]]

@[expose] def xWord : List Int := [
    3, 3, -1, 3, 3, -1, 3, 3, -1, -2, 1, 2, 1, -3, -2, 1, 2, -1, -2, -1, 2, 2, 3, 2, 3, -2, -2,
    1, 1, -2, 1, -2, -3, 2, 2, -1, 2, 3, 1, 3, -1, 3, 3, -1, -3, -1, -2, -3, -1, -2, 1, 1, 1, 1,
    -3, -2, 3, 2, 3, 3, -1, 3, 3, -1, -2, 1, 2, 1, -3, -2, 1, 2, -1, -2, -1, 2, 2, 3, 2, 3, -2,
    -2, 1, 1, -2, 1, -2, -3, 2, 2, -1, 2, 3, 1, 3, -1, 3, 3, -1, -3, -1, -2, -3, -1, -2, 1, 1,
    1, 1, -3, -2, 3, 2, 3, 3, -1, -2, 1, 2, 1, -3, -2, 1, 2, -1, -2, -1, 2, 2, 3, 2, 3, -2, -2,
    1, 1, -2, 1, -2, -3, 2, 2, -1, 2, 3, 1, 3, -1, 3, 3, -1, -3, -1, -2, -3, -1, -2, 1, 1, 1, 1,
    -3, -2, 3, 2, -2, 1, 2, 1, -3, -2, 1, 2, -1, -2, -1, 2, 2, 3, 2, 3, -2, -2, 1, 1, -2, 1, -2,
    -3, 2, 2, -1, 2, 3, 1, 3, -1, 3, 3, -1, -3, -1, -2, -3, -1, -2, 1, 1, 1, 1, -3, -2, 3, 2]

@[expose] def cWord : List Int := [
    3, 1, -3, -2, -3, 2, 3, 3, 1, -2, -1, -3, 1, -3, -1, -3, -2, 1, -2, -2, 3, 3, 3, -2, -3, 1,
    2, -1, 2, -1, 2, -1, -1, 2, 2, -3, -2, -3, -2, -2, 1]

@[expose] def commTab : List (List Nat) := [
    [0, 0, 0, 0, 0, 0, 2020, 553, 2020, 1131, 422, 1485],
    [0, 0, 0, 0, 0, 0, 553, 422, 553, 0, 911, 2020],
    [0, 0, 0, 0, 0, 0, 1485, 553, 0, 2020, 553, 0],
    [0, 0, 0, 0, 0, 0, 0, 553, 2020, 422, 1602, 1485],
    [0, 0, 0, 0, 0, 0, 1131, 553, 553, 1602, 911, 553],
    [0, 0, 0, 0, 0, 0, 2020, 0, 2020, 1131, 2020, 2020],
    [2020, 553, 1485, 0, 1131, 2020, 0, 422, 1131, 1485, 422, 0],
    [553, 422, 553, 553, 553, 0, 422, 0, 1602, 0, 911, 1602],
    [2020, 553, 0, 2020, 553, 2020, 1131, 1602, 0, 911, 553, 0],
    [1131, 0, 2020, 422, 1602, 1131, 1485, 0, 911, 0, 1131, 1131],
    [422, 911, 553, 1602, 911, 2020, 422, 911, 553, 1131, 0, 1131],
    [1485, 2020, 0, 1485, 553, 2020, 0, 1602, 0, 1131, 1131, 0]]

@[expose] def sqTab : List Nat := [0, 0, 0, 0, 0, 0, 1131, 0, 0, 553, 911, 0]

@[expose] def v0Masks : List Nat := [0, 422, 553, 911, 1131, 1485, 1602, 2020]

@[expose] def v0Gens : List Nat := [422, 553, 1131]

@[expose] def eR (T : Array (Array V2)) (c : Nat) : Array V2 := etaRows T 11 c

@[expose] def u5Rows (_ : Unit := ()) : Array V2 := pathRows (repPaths.getD 5 [])

@[expose] def u5Inv (_ : Unit := ()) : Array V2 := invRows (u5Rows ())

@[expose] def nRows (loc inv : Array (Array V2)) : Array V2 :=
  mulRows (mulRows (wordRows loc inv (invWord nWordL)) (u5Rows ()))
    (wordRows loc inv (invWord nWordR))

@[expose] def nInvRows (loc inv : Array (Array V2)) : Array V2 :=
  mulRows (mulRows (wordRows loc inv nWordR) (u5Inv ())) (wordRows loc inv nWordL)

@[expose] def ptVec (Ni : Array V2) (T : Array (Array V2)) (c : Nat) : V2 :=
  frApply (frTable (mulRows Ni (eR T c))) rootV

@[expose] def pRows (loc inv : Array (Array V2)) (T : Array (Array V2)) (i : Nat) : Array V2 :=
  if i < 6 then eR T (extraMasks.getD i 0) else wordRows loc inv (sWords.getD (i - 6) [])

@[expose] def pInvRows (loc inv : Array (Array V2)) (T : Array (Array V2)) (i : Nat) :
    Array V2 :=
  if i < 6 then eR T (extraMasks.getD i 0) else wordRows loc inv (invWord (sWords.getD (i - 6) []))

@[expose] def rowsDiffer (A B : Array V2) : Bool :=
  (List.range 112).any fun i => differs (A[i]?.getD V2.zero) (B[i]?.getD V2.zero)

@[expose] def commRows (P Pi X Xi : Array V2) : Array V2 := mulRows (mulRows (mulRows P X) Pi) Xi

@[expose] def chkU5 (_ : Unit := ()) : Bool := eqRows (mulRows (u5Rows ()) (u5Inv ())) idRows

@[expose] def chkNWith (T : Array (Array V2)) (N Ni : Array V2) : Bool :=
  v0Gens.all fun c => v0Masks.any fun d => eqRows (mulRows (mulRows N (eR T c)) Ni) (eR T d)

@[expose] def chkN (_ : Unit := ()) : Bool :=
  let loc := locMats ()
  let inv := locInvs ()
  chkNWith (uTab loc inv) (nRows loc inv) (nInvRows loc inv)

@[expose] def chkPtsWith (Ni : Array V2) (T : Array (Array V2)) : Bool :=
  ptMasks.all (fun c => differs (ptVec Ni T c) rootV) &&
    ptMasks.all fun c => ptMasks.all fun d => c == d || differs (ptVec Ni T c) (ptVec Ni T d)

@[expose] def chkPts (_ : Unit := ()) : Bool :=
  let loc := locMats ()
  let inv := locInvs ()
  chkPtsWith (nInvRows loc inv) (uTab loc inv)

@[expose] def fixesPts (Ni : Array V2) (T : Array (Array V2)) (P : Array V2) : Bool :=
  ptMasks.all fun c => (frApply (frTable P) (ptVec Ni T c)).beq (ptVec Ni T c)

@[expose] def centV0 (T : Array (Array V2)) (P : Array V2) : Bool :=
  v0Gens.all fun c => eqRows (mulRows P (eR T c)) (mulRows (eR T c) P)

@[expose] def chkPWith (loc inv : Array (Array V2)) (T : Array (Array V2)) (Ni X Xi : Array V2) :
    Bool :=
  ((List.range 12).all fun i =>
      fixesPts Ni T (pRows loc inv T i) && centV0 T (pRows loc inv T i)) &&
    fixesPts Ni T X &&
    (v0Gens.all fun c => v0Masks.any fun d => eqRows (mulRows (mulRows X (eR T c)) Xi) (eR T d)) &&
    rowsDiffer (mulRows (mulRows X (eR T 1131)) Xi) (eR T 1131)

@[expose] def chkP (_ : Unit := ()) : Bool :=
  let loc := locMats ()
  let inv := locInvs ()
  chkPWith loc inv (uTab loc inv) (nInvRows loc inv) (wordRows loc inv xWord)
    (wordRows loc inv (invWord xWord))

@[expose] def chkQWith (loc inv : Array (Array V2)) (T : Array (Array V2)) (X Xi : Array V2) :
    Bool :=
  (List.range 12).all fun i =>
    let qi := commRows (pRows loc inv T i) (pInvRows loc inv T i) X Xi
    let qii := commRows X Xi (pRows loc inv T i) (pInvRows loc inv T i)
    eqRows (mulRows qi qi) (eR T (sqTab.getD i 0)) &&
      (List.range 12).all fun j =>
        let qj := commRows (pRows loc inv T j) (pInvRows loc inv T j) X Xi
        let qji := commRows X Xi (pRows loc inv T j) (pInvRows loc inv T j)
        eqRows (commRows qi qii qj qji) (eR T ((commTab.getD i []).getD j 0))

@[expose] def chkQ (_ : Unit := ()) : Bool :=
  let loc := locMats ()
  let inv := locInvs ()
  chkQWith loc inv (uTab loc inv) (wordRows loc inv xWord) (wordRows loc inv (invWord xWord))

@[expose] def chkCWith (Ni : Array V2) (T : Array (Array V2)) (C : Array V2) : Bool :=
  centV0 T C && (frApply (frTable C) (ptVec Ni T 0)).beq (ptVec Ni T 0) &&
    (frApply (frTable C) (ptVec Ni T 1)).beq (ptVec Ni T 1) &&
    (frApply (frTable C) (ptVec Ni T 16)).beq (ptVec Ni T 17) &&
    (frApply (frTable C) (ptVec Ni T 17)).beq (ptVec Ni T 16)

@[expose] def chkC (_ : Unit := ()) : Bool :=
  let loc := locMats ()
  let inv := locInvs ()
  chkCWith (nInvRows loc inv) (uTab loc inv) (wordRows loc inv cWord)

end CFSG.Quasithin.J4M3
