module

public import Certificates.Data.TwoF4LieCheck
public import Certificates.Data.TwoF4LocData

public section

namespace CFSG.TwoF4Loc

open CFSG.Monster.B.Co2.Native CFSG.RuF45 CFSG.TwoF4Lie

@[expose] def locConj (c x : Array Nat) : Array Nat :=
  compA 1755 (compA 1755 c x) (invCand 1755 c)

@[expose] def locCol (pts : Array Nat) : List Nat :=
  ((List.range 2925).filter fun w => onLineP pts 0 w).flatMap fun w =>
    [pts[3 * w]!, pts[3 * w + 1]!, pts[3 * w + 2]!]

@[expose] def locCollFixed (pts g : Array Nat) : Bool := (locCol pts).all fun q => g[q]! == q

@[expose] def locFix (tA : Array Nat) : List Nat := (List.range 1755).filter fun p => tA[p]! == p

@[expose] def locLineOK (pts cA : Array Nat) : Bool :=
  onLineP pts 0 0 && onLineP pts cA[0]! 0 && onLineP pts cA[cA[0]!]! 0 &&
    (List.range 3).all fun k => pts[k]! == 0 || pts[k]! == cA[0]! || pts[k]! == cA[cA[0]!]!

@[expose] def locVOK (zA z1 z2 : Array Nat) : Bool :=
  eqA 1755 (compA 1755 zA z1) z2 && eqA 1755 (compA 1755 zA z1) (compA 1755 z1 zA) &&
    !eqA 1755 zA z1

@[expose] def locQOK (tA zA z1 qA : Array Nat) : Bool :=
  eqA 1755 (compA 1755 qA qA) zA && eqA 1755 (compA 1755 qA tA) (compA 1755 tA qA) &&
    eqA 1755 (compA 1755 qA z1) (compA 1755 z1 qA)

@[expose] def locChainOK (pts : Array Nat) (G Gi : Array (Array Nat)) (zA : Array Nat) :
    Array Nat → Array Nat → List (Nat × String) → Bool
  | a, b, [] => eqA 1755 a zA && !locCollFixed pts b
  | a, b, (kd, w) :: rest =>
    let c := wArr G Gi w
    wordOK w && (if kd == 0 then fixesH pts c else fixesN pts c) &&
      isInvA 1755 c (invCand 1755 c) && fixesS pts (locConj c a) && fixesS pts (locConj c b) &&
      locChainOK pts G Gi zA (locConj c a) (locConj c b) rest

@[expose] def locFixOK (pts : Array Nat) (G Gi : Array (Array Nat)) (zA tA z1 z2 : Array Nat) :
    Bool :=
  allLt (locFix tA).length fun k =>
    let m := wArr G Gi locWords[k]!
    let u := locConj m zA
    wordOK locWords[k]! && m[0]! == (locFix tA)[k]! && isInvA 1755 m (invCand 1755 m) &&
      (eqA 1755 u zA || eqA 1755 u z1 || eqA 1755 u z2 ||
        (fixesS pts u && fixesS pts tA && locChainOK pts G Gi zA u tA locChains[k]!))

@[expose] def twoF4LocCheck (pts : Array Nat) (G : Array (Array Nat)) (zA : Array Nat) : Bool :=
  let Gi := invArrs 1755 G
  let tA := tArr G Gi
  let cA := cArr G Gi
  let c2 := compA 1755 cA cA
  let z1 := compA 1755 (compA 1755 cA zA) c2
  let z2 := compA 1755 (compA 1755 c2 zA) cA
  locLineOK pts cA && locVOK zA z1 z2 && wordOK locQWord && locQOK tA zA z1 (wArr G Gi locQWord) &&
    locCollFixed pts tA && locFixOK pts G Gi zA tA z1 z2

end CFSG.TwoF4Loc
