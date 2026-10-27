module

public import Certificates.Data.CFSGNative.F4.T46SimpleData
public import Certificates.Data.CFSGNative.Fi22.Local

public section

namespace CFSG.F4.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi22.Native

set_option compiler.extract_closed false

@[expose] def t46FixAll (P : Table) : Bool := allIn 0 693 fun i => ap P i == i

@[expose] def t46TblEq (P Q : Table) : Bool := allIn 0 693 fun i => ap P i == ap Q i

@[expose] def t46XT (_ : Unit := ()) : Table := powT 693 3 (wordT 693 t46Gen [30, 33, 16, 12, 9, 39, 39])

@[expose] def t46YT (_ : Unit := ()) : Table := powT 693 2 (wordT 693 t46Gen [41, 46, 21, 23, 36])

@[expose] def t46XYGen (z : Int) : Table := if z = 1 then t46XT else t46YT

@[expose] def t46Lv1 (_ : Unit := ()) : Array Nat := levelLetters t46Letters t46Base 1

@[expose] def t46SubTree (_ : Unit := ()) : Tree := treeBFS 693 t46SubRoot t46Letters t46Lv1

@[expose] def t46InTree (T : Tree) (p : Nat) : Bool :=
  ap T.pos p < T.pts.size && ap T.pts (ap T.pos p) == p

@[expose] def t46SimpleCertificate (_ : Unit) : Bool :=
  t46Words.size == 53 && allIn 0 46 (fun k => t46Words[k]! == [(k : Int) + 1]) &&
    t46FixAll (tvTable 0) && t46FixAll (powT 693 2 t46XT) && !t46FixAll t46XT &&
    t46FixAll (powT 693 3 t46YT) && !t46FixAll t46YT &&
    t46FixAll (powT 693 11 (compT 693 t46XT t46YT)) && !t46FixAll (compT 693 t46XT t46YT) &&
    allIn 0 46 (fun k => t46TblEq (wordT 693 t46XYGen t46TvWords[k]!) (tvTable tvGens[k]!)) &&
    treeOK 693 t46SubRoot t46SubTree t46Letters t46Lv1 && t46SubTree.pts.size == 180 &&
    allIn 0 693 (fun p => p == 0 || t46InTree t46Trees[1]! p || t46InTree t46SubTree p)

end CFSG.F4.Native
