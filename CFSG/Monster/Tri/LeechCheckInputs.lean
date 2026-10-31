module

public import CFSG.Monster.Tri.LeechData
public import Certificates.Data.CFSGNative.MonsterB.Short

@[expose] public section

namespace CFSG.Monster.Tri.Leech

open CFSG.Monster.VisCert.Native

def tablesKlev (T : CFSG.Monster.B.Short.Native.ShortTables) : ByteArray := T.klev

def shortKlev : ByteArray := tablesKlev CFSG.Monster.B.Short.Native.shortTables

def shortHit (klev : ByteArray) (n : Nat) : Bool := decide (n < 2 ^ 24) && rd8 klev n != 0

def treeOK (klev : ByteArray) (vs par lev : Array Nat) : Bool :=
  (List.range vs.size).all fun i =>
    i == 0 || (decide (par[i]! < vs.size) && (lev[par[i]!]! + 1 == lev[i]!) &&
      shortHit klev (vs[i]! ^^^ vs[par[i]!]!))

def sortedOK (vs : Array Nat) : Bool :=
  (List.range vs.size).all fun i => i + 1 == vs.size || decide (vs[i]! < vs[i + 1]!)

def nbrOK (klev : ByteArray) (nbr : Array Nat) : Bool :=
  (nbr.size == 4600) && sortedOK nbr && (List.range nbr.size).all fun i =>
    shortHit klev nbr[i]! && shortHit klev (nbr[i]! ^^^ 12288)

def muOK (klev : ByteArray) (nbr : Array Nat) (b : Nat) (vs : Array Nat) : Bool :=
  sortedOK vs && vs.toList.all (fun n => shortHit klev n && shortHit klev (n ^^^ 12288) &&
    shortHit klev (n ^^^ b)) &&
    nbr.toList.all fun n => !shortHit klev (n ^^^ b) || decide (n ∈ vs.toList)

def leechCheck : Bool :=
  nbrOK shortKlev leechNbr &&
  treeOK shortKlev leechNbr leechNbrPar leechNbrLev &&
  muOK shortKlev leechNbr 1 leechIdx3 &&
  treeOK shortKlev leechIdx3 leechPar3 leechLev3 &&
  muOK shortKlev leechNbr 64 leechIdx4 &&
  treeOK shortKlev leechIdx4 leechPar4 leechLev4 &&
  (shortHit shortKlev (12288 ^^^ 64) == false)

end CFSG.Monster.Tri.Leech
