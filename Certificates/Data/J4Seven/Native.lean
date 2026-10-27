module

public import CFSG.Sporadic.J4.QT2LocCntNative

public section

namespace CFSG.Quasithin.J4Seven

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

@[expose] def locM : Array (Array V2) := locMats ()

@[expose] def locTabsS : Array (Array V2) := locM.map frTable

@[expose] def x2R : Array V2 := locM[2]!

@[expose] def sevenR : Array V2 := powRows x2R 3

@[expose] def rep5S : V2 := pathVec (repPaths.getD 5 [])

@[expose] def orbS5 : VOrb := vorbit locTabsS rep5S 15180 15

@[expose] def fixedS (M : Array V2) (O : VOrb) : List V2 :=
  let T := frTable M
  (O.pts.filter fun v => (frApply T v).beq v).toList

@[expose] def sevenFix : List V2 :=
  [⟨0xa6061adfa188e404, 0x00003c96ae3b5b51⟩, ⟨0xc463e58a03e2bd2d, 0x000021b1b9f0f46d⟩,
    ⟨0x1936054e4c068920, 0x0000b286d80b6c66⟩, ⟨0x9cf39f7d899ce832, 0x0000602a295fd503⟩]

@[expose] def actX (c : Nat) : Nat := act 3 (act 3 (act 3 c))

@[expose] def actTab : Array Nat := ((List.range 2048).map actX).toArray

@[expose] def actMask (c : Nat) : Nat := actTab.getD c 0

@[expose] def actIter : Nat → Nat → Nat
  | 0, c => c
  | k + 1, c => actMask (actIter k c)

@[expose] def cntF (k : Nat) : Nat :=
  ((List.range 2048).filter fun c => (actIter (k * 3) c ^^^ actIter k c ^^^ c) == 0).length

@[expose] def cntFs (k : Nat) : Nat :=
  ((List.range 2048).filter fun c => (actIter (k * 3) c ^^^ actIter (k * 2) c ^^^ c) == 0).length

@[expose] def chkSeven : Bool :=
  eqRows (powRows sevenR 7) idRows && !eqRows sevenR idRows &&
    (sevenR.size == 112 && sevenR.all V2.wf) &&
    vorbOK locTabsS rep5S orbS5 15180 &&
    fixedS sevenR orbS5 == sevenFix && sevenFix.all V2.wf && rootV.wf &&
    sevenFix.all (fun v => !(v.beq rootV)) &&
    (List.range 4).all (fun i => (List.range 4).all fun j =>
      i == j || !((sevenFix.getD i rootV).beq (sevenFix.getD j rootV))) &&
    (List.range 2048).all (fun c => actMask c == actX c && decide (actMask c < 2048)) &&
    (List.range' 1 6).all fun k => cntF k != cntFs k

end CFSG.Quasithin.J4Seven
