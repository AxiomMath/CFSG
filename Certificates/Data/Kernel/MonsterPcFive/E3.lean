module

public import Certificates.Data.Kernel.MonsterPcFive.Model

public section

namespace CFSG.KC.MonPcFive

@[expose] def nthN : List Nat → Nat → Nat
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: l, k + 1 => nthN l k

@[expose] def repK : List Nat :=
  [1, 5, 25, 30, 35, 45, 130, 135, 150, 160, 175, 210, 225, 740, 765, 785, 805, 910, 1165,
    3245, 3565, 26090, 78145, 78165, 78166, 78167, 390625, 390635, 390880, 390881, 390884]

@[expose] def e3A : List Nat :=
  [1353963, 68135, 36612, 44218, 57836, 43386, 10446, 480, 19656, 3922, 44459, 35367, 9442,
    48787, 52909, 35775, 68769, 6119, 71266, 75297, 1283925, 1180011, 211901, 208510, 1428405,
    721084, 10435, 1096104, 1305642, 416345, 1404349]

@[expose] def e3B : List Nat :=
  [11492, 17142, 7023, 21151, 24160, 29167, 52272, 45154, 61897, 58536, 59962, 37065, 73546,
    13177, 1739, 38293, 14976, 70817, 2671, 55150, 604753, 526451, 1221432, 144717, 1135754,
    907571, 1, 1946334, 1270610, 1129420, 1775305]

@[expose] def indepV (t a b : V9) : Bool :=
  allBelow (fun i => allBelow (fun j => allBelow (fun l =>
    (i.beq 0 && j.beq 0 && l.beq 0) ||
      !(mulV (mulV (powV t i) (powV a j)) (powV b l)).isOne) 5) 5) 5

@[expose] def tripV (t a b : V9) : Bool :=
  (mulV t a).beq (mulV a t) && (mulV t b).beq (mulV b t) && (mulV a b).beq (mulV b a) &&
    ord5 t && ord5 a && ord5 b && indepV t a b

@[expose] def e3OK (lo n : Nat) : Bool :=
  allBelow (fun k => tripV (dec (nthN repK (lo + k))) (dec (nthN e3A (lo + k)))
    (dec (nthN e3B (lo + k)))) n

end CFSG.KC.MonPcFive

end
