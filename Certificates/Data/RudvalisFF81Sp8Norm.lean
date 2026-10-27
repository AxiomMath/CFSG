module

public import Certificates.Data.RudvalisFF81Sp8Torus

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.G2U

@[expose] def n0Gens : List (List ℕ) :=
  [[16, 2, 4, 8, 17, 32, 64, 128], [16, 2, 4, 8, 1, 32, 64, 128], [2, 1, 4, 8, 32, 16, 64, 128],
    [2, 4, 8, 1, 32, 64, 128, 16]]

@[expose] def n0Chk899104 : Bool :=
  let E := tabS e0Gens 81
  let mE := indexMap E
  let T := tabS n0Gens 31104
  tabOK n0Gens T 31104 &&
    (n0Gens.all fun g => e0Gens.all fun z =>
      found E mE (conjS g z) && mulS g z == mulS (conjS g z) g) &&
    e0Gens.all fun z => found T (indexMap T) z

@[expose] def fixChk899104 : Bool :=
  fixS one8 == 256 && fixS zzS == 16 && fixS z012S == 4 && fixS z0123S == 1 &&
    e0Gens.all (fun z => fixS z == 64) && commS tS z012S && commS tS z0123S

@[expose] def clsChk899104 : Bool :=
  let E := tabS e0Gens 81
  let T := tabS n0Gens 31104
  let I := T.map invS
  let e2 := mulS z3S z3S
  let m1 := cmapS T I z3S
  let m2 := cmapS T I e2
  let m3 := cmapS T I zzS
  let m4 := cmapS T I z012S
  let m5 := cmapS T I z0123S
  allCheck (fun x => x == one8 ||
    (fixS x == 64 && l1S.contains x && (cfoundS T m1 z3S x || cfoundS T m2 e2 x)) ||
    (fixS x == 16 && cfoundS T m3 zzS x) || (fixS x == 4 && cfoundS T m4 z012S x) ||
    (fixS x == 1 && cfoundS T m5 z0123S x)) E

@[expose] def normChk899104 : Bool :=
  let T := tabS n0Gens 31104
  let I := T.map invS
  let m : Std.HashMap (List (List ℕ)) ℕ := (List.range T.size).foldl (fun m t =>
    m.insert (e0Gens.map fun z => mulS (mulS (T.getD t []) z) (I.getD t [])) t) {}
  (List.range 8).all fun a => (List.range 8).all fun b => (List.range 8).all fun c =>
    (List.range 8).all fun d =>
      !(decide [a / 2, b / 2, c / 2, d / 2].Nodup) ||
        match m.get? [l1S.getD a [], l1S.getD b [], l1S.getD c [], l1S.getD d []] with
        | some t => decide (t < T.size) &&
            mulS (T.getD t []) z0S == mulS (l1S.getD a []) (T.getD t []) &&
            mulS (T.getD t []) z1S == mulS (l1S.getD b []) (T.getD t []) &&
            mulS (T.getD t []) z2S == mulS (l1S.getD c []) (T.getD t []) &&
            mulS (T.getD t []) z3S == mulS (l1S.getD d []) (T.getD t [])
        | none => false

@[expose] def prodChk899104 : Bool :=
  let T := tabS n0Gens 31104
  let m := cmapS T (T.map invS) zzS
  (List.range 8).all fun a => (List.range 8).all fun b =>
    a / 2 == b / 2 || cfoundS T m zzS (mulS (l1S.getD a []) (l1S.getD b []))

end CFSG.RankThree.PartTwo.Sec21.FF81.Sp8
