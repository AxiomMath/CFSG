module

public import CFSG.Quasithin.H13.AS91Sec4SixInputs

public section

namespace CFSG.Quasithin.H13.AS91.Two

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Enum CFSG.GF2Type.Smith1979.IdxFour

@[expose] def aRows48 : Array ℕ := #[1034, 1033, 4, 11, 211, 32, 1680, 1616, 256, 704, 1027, 2048]

@[expose] def bRows48 : Array ℕ := #[293, 294, 3800, 2344, 2352, 1799, 2116, 2180, 2299, 804, 1316, 1756]

@[expose] def cRows48 : Array ℕ := #[822, 821, 3275, 3268, 2851, 1811, 3514, 3449, 760, 311, 2255, 1231]

@[expose] def sGens48 : List (Array ℕ) := [aRows48, bRows48, cRows48]

@[expose] def sWord48 : List ℕ := [3, 4, 3, 4, 5, 3, 2, 1, 0, 1, 1, 0, 1, 0, 1]

@[expose] def sWordInv48 : List ℕ := [4, 3, 4, 3, 4, 4, 3, 4, 5, 0, 2, 1, 0, 1, 0]

@[expose] def sRows48 (_ : Unit := ()) : Array ℕ := wordRows nGensI sWord48

@[expose] def sInvRows48 (_ : Unit := ()) : Array ℕ := wordRows nGensI sWordInv48

@[expose] def coreList48 (_ : Unit := ()) : List (Array ℕ) :=
  let P := Std.HashSet.ofList (enumGrp pRows)
  let s := sRows48 ()
  let si := sInvRows48 ()
  (enumGrp pRows).filter fun r => P.contains (mulR (mulR si r) s)

@[expose] def uList48 : List ℕ :=
  [0, 73, 144, 217, 292, 365, 436, 509, 513, 584, 657, 728, 805, 876, 949, 1020,
    1042, 1115, 1154, 1227, 1334, 1407, 1446, 1519, 1555, 1626, 1667, 1738, 1847, 1918, 1959, 2030,
    2052, 2125, 2196, 2269, 2336, 2409, 2480, 2553, 2565, 2636, 2709, 2780, 2849, 2920, 2993, 3064,
    3094, 3167, 3206, 3279, 3378, 3451, 3490, 3563, 3607, 3678, 3719, 3790, 3891, 3962, 4003, 4074]

@[expose] def cjA48 : List ℕ × List ℕ × Array ℕ :=
  ([0, 3, 0, 1, 0, 3, 0, 1, 0], [2, 3, 2, 1, 2, 3, 2, 1, 2],
    #[3898, 3897, 199, 200, 208, 224, 444, 380, 259, 707, 1219, 2243])

@[expose] def cjB48 : List ℕ × List ℕ × Array ℕ :=
  ([0], [2],
    #[3858, 3857, 239, 1255, 2808, 1231, 3004, 2940, 2819, 3347, 1259, 1811])

@[expose] def cjAB48 : List ℕ × List ℕ × Array ℕ :=
  ([0, 1, 0, 1, 1, 0, 3, 0, 1], [3, 2, 1, 2, 3, 3, 2, 3, 2],
    #[3898, 3897, 199, 200, 208, 224, 444, 380, 259, 707, 1219, 2243])

@[expose] def cjC48 : List ℕ × List ℕ × Array ℕ :=
  ([], [],
    #[822, 821, 3275, 3268, 2851, 1811, 3514, 3449, 760, 311, 2255, 1231])

@[expose] def cjAC48 : List ℕ × List ℕ × Array ℕ :=
  ([], [],
    #[1854, 1853, 3275, 3271, 3043, 1811, 4002, 3937, 760, 500, 2252, 1231])

@[expose] def cjBC48 : List ℕ × List ℕ × Array ℕ :=
  ([4], [1],
    #[1854, 1853, 3275, 3271, 3043, 1811, 4002, 3937, 760, 500, 2252, 1231])

@[expose] def conjOK (gs : List (Array ℕ)) (d : List ℕ × List ℕ × Array ℕ) (t : Array ℕ) : Bool :=
  d.1.all (· < gs.length) && d.2.1.all (· < gs.length) &&
    mulR (wordRows gs d.1) (wordRows gs d.2.1) == idR &&
    mulR (mulR (wordRows gs d.1) d.2.2) (wordRows gs d.2.1) == t

@[expose] def sOK48 (_ : Unit := ()) : Bool :=
  let P := Std.HashSet.ofList (enumGrp pRows)
  let Eb := Std.HashSet.ofList (enumGrp ebRows)
  let Sl := enumGrp sGens48
  gensOKb sGens48 && sGens48.all (fun g => P.contains g) && Sl.contains idR &&
    closedCheck sGens48 Sl && Sl.dedup.length == 16 && Sl.all (fun x => x == idR || !Eb.contains x)

@[expose] def coreOK48 (_ : Unit := ()) : Bool :=
  sWord48.all (· < 6) && sWordInv48.all (· < 6) && mulR (sRows48 ()) (sInvRows48 ()) == idR &&
    appN (sRows48 ()) 3 == 3 && (coreList48 ()).dedup.length == 32

@[expose] def uOK48 (_ : Unit := ()) : Bool :=
  let U := Std.HashSet.ofList uList48
  uList48.dedup.length == 64 && uList48.all (· < 4096) && uList48.contains 0 &&
    uList48.all (fun x => uList48.all fun y => U.contains (x ^^^ y)) &&
    uList48.all (fun u => !q0b u) && uList48.all (fun u => U.contains (appN omegaRows u)) &&
    sGens48.all (fun g => uList48.all fun u => U.contains (appN g u)) &&
    uList48.all (fun u => u == 0 || !w1List.contains u)

@[expose] def cjOK48 (_ : Unit := ()) : Bool :=
  let Eb := Std.HashSet.ofList (enumGrp ebRows)
  let C := Std.HashSet.ofList (coreList48 ())
  let ab := mulR aRows48 bRows48
  ebRows.all (fun g => mulR g omegaRows == mulR omegaRows g) &&
    conjOK gamGensI cjA48 aRows48 && Eb.contains cjA48.2.2 &&
    conjOK gamGensI cjB48 bRows48 && Eb.contains cjB48.2.2 &&
    conjOK gamGensI cjAB48 (mulR ab ab) && Eb.contains cjAB48.2.2 &&
    conjOK nGensI cjC48 cRows48 && C.contains cjC48.2.2 && cjC48.2.2 != idR &&
    conjOK nGensI cjAC48 (mulR aRows48 cRows48) && C.contains cjAC48.2.2 && cjAC48.2.2 != idR &&
    conjOK nGensI cjBC48 (mulR bRows48 cRows48) && C.contains cjBC48.2.2 && cjBC48.2.2 != idR &&
    [cRows48, mulR aRows48 cRows48, mulR bRows48 cRows48].all fun t =>
      mulR t t == idR && mulR (mulR t omegaRows) t == mulR omegaRows omegaRows

@[expose] def splitOK48 (_ : Unit := ()) : Bool := sOK48 () && coreOK48 () && uOK48 () && cjOK48 ()

end CFSG.Quasithin.H13.AS91.Two
