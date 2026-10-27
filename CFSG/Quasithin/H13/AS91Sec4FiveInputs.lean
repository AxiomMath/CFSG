module

public import CFSG.Quasithin.H13.AS91Sec4ThreeInputs

public section

namespace CFSG.Quasithin.H13.AS91.Two

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Enum CFSG.GF2Type.Smith1979.IdxFour

@[expose] def w1List : List ℕ :=
  [0, 3, 40, 43, 192, 195, 232, 235, 276, 279, 316, 319, 468, 471, 508, 511,
    1028, 1031, 1068, 1071, 1220, 1223, 1260, 1263, 1296, 1299, 1336, 1339, 1488, 1491, 1528, 1531,
    2560, 2563, 2600, 2603, 2752, 2755, 2792, 2795, 2836, 2839, 2876, 2879, 3028, 3031, 3068, 3071,
    3588, 3591, 3628, 3631, 3780, 3783, 3820, 3823, 3856, 3859, 3896, 3899, 4048, 4051, 4088, 4091]

@[expose] def pRows : List (Array ℕ) :=
  [#[3073, 3074, 3080, 3076, 3040, 2000, 113, 178, 568, 308, 2063, 1039],
    #[1, 2, 2564, 308, 56, 284, 64, 128, 2856, 3076, 3584, 1540],
    #[1269, 1270, 244, 3320, 548, 727, 2451, 2387, 3523, 755, 2824, 1803],
    #[1841, 1842, 3272, 3268, 3043, 1811, 3181, 3246, 571, 311, 2252, 1231]]

@[expose] def maskOf (L : List ℕ) : ℕ := L.foldl (fun acc x => acc ||| 1 <<< x) 0

@[expose] def w1Mask (_ : Unit := ()) : ℕ := maskOf w1List

@[expose] def imgMask (g : Array ℕ) (m : ℕ) : ℕ :=
  (List.range 4096).foldl (fun acc x => if m.testBit x then acc ||| 1 <<< appN g x else acc) 0

@[expose] def w1Orbit (_ : Unit := ()) : List ℕ :=
  let m := w1Mask ()
  bfsClosure (fun x : ℕ => x) (nGensI.map imgMask) 100 [m] ((∅ : Std.HashSet ℕ).insert m) []

@[expose] def orbitOK45 (_ : Unit := ()) : Bool :=
  let L := w1Orbit ()
  L.length == 77 && decide L.Nodup && L.all (fun m => nGensI.all fun g => L.contains (imgMask g m))

@[expose] def pOK45 (_ : Unit := ()) : Bool :=
  let X := Std.HashSet.ofList (enumGrp (stab1Gens ()))
  let P := enumGrp pRows
  let m := w1Mask ()
  gensOKb pRows && pRows.all (fun p => X.contains p) &&
    P.contains idR && closedCheck pRows P && P.dedup.length == 256 &&
    (List.range 4096).all (fun n => (pRows.all fun g => appN g n == n) == (n == 0 || n == 3)) &&
    pRows.all (fun g => zList.all fun n => zList.contains (appN g n)) &&
    pRows.all (fun g => imgMask g m == m) && imgMask omegaRows m == m

@[expose] def ok45 (_ : Unit := ()) : Bool := orbitOK45 () && pOK45 ()

end CFSG.Quasithin.H13.AS91.Two
