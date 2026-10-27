module

public import CFSG.Quasithin.H13.AS91Sec4TwoInputs

public section

namespace CFSG.Quasithin.H13.AS91.Two

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Enum CFSG.GF2Type.Smith1979.IdxFour
open CFSG.GF2Type.Smith1979.IdxFour.Orb

@[expose] def iList : List ℕ :=
  [0, 3, 12, 15, 192, 195, 204, 207, 820, 823, 824, 827, 1012, 1015, 1016, 1019, 1028, 1031,
    1032, 1035, 1220, 1223, 1224, 1227, 1840, 1843, 1852, 1855, 2032, 2035, 2044, 2047, 2052,
    2055, 2056, 2059, 2244, 2247, 2248, 2251, 2864, 2867, 2876, 2879, 3056, 3059, 3068, 3071,
    3072, 3075, 3084, 3087, 3264, 3267, 3276, 3279, 3892, 3895, 3896, 3899, 4084, 4087, 4088, 4091]

@[expose] def inIb (n : ℕ) : Bool := iList.contains n

@[expose] def zList : List ℕ := [0, 3, 192, 195]

@[expose] def inZb (n : ℕ) : Bool := zList.contains n

@[expose] def tWord : List ℕ := [0, 1, 2, 0, 2, 0]

@[expose] def tInvWord : List ℕ := [3, 5, 3, 5, 4, 3]

@[expose] def sel7 (L : List ℕ) : Array ℕ :=
  (L.foldl (fun (st : List ℕ × List ℕ) x =>
      if 7 ≤ st.2.length then st else
        let r := st.1.foldl (fun acc b => if acc ^^^ b < acc then acc ^^^ b else acc) x
        if r == 0 then st else
          ((r :: st.1).mergeSort (fun a b => decide (b ≤ a)), st.2 ++ [x]))
    ([], [])).2.toArray

@[expose] def iCountOK (_ : Unit := ()) : Bool := ((List.range 4096).filter inIb).length == 64

@[expose] def iWitOK1 (gs : List (Array ℕ)) (w : ℕ) : Bool :=
  inIb w ||
    (let L := orbitList gs w
     let vs := sel7 L
     vs.size == 7 && vs.all (fun v => L.contains v) && decide ((List.range 128).map (appN vs)).Nodup)

@[expose] def iWitOK (_ : Unit := ()) : Bool :=
  let gs := stab1Gens ()
  (List.range 4096).all (iWitOK1 gs)

@[expose] def iInterOK (_ : Unit := ()) : Bool :=
  let ti := wordRows nGensI tInvWord
  (List.range 4096).all (fun y => (inIb y && inIb (appN ti y)) == inZb y)

@[expose] def iOK43 (_ : Unit := ()) : Bool := iCountOK () && iWitOK () && iInterOK ()

end CFSG.Quasithin.H13.AS91.Two
