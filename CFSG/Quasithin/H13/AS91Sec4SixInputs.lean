module

public import CFSG.Quasithin.H13.AS91Sec4FiveInputs

public section

namespace CFSG.Quasithin.H13.AS91.Two

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Enum CFSG.GF2Type.Smith1979.IdxFour

@[expose] def g13Words : List (List ℕ) :=
  [[2, 1, 2, 4, 5, 5, 3, 5, 1, 2, 4, 5, 5, 5, 5, 4, 4, 5, 5, 1, 5, 4, 2, 1],
    [4, 5, 1, 2, 4, 2, 2, 1, 5, 3, 4, 5, 5, 3, 1, 5, 5, 4, 2, 1, 5, 4]]

@[expose] def g13Gens (_ : Unit := ()) : List (Array ℕ) := g13Words.map (wordRows nGensI)

@[expose] def ebRows : List (Array ℕ) :=
  [#[1, 2, 2564, 308, 56, 284, 64, 128, 2856, 3076, 3584, 1540],
    #[3898, 3897, 199, 200, 208, 224, 444, 380, 259, 707, 1219, 2243],
    #[1030, 1029, 2567, 308, 251, 284, 1424, 1360, 3048, 3076, 3587, 1540],
    #[41, 42, 2604, 1307, 2576, 1331, 2624, 2688, 296, 980, 3624, 2516]]

@[expose] def w1OK46 (_ : Unit := ()) : Bool :=
  w1List.all (fun a => w1List.all fun b => w1List.contains (a ^^^ b)) &&
    w1List.all fun a => !q0b a

@[expose] def ebOK46 (_ : Unit := ()) : Bool :=
  let St := enumGrp (stab1Gens ())
  let Eb := enumGrp ebRows
  let Ebs := Std.HashSet.ofList Eb
  let Ps := Std.HashSet.ofList (enumGrp pRows)
  let m := w1Mask ()
  gensOKb ebRows && ebRows.all (fun e => w1List.all fun c => appN e c == c) &&
    ebRows.all (fun e => Ps.contains e) &&
    ebRows.all (fun e => mulR e omegaRows == mulR omegaRows e) &&
    Eb.contains idR && closedCheck ebRows Eb && Eb.dedup.length == 16 &&
    St.all (fun x => !(w1List.all fun c => appN x c == c) || Ebs.contains x) &&
    (g13Gens ()).all (fun g => imgMask g m == m) &&
    Eb.all (fun x => Eb.all fun y => mulR x y == mulR y x) && Eb.all (fun x => mulR x x == idR)

@[expose] def ebOrbit (_ : Unit := ()) : List (Array ℕ) :=
  let fs := (g13Gens ()).map fun g => let gi := Viol.invR g; fun x => mulR g (mulR x gi)
  let e₀ := ebRows.headD idR
  bfsClosure (fun x : Array ℕ => x) fs 100 [e₀] ((∅ : Std.HashSet (Array ℕ)).insert e₀) []

@[expose] def transOK46 (_ : Unit := ()) : Bool :=
  let O := Std.HashSet.ofList (ebOrbit ())
  gensOKb (g13Gens ()) &&
    (enumGrp ebRows).all fun x => x == idR || O.contains x

@[expose] def pList (_ : Unit := ()) : List (Array ℕ) := (enumGrp pRows).dedup

@[expose] def fixMask (r : Array ℕ) : ℕ := maskOf ((List.range 4096).filter fun v => appN r v == v)

@[expose] def fullMask (_ : Unit := ()) : ℕ := maskOf (List.range 4096)

@[expose] def mkey (F : ℕ) : ℕ × ℕ := (F % 18446744073709551557, F)

@[expose] def fixPairs (_ : Unit := ()) : List (Array ℕ × ℕ) :=
  (pList ()).map fun r => (r, fixMask r)

@[expose] def fixClosure (_ : Unit := ()) : List ℕ :=
  let fs := (fixPairs ()).map fun rf F => F &&& rf.2
  let f := fullMask ()
  bfsClosure mkey fs 100 [f] ((∅ : Std.HashSet (ℕ × ℕ)).insert (mkey f)) []

@[expose] def popc (F : ℕ) : ℕ := ((List.range 4096).filter F.testBit).length

@[expose] def jF (fms : List (Array ℕ × ℕ)) (m F : ℕ) : Bool :=
  let C := (fms.filter fun rf => F &&& rf.2 == F).map Prod.fst
  let n := C.length * min 64 (popc F)
  if F == m then C.length == 16 else
    n ≤ 512 || (n ≤ 1024 && C.length == 64 && C.any fun a => C.any fun b => mulR a b != mulR b a)

@[expose] def jOK46 (_ : Unit := ()) : Bool :=
  let fms := fixPairs ()
  let L := fixClosure ()
  let Ls := Std.HashSet.ofList (L.map mkey)
  let m := w1Mask ()
  L.all (fun F => fms.all fun rf => Ls.contains (mkey (F &&& rf.2))) && L.all (jF fms m)

@[expose] def ok46 (_ : Unit := ()) : Bool := w1OK46 () && ebOK46 () && transOK46 () && jOK46 ()

end CFSG.Quasithin.H13.AS91.Two
