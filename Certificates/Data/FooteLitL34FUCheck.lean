module

public import Certificates.Data.GrSLitL34FactsRealBCheck

public section

namespace CFSG.ComponentClassification.TBLit.L34FU

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real

@[expose] def pow4X (x : MElt) : MElt := mulM (mulM x x) (mulM x x)

@[expose] def orb4 : Array Tab := (orbitBFS 42 gTabs (gTabs.map (invTab 42)) r₄T 1963).tabs

@[expose] def candTab (t i : ℕ) : Tab := comp 42 (wordTab (tg t)) (repTab i)

@[expose] def candOK (t i : ℕ) : Bool :=
  comp 42 (candTab t i) r₂T == comp 42 r₂T (candTab t i) &&
    comp 42 (candTab t i) (candTab t i) == idTab 42 && orb4.contains (candTab t i)

@[expose] def witnessOK (t i : ℕ) : Bool :=
  allM.any fun x => betaRepM 1 x == x && pow4X (mulM x (betaYM t i x)) == (0, 2, 0)

@[expose] def sixteenOK : Bool :=
  allBelow 64 fun t => allBelow 36 fun i => !candOK t i || witnessOK t i

@[expose] def pow8T (g : Tab) : Tab :=
  let g2 := comp 42 g g
  let g4 := comp 42 g2 g2
  comp 42 g4 g4

@[expose] def noSixteenOK : Bool :=
  (enumBFS 42 gTabs 241920).tabs.all fun g =>
    !(comp 42 (pow8T g) (pow8T g) == idTab 42) || pow8T g == idTab 42

@[expose] def g4r4OK : Bool := comp 42 g₄T r₄T == comp 42 r₄T g₄T

@[noinline, expose] def l34fuSixteenOK : Bool := sixteenOK && noSixteenOK && g4r4OK

end CFSG.ComponentClassification.TBLit.L34FU
