module

public import CFSG.Sporadic.Schreier.LyCheckSylow

public section

namespace CFSG.Sporadic.LySchreier.Native

open CFSG.Sporadic.Ly.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.He.Native

set_option compiler.extract_closed false

@[expose] def r3eWordsN : List (List Int) :=
  [[12], [6, 6, -12, 8, 10, 9], [5, 5, 5, 9, 6, 10, -11], [6, -11],
    [-6, 5, -6, -6, 7, 6, 8, 10, 9, 12, 11, 12], [2, 12, 1, -8, 6, -11, -12]]

@[expose] def r3eHM (b4 : Mat) : Mat :=
  mulM 5 111 (mulM 5 111 (mulM 5 111 matA matB) matA) (mulM 5 111 b4 matA)

@[expose] def r3eGM (mh mf : Mat) : Mat :=
  mulM 5 111 (powM 5 111 (mulM 5 111 mh mf) 7) (powM 5 111 (mulM 5 111 matA mh) 4)

@[expose] def r3eP18 (mc md mg : Mat) : Mat :=
  powM 5 111 (mulM 5 111 (mulM 5 111 mc md) mg) 18

@[expose] def cWordM (cs : Array (Mat × Mat)) (w : List Int) : Mat :=
  evalWordM (fun i => (pairAt cs i).1) (fun i => (pairAt cs i).2) w

@[noinline, expose] def r3eChecks (b4 : Mat) (cs : Array (Mat × Mat)) (us pts : Array Mat) :
    Bool :=
  let mf := pts[113]!
  let mg := r3eGM (r3eHM b4) mf
  let mc := (pairAt cs 3).1
  mulM 5 111 (mulM 5 111 (mulM 5 111 us[2]! us[1]!) us[2]!) us[1]! == mf &&
    mulM 5 111 mf mf == idM 111 && diffMod5 mf (idM 111) && diffMod5 mf matA &&
    mulM 5 111 matA mf == mulM 5 111 mf matA && mulM 5 111 mg matA == mulM 5 111 mf mg &&
    r3eWordsN.all (fun w => let md := cWordM cs w; mulM 5 111 md mf == mulM 5 111 mf md) &&
    r3eP18 mc (idM 111) mg == idM 111 && diffMod5 (r3eP18 mc matA mg) (idM 111) &&
    diffMod5 (r3eP18 mc mf mg) (idM 111) && r3eP18 mc (mulM 5 111 matA mf) mg == idM 111

@[noinline, expose] def r3eWithGens (b4 : Mat) (cs : Array (Mat × Mat)) (us : Array Mat) :
    Bool :=
  r3eChecks b4 cs us (sylowBFS us 256).1

@[noinline, expose] def r3eWithStar (b4 : Mat) (cs : Array (Mat × Mat)) : Bool :=
  r3eWithGens b4 cs (sylowGens cs)

@[expose] def r3eCertificate (_ : Unit) : Bool :=
  let b4 := powM 5 111 matB 4
  r3eWithStar b4 (cStarArr b4)

end CFSG.Sporadic.LySchreier.Native
