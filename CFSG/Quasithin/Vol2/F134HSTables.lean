module

public import CFSG.Quasithin.Vol2.F134HSData
public import CFSG.Quasithin.Vol2.F134HSBridge

public section

namespace CFSG.Quasithin.F134

@[expose] def hsLetB : ℕ := ofDigs (2 ^ 400) (hsLetterR.map (ofDigs (2 ^ 160)))

@[expose] def hsLet (c : ℕ) : ℕ := digW 400 hsLetB c

@[expose] def hsTelB : ℕ := ofDigs (2 ^ 400) (hsTelR.map (ofDigs (2 ^ 160)))

@[expose] def hsTel (i : ℕ) : ℕ := digW 400 hsTelB i

@[expose] def hsTGB : ℕ := ofDigs (2 ^ 400) (hsTGenR.map (ofDigs (2 ^ 160)))

@[expose] def hsTG (k : ℕ) : ℕ := digW 400 hsTGB k

@[expose] def hsDB : ℕ := ofDigs (2 ^ 400) (hsDR.map (ofDigs (2 ^ 160)))

@[expose] def hsD (j : ℕ) : ℕ := digW 400 hsDB j

@[expose] def hsNxtB : ℕ := ofDigs (2 ^ 9) hsNxtL

@[expose] def hsNxt (i : ℕ) : ℕ := digW 9 hsNxtB i

@[expose] def hsParB : ℕ := ofDigs (2 ^ 11) hsParL

@[expose] def hsPar (i : ℕ) : ℕ := digW 11 hsParB i

@[expose] def hsBadB : ℕ := ofDigs (2 ^ 18) hsBadL

@[expose] def hsBad (j : ℕ) : ℕ := digW 18 hsBadB j

@[expose] def hsCosB (j : ℕ) : ℕ := ofDigs (2 ^ 10) (hsCosRows.getD (j - 1) [])

@[expose] def hsCos (j i : ℕ) : ℕ := digW 10 (hsCosB j) i

@[expose] noncomputable def hsLetE (c : ℕ) : GL (Fin 20) (ZMod 2) :=
  if c = 0 then hsUA else hsUB ^ c

@[expose] noncomputable def hsWord : List ℕ → GL (Fin 20) (ZMod 2)
  | [] => 1
  | c :: w => hsLetE c * hsWord w

@[expose] def hsWordC : List ℕ → ℕ
  | [] => hsOneC
  | c :: w => mulX20 (hsLet c) (hsWordC w)

@[expose] def hsGOneEB : ℕ := ofDigs (2 ^ 9) hsGOneE

@[expose] def hsGOneEAt (p : ℕ) : ℕ := digW 9 hsGOneEB p

@[expose] def hsGOnePB : ℕ := ofDigs (2 ^ 11) hsGOneP

@[expose] def hsGOnePAt (p : ℕ) : ℕ := digW 11 hsGOnePB p

@[expose] def hsGOneQB : ℕ := ofDigs (2 ^ 11) hsGOneQ

@[expose] def hsGOneQAt (i : ℕ) : ℕ := digW 11 hsGOneQB i

@[expose] def hsGOneDecB : ℕ := ofDigs (2 ^ 27) hsGOneDec

@[expose] def hsGOneDecAt (e : ℕ) : ℕ := digW 27 hsGOneDecB e

@[expose] def hsGTwoEB : ℕ := ofDigs (2 ^ 9) hsGTwoE

@[expose] def hsGTwoEAt (p : ℕ) : ℕ := digW 9 hsGTwoEB p

@[expose] def hsGTwoPB : ℕ := ofDigs (2 ^ 11) hsGTwoP

@[expose] def hsGTwoPAt (p : ℕ) : ℕ := digW 11 hsGTwoPB p

@[expose] def hsGTwoQB : ℕ := ofDigs (2 ^ 11) hsGTwoQ

@[expose] def hsGTwoQAt (i : ℕ) : ℕ := digW 11 hsGTwoQB i

@[expose] def hsGTwoDecB : ℕ := ofDigs (2 ^ 27) hsGTwoDec

@[expose] def hsGTwoDecAt (e : ℕ) : ℕ := digW 27 hsGTwoDecB e

@[expose] def hsBWLet (l : ℕ) : ℕ := if l < 3 then hsTG l else if l = 3 then hsD 1 else hsD 251

@[expose] def hsBWC : List ℕ → ℕ
  | [] => hsOneC
  | l :: w => mulX20 (hsBWLet l) (hsBWC w)

end CFSG.Quasithin.F134
