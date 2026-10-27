module

public import Certificates.Data.Kernel.TWLK

public section

namespace Certificates.TWLKF

open Certificates.DepASmall Certificates.TwoDepSmall Certificates.TWLK

set_option compiler.extract_closed false

@[expose] def kRTF (_ : Nat) (_ : List GGDepANPair) (_ _ : Nat) : Bool := false

@[expose] def kSolAX (p N pos : Nat) (tgt : Nat → Nat) (e : Nat) : List (List Nat) :=
  (kSolA p N pos tgt).filter fun v => ggDepANDot p v (ggTWNX N) == e

@[expose] def kCells1N (p N pos c0 mi ni : Nat) : List (List GGDepANPair) :=
  (kSolH p N pos (kTgt1 p c0 ni)).flatMap fun ha => (kSolAX p N pos (kTgt1 p c0 mi) 1).filterMap
    fun aa => if ggDepANDot p aa ha == 2 % p then some [(ha, aa)] else none

@[expose] def kCells2N (p N pos c : Nat) (c2 : Option Nat) : List (List GGDepANPair) :=
  let X := ggTWNX N
  let Z := ggTWNZ p N pos
  let nb := match c2 with | none => (p - 1) % p | some _ => 0
  (kSolH p N pos (kTgt1 p c 1)).flatMap fun h1 => (kSolA p N pos (kTgt1 p c 1)).flatMap fun a1 =>
    if ggDepANDot p a1 h1 == 2 % p then
      let e1 := ggDepANDot p a1 X
      (kSolH p N pos (ggTWNTgt2 p c2)).flatMap fun h2 =>
        if ggDepANDot p a1 h2 == nb then
          (kSolAX p N pos (ggTWNTgt2 p c2) 1 ++
              (if e1 == 1 then kSolAX p N pos (ggTWNTgt2 p c2) 0 else [])).filterMap fun a2 =>
            if ggDepANDot p a2 h2 == 2 % p && ggDepANDot p a2 h1 == nb &&
                (e1 * ggDepANDot p a2 Z) % p == (ggDepANDot p a1 Z * ggDepANDot p a2 X) % p then
              some [(h1, a1), (h2, a2)]
            else none
        else []
    else []

@[expose] def kPat1N (p N : Nat) (RF : List (List Nat)) (e : KPat1) : Bool :=
  kAll2 (kCell p N e.1.1 RF kRTF e.2.1) (kCells1N p N e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2) e.2.2

@[expose] def kPat2N (p N : Nat) (RF : List (List Nat)) (e : KPat2) : Bool :=
  kAll2 (kCell p N e.1.1 RF kRTF e.2.1) (kCells2N p N e.1.1 e.1.2.1 (kDecode e.1.2.2)) e.2.2

@[expose] def kPat1NAt (p N : Nat) (RF : List (List Nat)) (S : List KPat1) (i : Nat) : Bool :=
  match S[i]? with
  | some e => kPat1N p N RF e
  | none => false

@[expose] def kPat2NAt (p N : Nat) (RF : List (List Nat)) (T : List KPat2) (i : Nat) : Bool :=
  match T[i]? with
  | some e => kPat2N p N RF e
  | none => false

end Certificates.TWLKF

end
