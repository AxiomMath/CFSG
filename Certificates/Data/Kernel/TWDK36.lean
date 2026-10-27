module

public import Certificates.Data.Kernel.TWDK
public import Certificates.Data.TwoDepSmallN36

public section

namespace Certificates.TWDK36

open Certificates.DepASmall Certificates.TwoDepSmall Certificates.TwoDepSmallN Certificates.TWDK

set_option compiler.extract_closed false

abbrev KOut := List (Nat × List Nat) × List (Nat × List Nat) × List (Nat × Nat)

abbrev KE := Bool × Nat

@[expose] def kOut (o : KOut) : GGTWDOut := ⟨o.1, o.2.1, o.2.2⟩

@[expose] def kTestE (p N : Nat) (F : List GGDepANPair) (O : List KOut) (news : List GGDepANPair)
    (ws : List KWit) (e : KE) : Bool :=
  if e.1 then ggTWDOutOK p N news (kOut (O.getD e.2 ([], [], [])))
  else kTest p N F news (ws.getD e.2 kW0)

@[expose] def kSolC (p N pos code a b t : Nat) : List Nat :=
  if code = 0 then kVec p N pos 0 0 a b t else kVec p N pos (code - 1) ((p - 1) % p) a b t

@[expose] def kANC (p N pos code u : Nat) : List Nat :=
  if code = 0 then kAN p N pos 0 0 u else kAN p N pos (code - 1) ((p - 1) % p) u

@[expose] def kBond (p code : Nat) : Nat := if code = 0 then (p - 1) % p else 0

@[expose] def kA2All (p N pos code : Nat) : List (List Nat) :=
  (List.range p).flatMap fun a => (List.range p).flatMap fun b => (List.range p).map fun t =>
    kSolC p N pos code a b t

@[expose] def kA2Norm (p N pos code : Nat) : List (List Nat) :=
  (List.range p).map fun u => kANC p N pos code u

@[expose] def kOuterA (p N pos c : Nat) : List GGDepANPair :=
  (List.range p).flatMap fun a => (List.range p).flatMap fun b => (List.range p).flatMap fun t =>
    let h1 := kVec p N pos c ((p - 1) % p) a b t
    (List.range p).filterMap fun u =>
      let a1 := kAN p N pos c ((p - 1) % p) u
      if ggDepANDot p a1 h1 == 2 % p then some (h1, a1) else none

@[expose] def kInnerC (p N pos code : Nat) (as2 : List (List Nat)) (o : GGDepANPair) :
    List GGDepANPair :=
  (List.range p).flatMap fun a => (List.range p).flatMap fun b => (List.range p).flatMap fun t =>
    let h2 := kSolC p N pos code a b t
    if ggDepANDot p o.2 h2 == kBond p code then
      as2.filterMap fun a2 =>
        if ggDepANDot p a2 h2 == 2 % p && ggDepANDot p a2 o.1 == kBond p code then some (h2, a2)
        else none
    else []

@[expose] def kOuterOK (p N : Nat) (F : List GGDepANPair) (O : List KOut) (pos code : Nat)
    (as2 : List (List Nat)) (ws : List KWit) (os : List GGDepANPair)
    (ent : List (Nat × List KE)) : Bool :=
  kAll2 (fun (o : GGDepANPair) (e : Nat × List KE) =>
      if e.1 = 0 then kAll2 (fun c ce => kTestE p N F O [o, c] ws ce) (kInnerC p N pos code as2 o) e.2
      else kTest p N F [o] (ws.getD (e.1 - 1) kW0))
    os ent

abbrev KOneE := (Nat × Nat × Nat × Nat) × List KWit × List KE

abbrev KTwoE := (Nat × Nat × Nat) × List KWit × List (Nat × List KE) × List (Nat × List KE)

@[expose] def kOne (p N : Nat) (F : List GGDepANPair) (O : List KOut) (e : KOneE) : Bool :=
  kAll2 (fun c ce => kTestE p N F O [c] e.2.1 ce)
    (kCells1 p N e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2) e.2.2

@[expose] def kTwo (p N : Nat) (F : List GGDepANPair) (O : List KOut) (e : KTwoE) : Bool :=
  let pos := e.1.1
  let c := e.1.2.1
  let code := e.1.2.2
  kOuterOK p N F O pos code (kA2All p N pos code) e.2.1 (kOuterA p N pos c) e.2.2.1 &&
    kOuterOK p N F O pos code (kA2Norm p N pos code) e.2.1 (kOuter p N pos c) e.2.2.2

@[expose] def kOneAt (p N : Nat) (F : List GGDepANPair) (O : List KOut) (S : List KOneE)
    (i : Nat) : Bool :=
  match S[i]? with
  | some e => kOne p N F O e
  | none => false

@[expose] def kTwoAt (p N : Nat) (F : List GGDepANPair) (O : List KOut) (T : List KTwoE)
    (i : Nat) : Bool :=
  match T[i]? with
  | some e => kTwo p N F O e
  | none => false

@[expose] def kCover36 (N : Nat) (S : List KOneE) (T : List KTwoE) : Bool :=
  [0, 1].all fun pos => (List.range (N - 1)).all fun c =>
    ([1, 2].all fun mi => [1, 2].all fun ni =>
      !ggTWNPat1B N pos c mi ni || (S.map (·.1)).contains (pos, c, mi, ni)) &&
    ((none :: (List.range (N - 1)).map some).all fun c2 =>
      !ggTWNPat2B N pos c c2 || (T.map (·.1)).contains (pos, c, ggTWNCode c2))

end Certificates.TWDK36

end
