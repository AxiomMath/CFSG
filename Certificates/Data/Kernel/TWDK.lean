module

public import Certificates.Data.DepASmall
public import Certificates.Data.TwoDepSmall

public section

namespace Certificates.TWDK

open Certificates.DepASmall Certificates.TwoDepSmall

set_option compiler.extract_closed false

abbrev KWit := Nat × List Nat × Nat × List Nat

@[expose] def kW0 : KWit := (0, [], 0, [])

@[expose] def kFrame (p N : Nat) : List GGDepANPair :=
  (List.range (N - 1)).map fun i => (ggDepANH p N i, ggDepANA p N i)

@[expose] def kFrameOK (p N : Nat) (F : List GGDepANPair) : Bool := F == kFrame p N

@[expose] def kGen (N : Nat) (F news : List GGDepANPair) (g : Nat) : GGDepANPair :=
  if g + 1 < N then F.getD g ([], []) else news.getD (g + 1 - N) ([], [])

@[expose] def kWord (p N : Nat) (F news : List GGDepANPair) (q : GGDepANPair) (w : List Nat) :
    GGDepANPair :=
  w.foldr (fun g acc => ggDepANConj p acc (kGen N F news g)) q

@[expose] def kValid (G : Nat) (w : KWit) : Bool :=
  decide (w.1 < G) && decide (w.2.2.1 < G) && w.2.1.all (fun g => decide (g < G)) &&
    w.2.2.2.all fun g => decide (g < G)

@[expose] def kTest (p N : Nat) (F news : List GGDepANPair) (w : KWit) : Bool :=
  kValid (N - 1 + news.length) w &&
    ggDepANTestPair p (kWord p N F news (kGen N F news w.1) w.2.1)
      (kWord p N F news (kGen N F news w.2.2.1) w.2.2.2)

@[expose] def kAll2 {α β : Type} (t : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | c :: cs, i :: is => t c i && kAll2 t cs is
  | _, _ => false

@[expose] def kChain (N pos j : Nat) : Bool :=
  if pos = 0 then decide (1 ≤ j) && decide (j + 2 ≤ N) else decide (j + 3 ≤ N)

@[expose] def kVec (p N pos c0 n a b t : Nat) : List Nat := (List.range N).map fun j =>
  if j + 1 = N then t % p
  else if kChain N pos j then (if c0 < j then (b + (p - n % p)) % p else b % p)
  else a % p

@[expose] def kAN (p N pos c0 m u : Nat) : List Nat :=
  if pos = 0 then kVec p N pos c0 m 0 u 1 else kVec p N pos c0 m u 0 1

@[expose] def kCells1 (p N pos c0 mi ni : Nat) : List GGDepANPair :=
  (List.range p).flatMap fun a => (List.range p).flatMap fun b => (List.range p).flatMap fun t =>
    let ha := kVec p N pos c0 ((p - ni % p) % p) a b t
    (List.range p).filterMap fun u =>
      let aa := kAN p N pos c0 ((p - mi % p) % p) u
      if ggDepANDot p aa ha == 2 % p then some (ha, aa) else none

@[expose] def kOuter (p N pos c : Nat) : List GGDepANPair :=
  (List.range p).flatMap fun a => (List.range p).flatMap fun b => (List.range p).flatMap fun t =>
    let h1 := kVec p N pos c ((p - 1) % p) a b t
    (List.range p).flatMap fun a' => (List.range p).filterMap fun b' =>
      let a1 := kVec p N pos c ((p - 1) % p) a' b' 0
      if ggDepANDot p a1 h1 == 2 % p then some (h1, a1) else none

@[expose] def kInner (p N pos : Nat) (o : GGDepANPair) : List GGDepANPair :=
  (List.range p).flatMap fun a => (List.range p).flatMap fun b => (List.range p).flatMap fun t =>
    let h2 := kVec p N pos 0 0 a b t
    if ggDepANDot p o.2 h2 == (p - 1) % p then
      (List.range p).filterMap fun u =>
        let a2 := kAN p N pos 0 0 u
        if ggDepANDot p a2 h2 == 2 % p && ggDepANDot p a2 o.1 == (p - 1) % p then some (h2, a2)
        else none
    else []

@[expose] def kSingle (p N : Nat) (F : List GGDepANPair) (key : Nat × Nat × Nat × Nat)
    (wits : List KWit) (idx : List Nat) : Bool :=
  kAll2 (fun c i => kTest p N F [c] (wits.getD i kW0))
    (kCells1 p N key.1 key.2.1 key.2.2.1 key.2.2.2) idx

@[expose] def kRes (p N : Nat) (F : List GGDepANPair) (key : Nat × Nat) (sw ra : List KWit)
    (ent : List (Nat × List Nat)) : Bool :=
  kAll2 (fun (o : GGDepANPair) (e : Nat × List Nat) =>
      if e.1 = 0 then kAll2 (fun c i => kTest p N F [o, c] (ra.getD i kW0)) (kInner p N key.1 o) e.2
      else kTest p N F [o] (sw.getD (e.1 - 1) kW0))
    (kOuter p N key.1 key.2) ent

abbrev KSingleE := (Nat × Nat × Nat × Nat) × List KWit × List Nat

abbrev KResE := (Nat × Nat) × List KWit × List KWit × List (Nat × List Nat)

@[expose] def kSingleAt (p N : Nat) (F : List GGDepANPair) (S : List KSingleE) (i : Nat) : Bool :=
  match S[i]? with
  | some e => kSingle p N F e.1 e.2.1 e.2.2
  | none => false

@[expose] def kResAt (p N : Nat) (F : List GGDepANPair) (R : List KResE) (i : Nat) : Bool :=
  match R[i]? with
  | some e => kRes p N F e.1 e.2.1 e.2.2.1 e.2.2.2
  | none => false

@[expose] def kCover (N : Nat) (S : List KSingleE) (R : List KResE) : Bool :=
  [0, 1].all fun pos => (List.range (N - 1)).all fun c0 =>
    ([1, 2].all fun mi => [1, 2].all fun ni =>
      !ggTWNPat1B N pos c0 mi ni || (S.map (·.1)).contains (pos, c0, mi, ni)) &&
    (!ggTWNPat2B N pos c0 none || (R.map (·.1)).contains (pos, c0))

end Certificates.TWDK

end
