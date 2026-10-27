module

public import Certificates.Data.TwoDepSmallLow

public section

namespace Certificates.TWLK

open Certificates.DepASmall Certificates.TwoDepSmall Certificates.TwoDepSmallLow

set_option compiler.extract_closed false

abbrev KKill := Nat × Nat × List Nat × Nat × List Nat

@[expose] def kK0 : KKill := (0, 0, [], 0, [])

@[expose] def kKill (k : KKill) : GGTWNKill :=
  if k.1 = 0 then .tv ⟨k.2.1, k.2.2.1, k.2.2.2.1, k.2.2.2.2⟩
  else .line ⟨k.2.1, k.2.2.1, k.2.2.2.1, k.2.2.2.2⟩

@[expose] def kRootsOK (p N : Nat) (RF : List (List Nat)) : Bool :=
  RF == ggTWNRoots p N && ggTWNRootsOK p N RF

@[expose] def kAll2 {α β : Type} (t : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | c :: cs, i :: is => t c i && kAll2 t cs is
  | _, _ => false

@[expose] def kChainH (p : Nat) (tgt : Nat → Nat) : Nat → Nat → Nat → Nat → List Nat
  | 0, _, _, _ => []
  | n + 1, c, a, b =>
    let v := (2 * b + (p - a % p) + (p - tgt c % p)) % p
    v :: kChainH p tgt n (c + 1) b v

@[expose] def kCandH (p N pos : Nat) (tgt : Nat → Nat) : List (List Nat) :=
  (List.range p).flatMap fun s => (List.range p).map fun t =>
    if pos = 0 then s :: (kChainH p tgt (N - 3) 1 0 s ++ [t])
    else
      let v0 := (p - tgt 0 % p) % p
      v0 :: (kChainH p tgt (N - 4) 1 0 v0 ++ [s, t])

@[expose] def kCandA (p N pos : Nat) (tgt : Nat → Nat) : List (List Nat) :=
  if pos = 0 then
    (List.range p).flatMap fun s => (List.range p).map fun t =>
      (List.range (N - 3)).map (fun j => tgt (j + 1) % p) ++ [s, t]
  else
    (List.range p).flatMap fun s => (List.range p).flatMap fun u => (List.range p).map fun t =>
      (List.range (N - 4)).map (fun j => tgt (j + 1) % p) ++ [s, u, t]

@[expose] def kOkH (p N pos : Nat) (tgt : Nat → Nat) (v : List Nat) : Bool :=
  (List.range (N - 1)).all fun c => !ggTWNInJ N pos c || ggDepANDot p (ggTWNA p N c) v == tgt c % p

@[expose] def kOkA (p N pos : Nat) (tgt : Nat → Nat) (v : List Nat) : Bool :=
  (List.range (N - 1)).all fun c => !ggTWNInJ N pos c || ggDepANDot p v (ggTWNH p N c) == tgt c % p

@[expose] def kSolH (p N pos : Nat) (tgt : Nat → Nat) : List (List Nat) :=
  (kCandH p N pos tgt).filter (kOkH p N pos tgt)

@[expose] def kSolA (p N pos : Nat) (tgt : Nat → Nat) : List (List Nat) :=
  (kCandA p N pos tgt).filter (kOkA p N pos tgt)

@[expose] def kTgt1 (p c0 n : Nat) (c : Nat) : Nat := if c = c0 then (p - n % p) % p else 0

@[expose] def kCells1 (p N pos c0 mi ni : Nat) : List (List GGDepANPair) :=
  let X := ggTWNX N
  (kSolH p N pos (kTgt1 p c0 ni)).flatMap fun ha => (kSolA p N pos (kTgt1 p c0 mi)).filterMap
    fun aa => if ggDepANDot p aa ha == 2 % p && ggDepANDot p aa X != 0 then some [(ha, aa)]
      else none

@[expose] def kCells2 (p N pos c : Nat) (c2 : Option Nat) : List (List GGDepANPair) :=
  let X := ggTWNX N
  let Z := ggTWNZ p N pos
  let nb := match c2 with | none => (p - 1) % p | some _ => 0
  (kSolH p N pos (kTgt1 p c 1)).flatMap fun h1 => (kSolA p N pos (kTgt1 p c 1)).flatMap fun a1 =>
    if ggDepANDot p a1 h1 == 2 % p then
      (kSolH p N pos (ggTWNTgt2 p c2)).flatMap fun h2 =>
        if ggDepANDot p a1 h2 == nb then
          (kSolA p N pos (ggTWNTgt2 p c2)).filterMap fun a2 =>
            if ggDepANDot p a2 h2 == 2 % p && ggDepANDot p a2 h1 == nb &&
                (ggDepANDot p a1 X != 0 || ggDepANDot p a2 X != 0) &&
                (ggDepANDot p a1 X * ggDepANDot p a2 Z) % p ==
                  (ggDepANDot p a1 Z * ggDepANDot p a2 X) % p then some [(h1, a1), (h2, a2)]
            else none
        else []
    else []

abbrev KHK := (Nat × List Nat × Nat × List Nat) × List (List Nat)

@[expose] def kH0 : KHK := ((0, [], 0, []), [])

@[expose] def kHKTest (p N pos : Nat) (news : List GGDepANPair) (y : List Nat) (h : KHK) : Bool :=
  let og := ggTWLOGens p N pos news
  let G := N - 1 + news.length
  let w : GGTWLHK := ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2⟩
  let R := h.2
  let s := ggTWNWord p N news (ggTWNGen p N news w.g) w.w
  let v := w.ow.foldr (fun k acc => ggTWNRefl p (og.getD k ([], [])) acc) (og.getD w.oc ([], [])).1
  let sv := ggTWNRefl p s v
  decide (w.g < G) && w.w.all (fun g => decide (g < G)) && decide (w.oc < og.length) &&
    w.ow.all (fun k => decide (k < og.length)) &&
    ggTWLStable p og (og.map (·.1)) R &&
    ggDepANDot p s.2 y % p == 0 &&
    R.all fun u => !ggTWLParMod p y u sv

@[expose] def kPairEq (p : Nat) (q r : GGDepANPair) : Bool :=
  (ggTWLVecEq p q.1 r.1 && ggTWLVecEq p q.2 r.2) ||
    (ggTWLVecEq p q.1 (ggDepANSmul p (p - 1) r.1) && ggTWLVecEq p q.2 (ggDepANSmul p (p - 1) r.2))

@[expose] def kEWord (p : Nat) (e : List GGDepANPair) (q : GGDepANPair) (u : List Nat) :
    GGDepANPair :=
  u.foldr (fun k acc => ggDepANConj p acc (e.getD k ([], []))) q

abbrev KE8 := List GGDepANPair × List (Nat × List Nat) × List (Nat × List Nat)

@[expose] def kE0 : KE8 := ([], [], [])

@[expose] def kE8Test (p N : Nat) (news : List GGDepANPair) (w : KE8) : Bool :=
  let d := N - 1
  let G := N - 1 + news.length
  let e := w.1
  decide (e.length = 8) && decide (w.2.1.length = G) && decide (w.2.2.length = 8) &&
    e.all (fun q => decide (q.1.length = d) && decide (q.2.length = d)) &&
    (List.range 8).all (fun i => (List.range 8).all fun j =>
      ggDepANDot p (e.getD i ([], [])).2 (e.getD j ([], [])).1 % p == ggTWLCartanE p i j) &&
    (List.range G).all (fun g =>
      let u := w.2.1.getD g (0, [])
      decide (u.1 < 8) && u.2.all (fun k => decide (k < 8)) &&
        kPairEq p (kEWord p e (e.getD u.1 ([], [])) u.2) (ggTWNGen p N news g)) &&
    (List.range 8).all fun i =>
      let u := w.2.2.getD i (0, [])
      decide (u.1 < G) && u.2.all (fun g => decide (g < G)) &&
        kPairEq p (ggTWNWord p N news (ggTWNGen p N news u.1) u.2) (e.getD i ([], []))

@[expose] def kCell (p N pos : Nat) (RF : List (List Nat))
    (rt : Nat → List GGDepANPair → Nat → Nat → Bool) (wits : List KKill)
    (news : List GGDepANPair) (code : Nat × Nat) : Bool :=
  if code.1 = 0 then
    let k := kKill (wits.getD code.2 kK0)
    ggTWNKillValid N (N - 1 + news.length) k && ggTWNKillTest p N news RF k
  else rt pos news code.1 code.2

abbrev KPat1 := (Nat × Nat × Nat × Nat) × List KKill × List (Nat × Nat)

abbrev KPat2 := (Nat × Nat × Nat) × List KKill × List (Nat × Nat)

@[expose] def kDecode : Nat → Option Nat
  | 0 => none
  | k + 1 => some k

@[expose] def kPat1 (p N : Nat) (RF : List (List Nat))
    (rt : Nat → List GGDepANPair → Nat → Nat → Bool) (e : KPat1) : Bool :=
  kAll2 (kCell p N e.1.1 RF rt e.2.1) (kCells1 p N e.1.1 e.1.2.1 e.1.2.2.1 e.1.2.2.2) e.2.2

@[expose] def kPat2 (p N : Nat) (RF : List (List Nat))
    (rt : Nat → List GGDepANPair → Nat → Nat → Bool) (e : KPat2) : Bool :=
  kAll2 (kCell p N e.1.1 RF rt e.2.1) (kCells2 p N e.1.1 e.1.2.1 (kDecode e.1.2.2)) e.2.2

@[expose] def kPat1At (p N : Nat) (RF : List (List Nat))
    (rt : Nat → List GGDepANPair → Nat → Nat → Bool) (S : List KPat1) (i : Nat) : Bool :=
  match S[i]? with
  | some e => kPat1 p N RF rt e
  | none => false

@[expose] def kPat2At (p N : Nat) (RF : List (List Nat))
    (rt : Nat → List GGDepANPair → Nat → Nat → Bool) (T : List KPat2) (i : Nat) : Bool :=
  match T[i]? with
  | some e => kPat2 p N RF rt e
  | none => false

@[expose] def kCover (N : Nat) (S : List KPat1) (T : List KPat2) : Bool :=
  [0, 1].all fun pos => (List.range (N - 1)).all fun c =>
    ([1, 2].all fun mi => [1, 2].all fun ni =>
      !ggTWNPat1B N pos c mi ni || (S.map (·.1)).contains (pos, c, mi, ni)) &&
    (none :: (List.range (N - 1)).map some).all fun c2 =>
      !ggTWNPat2B N pos c c2 || (T.map (·.1)).contains (pos, c, ggTWNCode c2)

@[expose] def kRT8 (p N : Nat) (H : List KHK) (E : List KE8) (pos : Nat)
    (news : List GGDepANPair) (kind k : Nat) : Bool :=
  if kind = 1 then kHKTest p N pos news (ggTWLY0 p N pos news) (H.getD k kH0)
  else if kind = 4 then kE8Test p N news (E.getD k kE0)
  else false

end Certificates.TWLK

end
