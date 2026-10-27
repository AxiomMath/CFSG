module

public import Certificates.Data.Kernel.TWLKPZ

public section

namespace Certificates.TWLK

open Certificates.DepASmall Certificates.TwoDepSmall Certificates.TwoDepSmallLow

set_option compiler.extract_closed false

abbrev KE6 := List GGDepANPair × List (Nat × List Nat) × List (Nat × List Nat) × List (Nat × Nat)

@[expose] def kF0 : KE6 := ([], [], [], [])

@[expose] def kE6Test (p N : Nat) (news : List GGDepANPair) (w : KE6) : Bool :=
  let d := N - 1
  let G := N - 1 + news.length
  let s := w.1
  let gw := w.2.1
  let sw := w.2.2.1
  let ot := w.2.2.2
  let Ts := s.map (ggTWLMatOfPair p d)
  let V := ggTWLOrbitPts p N news ot
  decide (s.length = 6) && decide (gw.length = G) && decide (sw.length = 6) &&
    decide (ot.length = 71) &&
    s.all (fun q => decide (q.1.length = d) && decide (q.2.length = d) &&
      ggDepANDot p q.2 q.1 % p == 2 % p) &&
    ot.all (fun e => decide (e.2 < G)) &&
    (List.range G).all (fun g =>
      let u := gw.getD g (0, [])
      decide (u.1 < 6) && u.2.all (fun k => decide (k < 6)) &&
        kPairEq p (kEWord p s (s.getD u.1 ([], [])) u.2) (ggTWNGen p N news g)) &&
    (List.range 6).all (fun i =>
      let u := sw.getD i (0, [])
      decide (u.1 < G) && u.2.all (fun g => decide (g < G)) &&
        kPairEq p (ggTWNWord p N news (ggTWNGen p N news u.1) u.2) (s.getD i ([], []))) &&
    (List.range 6).all (fun i => (List.range 6).all fun j =>
      ggTWLMatEq p (ggTWLMatPow p d (ggTWLMatMul p d (Ts.getD i []) (Ts.getD j []))
        (ggTWLE6M i j)) (ggTWLMatOne d)) &&
    ((List.range ot.length).all fun k => decide ((ot.getD k (0, 0)).1 < k + 1)) &&
    ggTWLNodup p (V.map fun v => [v])

@[expose] def kVKey (p : Nat) (vs : List (List Nat)) : Nat :=
  vs.foldl (fun k v => v.foldl (fun k x => k * p + x % p) k) 0

@[expose] def kIncr : List Nat → Bool
  | a :: b :: l => Nat.blt a b && kIncr (b :: l)
  | _ => true

@[expose] def kFrameOK (p N : Nat) (vs : List (List Nat)) (ws : List (List Nat)) : Bool :=
  decide (ws.length = 720) && vs.all (fun v => decide (v.length = N - 1)) &&
    ws.all (fun w => w.all fun g => decide (g + 1 < N)) &&
    kIncr (ws.map fun w => kVKey p (vs.map (ggTWNApply p N w)))

@[expose] def kRT6 (p N : Nat) (H : List KHK) (Z : List KPZ) (F : List KE6) (pos : Nat)
    (news : List GGDepANPair) (kind k : Nat) : Bool :=
  if kind = 1 then kHKTest p N pos news (ggTWLY0 p N pos news) (H.getD k kH0)
  else if kind = 2 then kPZTest p N pos news (ggTWLY0 p N pos news) (Z.getD k kZ0)
  else if kind = 3 then kE6Test p N news (F.getD k kF0)
  else false

end Certificates.TWLK

end
