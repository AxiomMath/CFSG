module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain
public import Certificates.Data.Kernel.Co2SmithS.Orb

public section

namespace CFSG.KC.Co2Eleven

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def ap12 (p x : Nat) : Nat := pg (nat_lit 12) (mask (nat_lit 12)) p x

@[expose] noncomputable def letK (A Ai B Bi : Nat) (WV WVI : Nat → Nat) (z : Int) : Nat :=
  if z = 1 then A else if z = -1 then Ai else if z = 2 then B else if z = -2 then Bi
  else if 0 < z then WV (z.natAbs - 3) else WVI (z.natAbs - 3)

@[expose] noncomputable def wordK (A Ai B Bi : Nat) (WV WVI : Nat → Nat) (wd : List Int) : Nat :=
  wd.foldr (fun z acc => pcomp (nat_lit 2300) (nat_lit 12) (mask (nat_lit 12))
    (letK A Ai B Bi WV WVI z) acc) (pidn (nat_lit 2300) (nat_lit 12))

@[expose] noncomputable def perm12 (p q : Nat) : Bool :=
  permOK (nat_lit 2300) (nat_lit 12) (mask (nat_lit 12)) (nat_lit 27600) p q

@[expose] noncomputable def lettersK (A B : Nat) (WV WVI : Nat → Nat) (ws : List (List Int)) :
    Bool :=
  let Ai := pinvS (nat_lit 2300) (nat_lit 12) (mask (nat_lit 12)) A
  let Bi := pinvS (nat_lit 2300) (nat_lit 12) (mask (nat_lit 12)) B
  perm12 A Ai && perm12 B Bi &&
    (List.range ws.length).all fun j =>
      perm12 (WV j) (WVI j) && Nat.beq (WV j) (wordK A Ai B Bi WV WVI (ws.getD j []))

@[expose] noncomputable def chainLet (WV WVI : Nat → Nat) (chain : List Nat) (l : Nat) : Nat :=
  if l % 2 = 0 then WV (chain.getD (l / 2) 0) else WVI (chain.getD (l / 2) 0)

@[expose] noncomputable def iterK (Y : Nat) (i ω : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ω (fun _ acc => ap12 Y acc) i

@[expose] noncomputable def lvK (LC : Nat → Nat) (NL : Nat) (bs : List Nat) : Nat → List Nat
  | 0 => List.range NL
  | i + 1 => (lvK LC NL bs i).filter fun l => Nat.beq (ap12 (LC l) (bs.getD i 0)) (bs.getD i 0)

@[expose] noncomputable def rf (R : Nat → Nat) (i t x : Nat) : Nat := ap12 (R (64 * i + t)) x

@[expose] noncomputable def levelK (LC : Nat → Nat) (NL : Nat) (bs : List Nat) (R : Nat → Nat)
    (i N : Nat) : Bool :=
  let lv := lvK LC NL bs i
  decide (0 < N) && decide (N ≤ 2300) && Nat.beq (rf R i 4 N) N &&
    (List.range N).all (fun k =>
      CFSG.KC.Co2SmithS.orbRecK (fun j x => ap12 (LC (lv.getD j 0)) x) lv.length N (bs.getD i 0)
        (rf R i 0) (rf R i 1) (rf R i 6) (rf R i 4) (rf R i 5) (fun k j => rf R i (8 + j) k) k &&
      Nat.beq (rf R i 2 k) (if k = 0 then 0 else lv.getD (rf R i 6 k) 0) &&
      Nat.beq (rf R i 3 (rf R i 0 k)) k) &&
    (List.range 2300).all fun x =>
      Nat.beq (rf R i 3 x) 4095 || (decide (rf R i 3 x < N) && Nat.beq (rf R i 0 (rf R i 3 x)) x)

@[expose] noncomputable def invL (l : Nat) : Nat := if l % 2 = 0 then l + 1 else l - 1

@[expose] noncomputable def wiK (LC R : Nat → Nat) (i : Nat) (fuel : Nat) : Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat → List Nat) (fun _ img => img)
    (fun _ ih k img => if 0 < k ∧ rf R i 1 k < k then
      ih (rf R i 1 k) (img.map fun x => ap12 (LC (invL (rf R i 2 k))) x) else img) fuel

@[expose] noncomputable def siftL (LC R : Nat → Nat) (bs szs : List Nat) (ls : List Nat) :
    List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun img => decide (img = bs))
    (fun i _ ih img => decide (rf R i 3 (img.getD i 0) < szs.getD i 0) &&
      ih (wiK LC R i (nat_lit 2300) (rf R i 3 (img.getD i 0)) img)) ls

@[expose] noncomputable def tupK (Y m p : Nat) : List Nat := (List.range m).map fun i => iterK Y i p

@[expose] noncomputable def baseK (WV : Nat → Nat) (is ih m : Nat) : List Nat :=
  (List.range m).map fun i => iterK (WV is) i (ap12 (WV ih) 0)

@[expose] noncomputable def levelsK (WV WVI R : Nat → Nat) (chain : List Nat) (is ih m : Nat)
    (szs : List Nat) : Bool :=
  decide (szs.length = m) &&
    (List.range m).all fun i => levelK (chainLet WV WVI chain) (2 * chain.length)
      (baseK WV is ih m) R i (szs.getD i 0)

@[expose] noncomputable def countK (WV WVI R : Nat → Nat) (chain : List Nat) (is ih m bound : Nat)
    (szs : List Nat) : Bool :=
  decide (((List.range 2300).filter fun p => siftL (chainLet WV WVI chain) R (baseK WV is ih m) szs
    (List.range m) (tupK (WV is) m p)).length ≤ bound)

@[expose] noncomputable def miscK (WV : Nat → Nat) (ws : List (List Int)) (chain : List Nat)
    (is ih m e : Nat) (szs : List Nat) : Bool :=
  decide (is < ws.length) && decide (ih < ws.length) && chain.all (fun j => decide (j < ws.length)) &&
    decide (0 < m) && decide (ap12 (WV ih) 0 < 2300) &&
    Nat.beq (ppow (nat_lit 2300) (nat_lit 12) (mask (nat_lit 12)) (pidn (nat_lit 2300) (nat_lit 12))
      (WV is) e) (pidn (nat_lit 2300) (nat_lit 12)) &&
    !Nat.beq (WV is) (pidn (nat_lit 2300) (nat_lit 12)) &&
    decide (szs.foldl (· * ·) 1 = 42305421312000)

@[expose] def chunkK : List Nat → List Nat → List (List Nat)
  | [], _ => []
  | k :: ns, flat => flat.take k :: chunkK ns (flat.drop k)

@[expose] noncomputable def elevenK (A B : Nat) (WV WVI R : Nat → Nat) (ws : List (List Int))
    (is ih : Nat) (chain : List Nat) (m e bound : Nat) (szs : List Nat) : Bool :=
  lettersK A B WV WVI ws && levelsK WV WVI R chain is ih m szs &&
    countK WV WVI R chain is ih m bound szs && miscK WV ws chain is ih m e szs

@[expose] def memK (a : Nat) : List Nat → Bool
  | [] => false
  | b :: l => Nat.beq a b || memK a l

@[expose] def nodupK : List Nat → Bool
  | [] => true
  | a :: l => !memK a l && nodupK l

@[expose] noncomputable def centPts (WV : Nat → Nat) (ids : List Nat) (is ih e : Nat) : List Nat :=
  (List.range (e * ids.length)).map fun t =>
    iterK (WV is) (t / ids.length) (ap12 (WV (ids.getD (t % ids.length) 0)) (ap12 (WV ih) 0))

@[expose] noncomputable def centK (WV : Nat → Nat) (ws : List (List Int)) (ids : List Nat)
    (is ih e : Nat) : Bool :=
  ids.all (fun j => decide (j < ws.length) &&
    Nat.beq (pcomp (nat_lit 2300) (nat_lit 12) (mask (nat_lit 12)) (WV j) (WV is))
      (pcomp (nat_lit 2300) (nat_lit 12) (mask (nat_lit 12)) (WV is) (WV j))) &&
    nodupK (centPts WV ids is ih e)

end CFSG.KC.Co2Eleven

end
