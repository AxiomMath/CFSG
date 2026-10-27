module

public section

namespace Certificates.FzBU

@[expose] def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => p n && allBelow p n

@[expose] def anyBelow (p : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => p n || anyBelow p n

@[expose] def countBelow (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => (if p n then 1 else 0) + countBelow p n

@[expose] def f4mul (a b : Nat) : Nat :=
  ((a % 2 * (b % 2) + a / 2 * (b / 2)) % 2) +
    2 * ((a % 2 * (b / 2) + a / 2 * (b % 2) + a / 2 * (b / 2)) % 2)

@[expose] def uMul (x y : Nat) : Nat :=
  16 * ((x / 16) ^^^ (y / 16)) + 4 * ((x / 4 % 4) ^^^ (y / 4 % 4)) +
    (((x % 4) ^^^ (y % 4)) ^^^ f4mul (x / 16) (y / 4 % 4))

@[expose] def gensU : Array Nat := #[16, 32, 4, 8]

@[expose] def evalW (y : Array Nat) : List Nat → Nat
  | [] => 0
  | i :: w => uMul y[i]! (evalW y w)

@[expose] def bfsRound (tab : Array (Option (List Nat))) : Array (Option (List Nat)) :=
  (List.range 64).foldl (fun t x =>
    match tab[x]! with
    | none => t
    | some w => (List.range 4).foldl (fun t i =>
        let z := uMul gensU[i]! x
        if t[z]!.isNone then t.set! z (some (i :: w)) else t) t) tab

@[expose] def wordTab (_ : Unit := ()) : Array (List Nat) :=
  let t0 : Array (Option (List Nat)) := (Array.replicate 64 none).set! 0 (some [])
  ((List.range 12).foldl (fun t _ => bfsRound t) t0).map (fun o => o.getD [])

@[expose] def extArr (words : Array (List Nat)) (y : Array Nat) : Array Nat :=
  (Array.range 64).map (fun x => evalW y words[x]!)

@[expose] def wordsOK (words : Array (List Nat)) : Bool :=
  allBelow (fun x => evalW gensU words[x]! == x) 64

@[expose] def isAutArr (a : Array Nat) : Bool :=
  a.size == 64 && allBelow (fun x => a[x]! < 64) 64 && a[0]! == 0 &&
    allBelow (fun x => allBelow (fun y => a[x]! != a[y]!) x) 64 &&
    allBelow (fun i => allBelow (fun x =>
      a[uMul gensU[i]! x]! == uMul a[gensU[i]!]! a[x]!) 64) 4

@[expose] def commA (a b : Array Nat) : Bool := allBelow (fun x => a[b[x]!]! == b[a[x]!]!) 64

@[expose] def isRho (r : Array Nat) : Bool :=
  allBelow (fun x => x == 0 || r[x]! != x) 64 && allBelow (fun x => r[r[r[x]!]!]! == x) 64

@[expose] def condQ (r aq : Array Nat) : Bool :=
  commA aq r && allBelow (fun x => aq[aq[aq[aq[x]!]!]!]! == x) 64 &&
    countBelow (fun x => aq[aq[x]!]! == x) 64 == 16

@[expose] def condS (r aq as : Array Nat) : Bool :=
  commA as r &&
  (allBelow (fun x => as[as[x]!]! == x) 64 || allBelow (fun x => as[as[x]!]! == aq[x]!) 64 ||
    allBelow (fun x => as[as[x]!]! == aq[aq[x]!]!) 64 ||
    allBelow (fun x => as[as[x]!]! == aq[aq[aq[x]!]!]!) 64) &&
  (commA as aq || allBelow (fun x => as[aq[x]!]! == aq[aq[aq[as[x]!]!]!]!) 64) &&
  allBelow (fun x => aq[aq[x]!]! != x || uMul as[x]! x == 0) 64 &&
  allBelow (fun p => anyBelow (fun z => as[p]! == uMul z p) 4) 64

@[expose] def isInvR (r a : Array Nat) : Bool :=
  allBelow (fun x => a[a[x]!]! == x) 64 && allBelow (fun x => a[r[x]!]! == r[r[a[x]!]!]!) 64

@[expose] def conjP (g x x0 : Array Nat) : Bool := allBelow (fun i => g[x[i]!]! == x0[g[i]!]!) 64

@[expose] def repImgs (c : Bool) : Array (Array Nat) :=
  if c then #[#[4, 8, 17, 35], #[16, 32, 5, 11], #[16, 48, 4, 12]]
  else #[#[4, 8, 17, 35], #[18, 33, 7, 10], #[6, 15, 19, 49]]

@[expose] def repOK (aq as ay : Array Nat) : Bool :=
  isAutArr aq && isAutArr as && isAutArr ay &&
    allBelow (fun x => aq[aq[aq[aq[x]!]!]!]! == x) 64 && anyBelow (fun x => aq[aq[x]!]! != x) 64 &&
    allBelow (fun x => as[as[x]!]! == x) 64 &&
    allBelow (fun x => as[aq[x]!]! == aq[aq[aq[as[x]!]!]!]!) 64 &&
    allBelow (fun x => ay[ay[x]!]! == x) 64 && commA ay aq && commA ay as

structure Mod where
  aq : Array Nat
  as : Array Nat
  ay : Array Nat
  tab : Array Nat

@[expose] def iterA (f : Array Nat) : Nat → Nat → Nat
  | 0, u => u
  | i + 1, u => f[iterA f i u]!

@[expose] def Mod.act (M : Mod) (w u : Nat) : Nat :=
  iterA M.aq (w % 4) (iterA M.as (w / 4 % 2) (iterA M.ay (w / 8) u))

@[expose] def amul (w w' : Nat) : Nat :=
  ((w % 4 + (if w / 4 % 2 == 0 then w' % 4 else (4 - w' % 4) % 4)) % 4) +
    4 * ((w / 4 % 2 + w' / 4 % 2) % 2) + 8 * ((w / 8 + w' / 8) % 2)

@[expose] def Mod.mulA (M : Mod) (x y : Nat) : Nat :=
  uMul (x % 64) (M.act (x / 64) (y % 64)) + 64 * amul (x / 64) (y / 64)

@[expose] def Mod.mul (M : Mod) (x y : Nat) : Nat :=
  if x < 1024 ∧ y < 1024 then M.tab[x * 1024 + y]! else M.mulA x y

@[expose] def modl (c : Bool) (_ : Unit := ()) : Mod :=
  let r := (repImgs c).map (extArr (wordTab ()))
  let M0 : Mod := ⟨r[0]!, r[1]!, r[2]!, #[]⟩
  { M0 with tab := (Array.range 1048576).map (fun i => M0.mulA (i / 1024) (i % 1024)) }

end Certificates.FzBU
