module

public import Certificates.Data.CFSGNative.MonsterAxis.Basic

public section

namespace CFSG.Monster.AxisCount.Native

open CFSG.Monster.B.Rep4371.Native

set_option compiler.extract_closed false

structure DVec where
  e : Nat
  D : Array Int

instance : Inhabited DVec := ⟨⟨0, #[]⟩⟩

@[expose] def scale (f : Nat) (A : Array Int) : Array Int :=
  let m : Int := 2 ^ f
  A.map (· * m)

@[expose] def reduceN : Nat → DVec → DVec
  | 0, v => v
  | n + 1, v =>
    if v.e > 0 && v.D.all (fun x => x % 2 == 0) then reduceN n ⟨v.e - 1, v.D.map (· / 2)⟩ else v

@[expose] def DVec.reduce (v : DVec) : DVec := reduceN v.e v

@[expose] def DVec.eqv (v w : DVec) : Bool :=
  scale (max v.e w.e - v.e) v.D == scale (max v.e w.e - w.e) w.D

@[expose] def DVec.ofListE (e : Nat) (l : List (Nat × Int)) : DVec :=
  ⟨e, l.foldl (fun D t => if t.1 < 196884 then D.modify t.1 (fun y => y + t.2) else D)
    (Array.replicate 196884 0)⟩

@[expose] def DVec.ofList (l : List (Nat × Int)) : DVec := DVec.ofListE 0 l

@[expose] def rndEntry (seed k : Nat) : Int :=
  let x := seed * 1000003 + k + 88172645463325252
  let x := (x ^^^ (x >>> 30)) * 13787848793156543929 % 2 ^ 64
  let x := (x ^^^ (x >>> 27)) * 10723151780598845931 % 2 ^ 64
  let x := x ^^^ (x >>> 31)
  ((x % 7 : Nat) : Int) - 3

@[expose] def randDVec (seed : Nat) : DVec :=
  ⟨0, Array.ofFn (n := 196884) fun k => rndEntry seed k.val⟩

@[expose] def aStarDVec (_ : Unit) : DVec := DVec.ofList [(0, 1), (1, 1), (24, -1), (300, -2)]

structure GD where
  latS : Nat
  G : Array Int
  tT : Array Pauli
  tD : Array Pauli
  rowS : Nat
  rowT : Array (List (Nat × Int))

@[expose] def GD.eNew (g : GD) : Nat := max (2 * g.latS) (g.latS + g.rowS)

@[expose] def GD.xT (c : Ctx) (g : GD) (p : Nat) : List (Nat × Int) :=
  let k := c.keys[p]!
  let y := fastAct g.tT g.tD (false, k.1, k.2)
  [(c.find y.2.1 y.2.2, sgnI y.1)]

@[expose] def GD.wT (g : GD) (k : Nat) : List (Nat × Int) :=
  (g.rowT[k / 24]!).map fun t => (t.1 * 24 + k % 24, t.2)

@[expose] def applyGD (c : Ctx) (g : GD) (v : DVec) : DVec :=
  ⟨v.e + g.eNew,
    scale (g.eNew - 2 * g.latS) (latA g.G v.D) ++
    scale g.eNew (scatterAt 300 98280 (g.xT c) v.D) ++
    scale (g.eNew - g.latS - g.rowS) (scatterAt 0 98304 g.wT (wMul g.G v.D))⟩

inductive Gen where
  | rho (q : Pauli)
  | perm (arr : Array Nat)
  | sign (a : Nat)
  | xi
  | tau

@[expose] def GD.ofGen (c : Ctx) : Gen → GD
  | .rho q => ⟨0, idG, tabT (conjPauliN q), tabD (conjPauliN q), 0, monoRows (ePauliN q)⟩
  | .perm arr =>
    let bt := betaTab arr
    ⟨0, permG arr, tabTPerm arr bt c.th, tabDPerm arr c.th, 0, monoRows (ePermT arr bt)⟩
  | .sign a => ⟨0, signG a, tabT (conjYN a), tabD (conjYN a), 0, monoRows (eYN a)⟩
  | .xi => ⟨1, xiG, tabT conjXiN, tabD conjXiN, 6, xiRows ()⟩
  | .tau => ⟨0, #[], #[], #[], 0, #[]⟩

@[expose] def Gen.xiPow (e : Nat) : List Gen := List.replicate e Gen.xi

@[expose] def Gen.tauPow (e : Nat) : List Gen := List.replicate e Gen.tau

@[expose] def tauT (tb : TauTab) (p : Nat) : List (Nat × Int) :=
  if p < 24 then [(p, 8)]
  else if p < 300 then [(300 + 2 * (p - 24), 8), (300 + 2 * (p - 24) + 1, -8)]
  else if p < 852 then
    if (p - 300) % 2 = 0 then
      [(24 + (p - 300) / 2, 4), (300 + 2 * ((p - 300) / 2), 4), (300 + 2 * ((p - 300) / 2) + 1, 4)]
    else
      [(24 + (p - 300) / 2, 4), (300 + 2 * ((p - 300) / 2), -4), (300 + 2 * ((p - 300) / 2) + 1, -4)]
  else if p < 50004 then
    [(98580 + (2048 + (p - 852) / 24) * 24 + (p - 852) % 24,
      8 * sgnI (tb.w[(p - 852) / 24]!.testBit ((p - 852) % 24)))]
  else if p < 98580 then
    (List.range 64).map fun q' => (50004 + (p - 50004) / 64 * 64 + q', tb.S[(p - 50004) % 64 * 64 + q']!)
  else if (p - 98580) / 24 < 2048 then
    [(852 + 24 * ((p - 98580) / 24) + (p - 98580) % 24, 8 * sgnI tb.pb[(p - 98580) / 24]!)]
  else
    [(98580 + ((p - 98580) / 24 - 2048) * 24 + (p - 98580) % 24,
      8 * sgnI (tb.w[(p - 98580) / 24 - 2048]!.testBit ((p - 98580) % 24)) *
        sgnI tb.pb[(p - 98580) / 24 - 2048]!)]

@[expose] def applyTau (c : Ctx) (v : DVec) : DVec := ⟨v.e + 3, scatterAt 0 196884 (tauT c.tau) v.D⟩

@[expose] def applyGen (c : Ctx) (g : Gen) (v : DVec) : DVec :=
  match g with
  | .tau => applyTau c v
  | _ => applyGD c (GD.ofGen c g) v

@[expose, noinline] def evalWordC (c : Ctx) (w : List Gen) (v : DVec) : DVec :=
  w.foldl (fun v g => (applyGen c g v).reduce) v

@[expose] def evalWord (w : List Gen) (v : DVec) : DVec := evalWordC (mkCtx ()) w v

@[expose] def permInv (arr : Array Nat) : Array Nat :=
  Array.ofFn (n := 24) fun j => ((List.range 24).find? fun k => arr[k]! == j.val).getD 0

@[expose] def permValid (arr : Array Nat) : Bool :=
  arr.size == 24 && (List.range 24).all (fun i => arr[i]! < 24) &&
  (List.range 24).all (fun j => (permInv arr)[j]! < 24) &&
  (List.range 24).all (fun j => arr[(permInv arr)[j]!]! == j) &&
  (List.range 24).all (fun i => (permInv arr)[arr[i]!]! == i) &&
  (List.range 12).all fun i =>
    wordN (coeffN (permWordN arr (bmaskN i))) == permWordN arr (bmaskN i) &&
    wordN (coeffN (permWordN (permInv arr) (bmaskN i))) == permWordN (permInv arr) (bmaskN i)

@[expose] def Gen.validB : Gen → Bool
  | .perm arr => permValid arr
  | _ => true

@[expose, noinline] def checkWordC (c : Ctx) (w : List Gen) (v v' : DVec) : Bool :=
  w.all (fun g => g.validB) && (evalWordC c w v).eqv v'

@[expose] def checkWord (w : List Gen) (v v' : DVec) : Bool := checkWordC (mkCtx ()) w v v'

@[expose, noinline] def checkWordsC (c : Ctx) (ws : List (List Gen × DVec × DVec)) : Bool :=
  ws.all fun x => checkWordC c x.1 x.2.1 x.2.2

@[expose] def checkWords (ws : List (List Gen × DVec × DVec)) : Bool := checkWordsC (mkCtx ()) ws

@[expose, noinline] def checkEqsC (c : Ctx) (vs : Array DVec) (items : List (List Gen × Nat × Nat)) :
    Bool :=
  items.all fun x => checkWordC c x.1 vs[x.2.1]! vs[x.2.2]!

@[expose] def checkEqs (vs : Array DVec) (items : List (List Gen × Nat × Nat)) : Bool :=
  checkEqsC (mkCtx ()) vs items

end CFSG.Monster.AxisCount.Native
