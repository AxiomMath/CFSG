module

public section

namespace CFSG.KC.W4C2K

@[expose] def vm (m v : Nat) : Nat :=
  m % 16 * (v % 2) ^^^ m / 16 % 16 * (v / 2 % 2) ^^^ m / 256 % 16 * (v / 4 % 2) ^^^
    m / 4096 % 16 * (v / 8 % 2)

@[expose] def mm (x y : Nat) : Nat :=
  vm y (x % 16) + vm y (x / 16 % 16) * 16 + vm y (x / 256 % 16) * 256 +
    vm y (x / 4096 % 16) * 4096

@[expose] def trR (a b c d : Nat) : Nat :=
  (a % 2 + b % 2 * 2 + c % 2 * 4 + d % 2 * 8) +
    (a / 2 % 2 + b / 2 % 2 * 2 + c / 2 % 2 * 4 + d / 2 % 2 * 8) * 16 +
    (a / 4 % 2 + b / 4 % 2 * 2 + c / 4 % 2 * 4 + d / 4 % 2 * 8) * 256 +
    (a / 8 % 2 + b / 8 % 2 * 2 + c / 8 % 2 * 4 + d / 8 % 2 * 8) * 4096

@[expose] def tr (m : Nat) : Nat := trR (m % 16) (m / 16 % 16) (m / 256 % 16) (m / 4096 % 16)

@[expose] def idM : Nat := 33825

@[expose] def mk (g h : Nat) (s : Bool) : Nat := g + h * 65536 + (bif s then 4294967296 else 0)

@[expose] def gK (e : Nat) : Nat := e % 65536

@[expose] def hK (e : Nat) : Nat := e / 65536 % 65536

@[expose] def sK (e : Nat) : Bool := e / 4294967296 % 2 == 1

@[expose] def idK : Nat := mk idM idM false

@[expose] def eqEK (e f : Nat) : Bool := gK e == gK f && hK e == hK f && sK e == sK f

@[expose] def mulK (e f : Nat) : Nat :=
  bif sK e then mk (mm (hK f) (gK e)) (mm (gK f) (hK e)) (!sK f)
  else mk (mm (gK f) (gK e)) (mm (hK f) (hK e)) (sK f)

@[expose] def invK (e : Nat) : Nat :=
  bif sK e then mk (tr (gK e)) (tr (hK e)) true else mk (tr (hK e)) (tr (gK e)) false

@[expose] def conjK (f e : Nat) : Nat := mulK (mulK f e) (invK f)

@[expose] def commK (e x : Nat) : Bool := eqEK (mulK e x) (mulK x e)

@[expose] def appK (e : Nat) (v : Nat × Nat) : Nat × Nat :=
  bif sK e then (vm (gK e) (v.2 % 16), vm (hK e) (v.1 % 16))
  else (vm (gK e) (v.1 % 16), vm (hK e) (v.2 % 16))

@[expose] def eqVK (u v : Nat × Nat) : Bool := u.1 % 16 == v.1 % 16 && u.2 % 16 == v.2 % 16

@[expose] def xorVK (u v : Nat × Nat) : Nat × Nat := (u.1 ^^^ v.1, u.2 ^^^ v.2)

@[expose] def validK (e : Nat) : Bool := mm (gK e) (tr (hK e)) == idM

@[expose] def injK (n : Nat) : Bool := (List.range 15).all fun i => vm n ((i + 1) % 16) != 0

@[expose] def invRowK (n j : Nat) : Nat :=
  ((List.range 16).find? fun x => vm n (x % 16) == 1 <<< j).getD 0

@[expose] def invMK (n : Nat) : Nat :=
  invRowK n 0 % 16 + invRowK n 1 % 16 * 16 + invRowK n 2 % 16 * 256 + invRowK n 3 % 16 * 4096

@[expose] def dualK (n : Nat) : Nat := tr (invMK n)

@[expose] def dotK (x y : Nat) : Bool :=
  (x % 2 * (y % 2) + x / 2 % 2 * (y / 2 % 2) + x / 4 % 2 * (y / 4 % 2) +
    x / 8 % 2 * (y / 8 % 2)) % 2 == 1

@[expose] def bNK : Nat × Nat := (1, 0)

@[expose] def bMK : Nat × Nat := (1, 2)

@[expose] def ws4K : List (Nat × Nat) := [(1, 2), (0, 2), (4, 8), (8, 4)]

@[expose] def perpK (b : Nat × Nat) : List (Nat × Nat) :=
  ((List.range 16).flatMap fun x => (List.range 16).map fun y => (x, y)).filter fun v =>
    !(dotK b.1 v.2 ^^ dotK v.1 b.2)

@[expose] def stabNK (b : Nat × Nat) (n : Nat) (s : Bool) : Bool :=
  bif s then vm n (b.2 % 16) == b.1 % 16 && vm (dualK n) (b.1 % 16) == b.2 % 16
  else vm n (b.1 % 16) == b.1 % 16 && vm (dualK n) (b.2 % 16) == b.2 % 16

@[expose] def stabPK (b : Nat × Nat) (n : Nat) : List Nat :=
  ([false, true].filter (stabNK b n)).map (mk n (dualK n))

@[expose] def isCommK (P : List Nat) (E : Nat) : Bool :=
  eqEK (mulK E E) idK && P.all fun F => commK E (conjK F E)

@[expose] def candOKK (P Cl : List Nat) : Bool :=
  P.all fun E => !(eqEK (mulK E E) idK) || Cl.any (eqEK E) ||
    P.any fun F => !commK E (conjK F E)

@[expose] def chkNK (P U : List Nat) : Bool :=
  candOKK P U && U.all fun E => eqEK E idK || P.any fun F => eqEK (conjK F E) E1K
where
  E1K : Nat := mk 33841 33827 false

@[expose] def chkMK (P Cl : List Nat) : Bool :=
  candOKK P Cl && Cl.length == 16 &&
    Cl.all (fun c => eqEK (mulK c c) idK &&
      Cl.all fun c' => Cl.any (eqEK (mulK c c')) && commK c c') &&
    P.all (fun F => Cl.all fun c => Cl.any (eqEK (conjK F c))) &&
    (Cl.filter (sK · == false)).all (fun k => P.any fun p => Cl.any fun c =>
      eqEK (mulK (conjK p c) c) k) &&
    ws4K.all (fun w => (Cl.filter (sK · == false)).any fun k => (perpK bMK).any fun v =>
      eqVK (xorVK (appK k v) v) w) &&
    (Cl.filter (sK · == false)).any fun k => !(eqEK k idK) && ws4K.all fun w => eqVK (appK k w) w

@[expose] def orbWK (W : List Nat) : Bool :=
  (List.range 256).all fun n => orb1K n (W.getD n 0)
where
  orb1K (n w : Nat) : Bool :=
    n == 0 || dotK (n % 16) (n / 16) ||
      (Nat.blt (w / 2) 65536 && injK (w / 2) &&
        eqVK (appK (mk (w / 2) (dualK (w / 2)) (w % 2 == 1))
          (bif n % 16 == 0 || n / 16 == 0 then bNK else bMK)) (n % 16, n / 16))

end CFSG.KC.W4C2K
