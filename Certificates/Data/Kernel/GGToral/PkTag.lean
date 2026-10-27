module

public import Certificates.Data.Kernel.GGToral.Pk
public import CFSG.Blueprint.Chevalley

public section

namespace CFSG.KC.GGToral

open CFSG.Blueprint.Chevalley

@[expose] noncomputable def tgRank (τ : Tag) : Nat :=
  Tag.rec (motive := fun _ => Nat) 2 4 4 6 7 8 τ

@[expose] noncomputable def tgNp (τ : Tag) : Nat :=
  Tag.rec (motive := fun _ => Nat) 6 24 12 36 63 120 τ

@[expose] noncomputable def tgOK (τ : Tag) : Bool :=
  Tag.rec (motive := fun _ => Bool) false true false true true true τ

@[expose] noncomputable def pkTheta (τ : Tag) : List Nat :=
  Tag.rec (motive := fun _ => List Nat) [] [2, 3, 4, 2] [] [1, 2, 2, 3, 2, 1] [2, 2, 3, 4, 3, 2, 1]
    [2, 3, 4, 6, 5, 4, 3, 2] τ

@[expose] noncomputable def tgK0 (τ : Tag) : Nat :=
  Tag.rec (motive := fun _ => Nat) 0 0 0 1 0 7 τ

@[expose] noncomputable def tgCneg (τ : Tag) : Nat :=
  Tag.rec (motive := fun _ => Nat) 0
    169230328010303641331690318856389418788647235367734092945509472698594606438732922831669549330939436994164777234610094526758912
    0
    84162174424773976115855838126082074857850631560511950762607064234252541599391005606483490444719097205486700613504589952195310791364040509934732543733621344588621959565840197895853065879350183033666834179911843840
    1876879207201175057492789423877314576801726697201389918429382765738862525710183501839407269632480758244013025282125952997663166539505617809464354493712151794381882758392558304573462348533931709843239240389098655675685759680288582270941200429463966142431232
    41855804968213567224547853478906328786189690805581178444396888406252332961286172713959820640856630213448697736448517078129897401976853046573883322080827925438862068296719706967879368940604858713180851230580635381195307951619317795396847896544051977449463156304801026011817878911469416472158670946304
    τ

@[expose] noncomputable def tgDiag (τ : Tag) : Nat :=
  Tag.rec (motive := fun _ => Nat) 0 281479271809026 0 1208944266640182156001281
    79229371458530977775699951617 5192376087906286159508272029171713 τ

@[expose] noncomputable def packN (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun j ih => Nat.add ih (Nat.shiftLeft (f j) (Nat.mul 16 j))) n

@[expose] noncomputable def sumN (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun j ih => Nat.add ih (f j)) n

@[expose] noncomputable def packRevL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun a _ ih => fun acc => ih (Nat.add (Nat.mul acc 65536) a)) l 0

@[expose] noncomputable def maskN (m : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun s ih => Nat.add ih (Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft 1 s) (f s))) m

@[expose] noncomputable def allN (m : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun r ih => andB (f r) ih) m

@[expose] noncomputable def rtC (H : Hd) (r k : Nat) : Nat := lane (row H.rrev r) (Nat.sub (Nat.sub H.n 1) k)

@[expose] noncomputable def negC (τ : Tag) (H : Hd) (r j : Nat) : Nat :=
  sumN H.n (fun k => Nat.mul (lane (row (tgCneg τ) j) k) (rtC H r k))

@[expose] noncomputable def gramC (τ : Tag) (H : Hd) (r : Nat) : Nat :=
  Nat.sub (sumN H.n (fun j => Nat.mul (Nat.mul (rtC H r j) (lane (tgDiag τ) j)) (Nat.mul 2 (rtC H r j))))
    (sumN H.n (fun j => Nat.mul (Nat.mul (rtC H r j) (lane (tgDiag τ) j)) (negC τ H r j)))

@[expose] noncomputable def corC (τ : Tag) (H : Hd) (r j : Nat) : Nat :=
  let ps := Nat.mul 2 (rtC H r j)
  let ng := negC τ H r j
  let dj := Nat.mul 2 (lane (tgDiag τ) j)
  let g := gramC τ H r
  Bool.rec (motive := fun _ => Nat)
    (Nat.mod (Nat.sub H.p (Nat.mod (Nat.div (Nat.mul dj (Nat.sub ng ps)) g) H.p)) H.p)
    (Nat.mod (Nat.div (Nat.mul dj (Nat.sub ps ng)) g) H.p)
    (Nat.ble ng ps)

@[expose] noncomputable def corExact (τ : Tag) (H : Hd) (r : Nat) : Bool :=
  andB (Nat.blt 0 (gramC τ H r)) (allN H.n (fun j =>
    let ps := Nat.mul 2 (rtC H r j)
    let ng := negC τ H r j
    Nat.beq (Nat.mod (Nat.mul (Nat.mul 2 (lane (tgDiag τ) j)) (Nat.add (Nat.sub ps ng)
      (Nat.sub ng ps))) (gramC τ H r)) 0))

@[expose] noncomputable def gramNZ (τ : Tag) (H : Hd) (r s : Nat) : Bool :=
  notB (Nat.beq
    (sumN H.n (fun j => Nat.mul (Nat.mul (rtC H s j) (lane (tgDiag τ) j)) (Nat.mul 2 (rtC H r j))))
    (sumN H.n (fun j => Nat.mul (Nat.mul (rtC H s j) (lane (tgDiag τ) j)) (negC τ H r j))))

@[expose] noncomputable def atilC (τ : Tag) (H : Hd) (l j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.mod (lane (row (tgCneg τ) l) j) H.p) (Nat.sub H.p 2)
    (Nat.beq j l)

@[expose] noncomputable def gRev (v : Nat) : Nat :=
  Nat.add (lane v 5) (Nat.add (Nat.shiftLeft (lane v 3) 16) (Nat.add (Nat.shiftLeft (lane v 2) 32)
    (Nat.add (Nat.shiftLeft (lane v 1) 48) (Nat.add (Nat.shiftLeft (lane v 4) 64)
      (Nat.shiftLeft (lane v 0) 80)))))

@[expose] noncomputable def tagHdOK (τ : Tag) (p mode : Nat) (H : Hd) : Bool :=
  andB (tgOK τ) (andB (Nat.beq H.mode mode) (andB (Nat.beq H.n (tgRank τ)) (andB (Nat.beq H.p p)
  (andB (Nat.ble 3 p) (andB (Nat.blt p 16) (andB (Nat.beq H.np (tgNp τ))
  (andB (Nat.beq H.threv (packRevL (pkTheta τ))) (andB (Nat.beq H.k0 (tgK0 τ))
  (andB (allN H.n (fun l => Nat.beq (row H.atil l) (packN H.n (atilC τ H l))))
  (andB (allN H.np (fun r => Nat.blt (row H.rrev r) (Nat.shiftLeft 1 (Nat.mul 16 H.n))))
  (andB (allN H.np (fun r => andB (Nat.beq (row H.cor r) (packN H.n (corC τ H r)))
    (corExact τ H r)))
  (andB (allN H.np (fun r => Nat.beq (row H.adj r) (maskN H.np (gramNZ τ H r))))
  (orB (Nat.beq mode 0) (andB (Nat.beq mode 1)
    (allN H.np (fun r => andB (Nat.blt (lane H.gam r) H.np)
      (Nat.beq (row H.rrev (lane H.gam r)) (gRev (row H.rrev r)))))))))))))))))))

@[expose] noncomputable def pkTag (τ : Tag) (p mode : Nat) (D : List Nat) : Bool :=
  hdK (fun H _ => tagHdOK τ p mode H) D

end CFSG.KC.GGToral
