module

public import Certificates.Data.Kernel.Co2Smith.Rows
public import Certificates.Data.CFSGNative.HS.SmallF2
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.Co2Span

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.SmallF2.Native

@[expose] def allN (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => f n && allN f n

@[expose] def xbits (t sg cb a : Nat) : Bool :=
  if a / 22 < 2 then decide (a % 22 < 2) && t.testBit (2 * (a / 22) + a % 22)
  else decide (2 ≤ a % 22) &&
    ((sg >>> (4 * ((a % 22 - 2) / 2))) % 16 == (a / 22 - 2) / 2) &&
      cb.testBit (4 * ((a % 22 - 2) / 2) + 2 * ((a % 22 - 2) % 2) + (a / 22 - 2) % 2)

@[expose] def xPack (t sg cb : Nat) : Nat := ofBits 484 (xbits t sg cb)

@[expose] noncomputable def xPackS (t sg cb : Nat) : Nat :=
  CFSG.KC.Loop.strictN sg fun sg => CFSG.KC.Loop.strictN cb fun cb => xPack t sg cb

@[expose] def sgOf (S : Array Nat) (m : Nat) : Nat :=
  ofBits 40 fun b => (S.getD (10 * m + b / 4) 0 % 10).testBit (b % 4)

@[expose] def cfNat (v c : Nat) : Bool := if c = 0 then v != 1 else v != 0

@[expose] def cbOf (U : Array Nat) (m : Nat) : Nat :=
  ofBits 40 fun b => cfNat (U.getD (20 * m + 2 * (b / 4) + b % 4 / 2) 0 / 3 % 3) (b % 2)

@[expose] def sgId : Nat := ofBits 40 fun b => (b / 4).testBit (b % 4)

@[expose] def cbId : Nat := ofBits 40 fun b => b % 4 / 2 == b % 2

@[expose] def eqMaskP (Y Z i j : Nat) : Nat :=
  (List.range 22).foldl (fun acc q =>
    acc ^^^ (if Y.testBit (22 * q + j) then 1 <<< (22 * i + q) else 0) ^^^
      (if Z.testBit (22 * i + q) then 1 <<< (22 * q + j) else 0)) 0

@[expose] def eqAtP (Ys Zs : List Nat) (r : Nat) : Nat :=
  eqMaskP (Ys.getD (r / 484) 0) (Zs.getD (r / 484) 0) (r % 484 / 22) (r % 22)

@[expose] def xorEqs (Ys Zs : List Nat) (rs : List Nat) : Nat :=
  rs.foldl (fun acc r => acc ^^^ eqAtP Ys Zs r) 0

@[expose] def fullP : Nat := 2 ^ 484 - 1

@[expose] def peelK (Ys Zs : List Nat) : Nat → List (Nat × List Nat) → Bool
  | K, [] => K == fullP
  | K, (a, rs) :: L => decide (a < 484) && rs.all (fun r => decide (r < 1452)) &&
      (xorEqs Ys Zs rs &&& (fullP ^^^ K) == 1 <<< a) && peelK Ys Zs (K ||| 1 <<< a) L

@[expose] def maskOf (l : List Nat) : Nat := l.foldl (fun m f => m ||| (1 <<< f)) 0

@[expose] def rowsAgree (R : Array Nat) (P : Nat) : Bool :=
  allN (fun r => allN (fun c => (R[r]?.getD 0).testBit c == P.testBit (22 * r + c)) 22) 22

@[expose] def comboP (Bs : List Nat) (cc : Nat) : Nat :=
  (List.range 11).foldl (fun acc i => if cc.testBit i then acc ^^^ Bs.getD i 0 else acc) 0

@[expose] noncomputable def wordP (X1 X2 : Nat) (w : List (Nat × Nat)) : Nat :=
  w.foldl (fun acc q => mulV acc (powK (if q.1 % 2 == 0 then X1 else X2) q.2)) IDP

@[expose] noncomputable def relsP (X1 X2 M : Nat) (tw : List (List (Nat × Nat))) (kk : List Nat) :
    Bool :=
  (tw.zip kk).all fun p => eqK (powK (mulV (wordP X1 X2 p.1) M) p.2) IDP

@[expose] noncomputable def conjP (Qs : List Nat) (X1 X2 M X01 X02 M0 : Nat) : Bool :=
  Qs.any fun Q => eqK (mulV Q X1) (mulV X01 Q) && eqK (mulV Q X2) (mulV X02 Q) &&
    eqK (mulV Q M) (mulV M0 Q)

@[expose] noncomputable def enumP (Bs X1s X2s : List Nat) (tw : List (List (Nat × Nat)))
    (kk : List Nat) (Qs : List Nat) (X01 X02 M0 : Nat) : Bool :=
  allN (fun cc => letB (comboP Bs cc) fun M =>
    !eqK (powK M 3) IDP || allN (fun c₁ => letB (X1s.getD c₁ 0) fun X1 =>
      !eqK (powK (mulV X1 M) (kk.getD 0 0)) IDP || allN (fun c₂ => letB (X2s.getD c₂ 0) fun X2 =>
        !relsP X1 X2 M tw kk || conjP Qs X1 X2 M X01 X02 M0) 16) 16) 2048

end CFSG.KC.Co2Span
