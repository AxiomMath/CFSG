module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Bits
public import Mathlib

public section

namespace CFSG.KC.O8Split

open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.NSplit
  CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def fld (w x k : ℕ) : ℕ := (x >>> (w * k)) % 2 ^ w

@[expose] def xorN : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => xorN n f ^^^ f n

@[expose] def packN (w : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => packN w n f ||| (f n <<< (w * n))

@[expose] def allN : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n + 1, p => allN n p && p n

@[expose] def applyM (mm v : ℕ) : ℕ := xorN 7 fun b => if v.testBit b then fld 7 mm b else 0

@[expose] def pi0 (m : ℕ) : ℕ := packN 6 m fun g => g

@[expose] def mm0 : ℕ := packN 7 7 fun b => 2 ^ b

@[expose] def stepPi (m TP i pi : ℕ) : ℕ := packN 6 m fun g => fld 6 pi (fld 6 TP (i * m + g))

@[expose] def stepM (TA i mm : ℕ) : ℕ := packN 7 7 fun b => applyM mm (fld 7 TA (128 * i + 2 ^ b))

@[expose] def contrib (m w YBj pi mm : ℕ) : ℕ :=
  packN w (7 * m) fun c =>
    xorN 7 fun b' => if (fld 7 mm (c % 7)).testBit b' then fld w YBj (7 * fld 6 pi (c / 7) + b')
      else 0

@[expose] def walk (m w TP TA YBj : ℕ) : List ℕ → ℕ → ℕ → ℕ → ℕ
  | [], _, _, acc => acc
  | i :: l, pi, mm, acc =>
    walk m w TP TA YBj l (stepPi m TP i pi) (stepM TA i mm)
      (acc ^^^ (contrib m w YBj pi mm <<< (w * (7 * m) * i)))

@[expose] def accN (m w TP TA : ℕ) (YB : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => walk m w TP TA (YB n) (relWords.getD n []) (pi0 m) mm0 (accN m w TP TA YB n)

@[expose] def yiRows (m w ny : ℕ) (YB : ℕ → ℕ) : Array ℕ :=
  Array.ofFn (n := ny) fun k =>
    bitsOf 203 fun c => (xorN m fun g => fld w (YB (c / 7)) (7 * g + c % 7)).testBit k

@[expose] def ySplitOK (ε : Eps) (w ny TP TA : ℕ) (YB : ℕ → ℕ) : Bool :=
  decide (ny ≤ w) &&
    allN 7 (fun i => allN (mOf ε) fun g => fld 6 TP (i * mOf ε + g) == permIdx ε i g) &&
    allN 7 (fun i => allN 128 fun x => fld 7 TA (128 * i + x) == actECode ε i x) &&
    accN (mOf ε) w TP TA YB 29 == 0 &&
    certCheck 203 49 ny (yiRows (mOf ε) w ny YB) (foxECols ε)

end CFSG.KC.O8Split

end
