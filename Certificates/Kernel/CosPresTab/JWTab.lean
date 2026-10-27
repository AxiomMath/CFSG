module

public import Certificates.Data.Kernel.TabWordK
public import Certificates.Kernel.Sporadic.McLK.Defs
public import CFSG.Sporadic.Recognition.JankoWongPresInputs
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 200

namespace CFSG.KC.TabWord.JW

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CertificateChecks.KernelSpor.McLK
  CFSG.Sporadic.Recognition.JankoWong

@[expose] noncomputable def idn : Nat := pidn 275 9

@[expose] noncomputable def PAL : Nat := pmk 275 9 fun x => r32 AL x

@[expose] noncomputable def PBE : Nat := pmk 275 9 fun x => r32 BE x

@[expose] noncomputable def PBI : Nat := pmk 275 9 fun x => r32 BI x

@[expose] noncomputable def BL (z : Int) : Nat :=
  if z = 1 ∨ z = -1 then PAL else if z = 2 then PBE else PBI

@[expose] noncomputable def TP (neg : Bool) (k : Nat) : Nat := wordK 275 9 idn BL (jwGenWord neg k)

@[expose] noncomputable def VP (neg : Bool) (k : Nat) : Nat :=
  wordK 275 9 idn BL ((jwGenWord neg k).reverse.map Neg.neg)

@[expose] noncomputable def LP (neg : Bool) (z : Int) : Nat :=
  if z = 1 then TP neg 0 else if z = 2 then TP neg 1 else if z = 3 then TP neg 2
  else if z = 4 then TP neg 3 else if z = 5 then TP neg 4 else if z = 6 then TP neg 5
  else if z = -1 then VP neg 0 else if z = -2 then VP neg 1 else if z = -3 then VP neg 2
  else if z = -4 then VP neg 3 else if z = -5 then VP neg 4 else VP neg 5

@[expose] noncomputable def genOk (neg : Bool) (k : Nat) : Bool :=
  allLtK 275 9 (VP neg k) 275 &&
    Nat.beq (pcomp 275 9 (mask 9) (VP neg k) (TP neg k)) idn

@[expose] noncomputable def jwOk (neg : Bool) : Bool :=
  allLtK 275 9 PAL 275 && allLtK 275 9 PBE 275 && allLtK 275 9 PBI 275 &&
    (List.range' 0 6).all (genOk neg) &&
    (jwRels neg).all (fun r => Nat.beq (wordK 275 9 idn (LP neg) (r.map jwLetterZ)) idn) &&
    Nat.beq (wordK 275 9 idn (LP neg) jwSurjA) PAL &&
    Nat.beq (wordK 275 9 idn (LP neg) (jwSurjB neg)) PBE

theorem jw_ok_false : jwOk false = true := by quickRfl

theorem jw_ok_true : jwOk true = true := by quickRfl

theorem neg_rel : (!Nat.beq (wordK 275 9 idn (LP false) [1]) idn) = true := by quickRfl

theorem neg_surj : (!Nat.beq (wordK 275 9 idn (LP false) (jwSurjB true)) PBE) = true := by
  quickRfl

end CFSG.KC.TabWord.JW

end
