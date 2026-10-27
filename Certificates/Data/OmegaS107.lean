module

public import Certificates.Data.OmegaB0
public import Certificates.Data.OmegaF1051

public section

namespace Certificates.OmegaS107

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ClassicalInvolution.Q3.TA3.Check

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def gensT0 (_ : Unit := ()) : List P45 := [tab syl1, tab syl2, tab syl3]

@[expose] def cnt (L : List P45) (a : P45) : ℕ :=
  (L.filter fun g => decide (g * a = a * g)).length

@[expose] def wList (A0 P0 T0 : List P45) : List P45 :=
  (A0.filter fun w => (gensT0 ()).all fun g => memB T0 (w * g * w⁻¹)).filter fun w =>
    !memB P0 w

@[expose] def tList (T0 : List P45) (w : P45) : List P45 := T0 ++ T0.map fun a => a * w

@[expose] def outInv (T0 : List P45) (w : P45) : List P45 :=
  (T0.map fun a => a * w).filter fun y => decide (y * y = 1)

@[expose] def centIn (T : List P45) (y : P45) : List P45 :=
  T.filter fun g => decide (g * y = y * g)

@[expose] def b2List (Q : List P45) (y2 : P45) : List P45 :=
  let C := Q.filter fun q => decide (q * y2 = y2 * q)
  C ++ C.map fun c => c * y2

@[expose] def conjList (T : List P45) (y : P45) : List P45 :=
  (1 :: T.map fun g => g * y * g⁻¹).dedup

@[expose] def prod2 (cl : List P45) : List P45 := cl.flatMap fun c => cl.map fun d => c * d

@[expose] def b2Group (T T0 Q B2 : List P45) : Bool :=
  decide (B2.length = 16 ∧ B2.Nodup) && decide ((1 : P45) ∈ B2) &&
    (B2.all fun a => memB T a && decide (a * a = 1) && (!memB T0 a || memB Q a) &&
      (B2.all fun b => decide (a * b = b * a) && memB B2 (a * b))) &&
    T.all fun g => B2.all fun b => memB B2 (g * b * g⁻¹)

@[expose] def outerChk (T T0 B2 : List P45) (y : P45) : Bool :=
  (memB B2 y || T.any fun g => decide ((g * y * g⁻¹) * y ≠ y * (g * y * g⁻¹))) &&
    (memB B2 y || (decide ((centIn T y).length = 16) &&
      (centIn T y).any fun y' => memB B2 y' && !memB T0 y')) &&
    (!memB B2 y || (let P2 := prod2 (conjList T y)
      B2.all fun b => P2.any fun c => P2.any fun d => decide (b = c * d)))

@[expose] def wChk (T0 Q B0 L1440 : List P45) (w : P45) : Bool :=
  let T := tList T0 w
  decide T.Nodup && (T.all fun g => B0.all fun b => memB B0 (g * b * g⁻¹)) &&
    (outInv T0 w).any fun y2 =>
      memB L1440 y2 && !memB T0 y2 &&
        (let B2 := b2List Q y2
         b2Group T T0 Q B2 && (outInv T0 w).all (outerChk T T0 B2))

@[expose] def l1440 (A0 ws : List P45) : List P45 :=
  (ws.filter fun y => decide (y * y = 1)).filter fun y => decide (cnt A0 y = 1440)

@[expose] def b0List (_ : Unit := ()) : List P45 :=
  Certificates.OmegaB0.bElems (Certificates.OmegaB0.phiTable (Certificates.OmegaB0.bl ()))
    (Certificates.OmegaB0.allVecs ())

@[expose] def check (_ : Unit := ()) : Bool :=
  let A0 := elemsT QA45
  let T0 := elemsT QT0
  let Q := Certificates.OmegaF1051.q0l ()
  let ws := wList A0 (elemsT QP45) T0
  (Q.all fun q => memB T0 q) && ((gensT0 ()).all fun g => memB T0 g) &&
    decide (ws.length = 192) && ws.all (wChk T0 Q (b0List ()) (l1440 A0 ws))

end Certificates.OmegaS107
