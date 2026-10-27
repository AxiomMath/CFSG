
module

public import Certificates.Data.Kernel.HMathieu.PredHF
public import Certificates.Data.Kernel.HMathieu.Tab
public import Certificates.Data.Kernel.HMathieu.Avoid
public import CFSG.Quasithin.Background.HMathieuSyl24
public import CFSG.Quasithin.Background.HMathieuPred
public import CFSG.Quasithin.AppendixH.H14.H141C1Inputs
public import CFSG.Quasithin.AppendixH.H16.H165Inputs

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.AppendixH.H14

@[expose] def xiCandsK (Mc : List (List Nat)) (m : Nat) (S : List Nat) : List Nat :=
  (S.filter (· != m)).flatMap fun s => fixMasks 11 actM [Mc.getD s []]

@[expose] def pred24K (Mc : List (List Nat)) (L S : List Nat) (st : List (List Nat) × List Nat) :
    Bool :=
  let k := L.length
  let F := st.2
  let d := Nat.log 2 F.length
  decide (k ≤ 6) && (k == 0 || !decide (11 - d ≤ k + 1) || avoidK 11 3 o2Masks24 F) &&
    (k != 1 || decide (4 ≤ 11 - d)) &&
    (k != 6 || indepCheck 11 (xiCandsK Mc 191 S) (pickBasis (xiCandsK Mc 191 S)) || d == 3)

@[expose] noncomputable def predH165K (E P L S : List Nat) (st : List (List Nat) × List Nat) :
    Bool :=
  predHF24K E P L S st &&
    (L.length != 6 || decide (7 < 11 - Nat.log 2 st.2.length) ||
      S.all fun s => ksRefArrs.contains (unpk (P.getD s 0)))

@[expose] def maskOf (n : Nat) (f : Nat → Bool) : Nat :=
  (List.range n).foldr (fun k acc => if f k then acc ||| 1 <<< k else acc) 0

@[expose] def c1CompL (a b : Array Nat) : Array Nat :=
  ((List.range 24).map fun i => a[b[i]!]!).toArray

@[expose] def c1ConjL (a t : Array Nat) : Array Nat := c1CompL (c1CompL a t) (invArr a)

@[expose] noncomputable def c1MaskS (P : List Nat) : Nat :=
  maskOf 192 fun k => inTab64 tabS (unpk (P.getD k 0))

@[expose] noncomputable def c1MaskT (P : List Nat) : Nat :=
  maskOf 192 fun k => inTab64 tabT (unpk (P.getD k 0))

@[expose] noncomputable def c1MaskF (P : List Nat) : List Nat :=
  c1Fuse.map fun cs => maskOf 192 fun k =>
    inTab64 (if cs.2 then tabS else tabT) (c1ConjL cs.1 (unpk (P.getD k 0)))

@[expose] def predC1K (mS mT : Nat) (mF : List Nat) (L S : List Nat) : Bool :=
  decide (L.length ≤ 6) &&
    (decide (L.length < 5) || S.all mS.testBit || S.all mT.testBit ||
      (L.length == 5 && mF.any fun mf => S.all mf.testBit))

end CFSG.KC.HMathieu

end
