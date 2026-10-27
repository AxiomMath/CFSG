module

public import Certificates.Data.Kernel.HMathieu.Tab
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatR4In
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatR2In
public import CFSG.Quasithin.AppendixH.H15.CocodeTwoOffDefs24
public import Certificates.Data.SmithB45MatQ
public import Mathlib.Data.Nat.Log

public section

namespace CFSG.KC.HMathieu

open CFSG.KC.Enum CFSG.KS CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H13.Mat
open CFSG.Quasithin.B45Mat CFSG.ASVolI.AppH

@[expose] def chainCommInM (n : Nat) (B : List Nat) (M : List Nat) : Bool :=
  (List.range n).all fun j => (combos B).contains (actM M (2 ^ j) ^^^ 2 ^ j)

@[expose] def predKTK (st : List (List Nat) × List Nat) : Bool :=
  st.1.length != 6 || st.2.length != 8 || st.2 == uTMasks

@[expose] def predMB24K (st : List (List Nat) × List Nat) : Bool :=
  predKTK st && (st.1.length != 6 || st.2.length != 8 || st.1.all (chainCommInM 11 r4L9))

@[expose] noncomputable def t24PresUTK (E : List Nat) : Bool :=
  E.all fun e => uTMasks.all fun m => uTMasks.contains (actP ccECols liftECols e m)

@[expose] noncomputable def t24FixK (E : List Nat) : Bool :=
  ((List.range (2 ^ 11)).filter fun m => E.all fun e => actP ccECols liftECols e m == m) ==
    [0, 1192]

@[expose] noncomputable def predOff24K (P L : List Nat) (st : List (List Nat) × List Nat) : Bool :=
  let k := L.length
  let d := Nat.log 2 st.2.length
  decide (k ≤ 6) && (k == 0 || !decide (11 - d ≤ k + 1) ||
    (k == 4 && L.all fun a => offPts24.all fun i => pg 5 (mask 5) (P.getD a 0) i == i))

@[expose] noncomputable def predQ22inK (P L : List Nat) (Ms : List (List Nat)) : Bool :=
  !(L.all fun a => pg 5 (mask 5) (P.getD a 0) 0 == 0) || predQ 10 actM true Ms

@[expose] def predMB22K (st : List (List Nat) × List Nat) : Bool :=
  (st.1.length != 5 || st.2 == u22Masks) &&
    (st.1.length != 5 || (st.1.all (chainCommInM 10 r2B9) &&
      st.1.any fun M => !(chainCommInM 10 r2W8 M)))

end CFSG.KC.HMathieu

end
