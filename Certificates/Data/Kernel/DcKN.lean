module

public import Certificates.Data.Kernel.DcK

public section

namespace CFSG.KC.DcK

open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.KC.E64F

namespace DcK

variable (K : DcK)

@[expose] def conjKey2 (i j k : Nat) : Nat :=
  keyNat K.n K.B.length ((ePts K.R K.rt (k + 1) k
    (K.B.map (wordF K.ab (K.reps.getD j [])))).map (wordF K.ab (invW (K.reps.getD i []))))

@[expose] def noHitK (i j : Nat) (P : Nat → Nat) : Bool :=
  (List.range K.R.N).all fun k => memK K.n K.B.length K.R (K.conjKey2 i j k) (P k) == some false

@[expose] def distOKN (I : List Nat) (P : Nat → Nat → Nat → Nat) : Bool :=
  I.length == K.reps.size && (List.range K.reps.size).all (fun j => K.inv j == I.getD j 0) &&
    (List.range K.reps.size).all fun i => (List.range K.reps.size).all fun j =>
      decide (j ≤ i) || I.getD i 0 != I.getD j 0 || K.noHitK i j (P i j)

@[expose] def gd (f : Nat → Nat) (w : List Nat) (q : Nat) : Nat :=
  if q < K.n then f q else wordF K.ab w q

@[expose] def tabsOK (xt xti : Nat → Nat → Nat) (lo len : Nat) : Bool :=
  (List.range' lo len).all fun j => (List.range K.n).all fun p =>
    xt j p == wordF K.ab (K.reps.getD j []) p && xti j p == wordF K.ab (invW (K.reps.getD j [])) p

@[expose] def conjKeyT (xt xti : Nat → Nat → Nat) (i j k : Nat) : Nat :=
  keyNat K.n K.B.length ((ePts K.R K.rt (k + 1) k
    (K.B.map (K.gd (xt j) (K.reps.getD j [])))).map (K.gd (xti i) (invW (K.reps.getD i []))))

@[expose] def noHitKT (xt xti : Nat → Nat → Nat) (i j : Nat) (P : Nat → Nat) : Bool :=
  (List.range K.R.N).all fun k =>
    memK K.n K.B.length K.R (K.conjKeyT xt xti i j k) (P k) == some false

@[expose] def distOKNT (xt xti : Nat → Nat → Nat) (I : List Nat) (P : Nat → Nat → Nat → Nat) :
    Bool :=
  I.length == K.reps.size && (List.range K.reps.size).all (fun j => K.inv j == I.getD j 0) &&
    (List.range K.reps.size).all fun i => (List.range K.reps.size).all fun j =>
      decide (j ≤ i) || I.getD i 0 != I.getD j 0 || K.noHitKT xt xti i j (P i j)

@[expose] def hitT (xt xti : Nat → Nat → Nat) (j : Nat) : Option Nat :=
  cntK (fun k => memK K.n K.B.length K.R (K.conjKeyT xt xti j j k) (K.hpos j k))
    (List.range K.R.N) 0

@[expose] def hitOKT (xt xti : Nat → Nat → Nat) (H : List Nat) : Bool :=
  H.length == K.reps.size &&
    (List.range K.reps.size).all fun j => K.hitT xt xti j == some (H.getD j 0)

end DcK

@[expose] def chkAllKN (K : DcK) (I H : List Nat) (P : Nat → Nat → Nat → Nat) : Bool :=
  K.invOK && K.basicOK && K.labOK && K.distOKN I P && K.edgesOK && K.vsOK && K.hitOK H &&
    K.massOK H

@[expose] def chkAllKT (K : DcK) (I H : List Nat) (P : Nat → Nat → Nat → Nat)
    (xt xti : Nat → Nat → Nat) : Bool :=
  K.invOK && K.basicOK && K.labOK && K.distOKNT xt xti I P && K.edgesOK && K.vsOK &&
    K.hitOKT xt xti H && K.massOK H && K.tabsOK xt xti 0 K.reps.size

end CFSG.KC.DcK

end
