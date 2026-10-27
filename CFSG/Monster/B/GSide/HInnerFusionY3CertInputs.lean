module

public import CFSG.Monster.B.GSide.HInnerFusionI3Cert
public meta import CFSG.Monster.B.GSide.HInnerFusionI3Cert

public section

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B.CTIB CFSG.Monster.B.CTIB.Native CFSG.Monster.B.Max2.Native

@[expose] def yWords : List (List Int) :=
  [[1, 2, 1, -2, -2, 1, 2, 2, 1, -2, 1],
    [-2, -2, -2, 1, 2, 2, 2, 1, -2, 1, 2, 1],
    [1, -2, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 2, 1],
    [1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1],
    [2, 2, 2, 1, 2, 2, 1, -2, 1, 2, 1, -2, -2, 1, -2, -2, -2],
    [2, 1, 2, 2, 1, 2, 2, 1, -2, 1, 2, 1, -2, -2, 1, -2, -2, 1, -2]]

@[expose] def yFlips : List Nat := [0, 16, 0, 0, 0, 0]

@[expose] def yAuts (_ : Unit) : Array (Array Nat) :=
  (yWords.map fun w => wordAut (genInvImgs ()) w).toArray

@[expose] def yAct (gA : Array (Array Nat)) (j n : Nat) : Nat :=
  qmul gArr (qmul gArr (qinv (yFlips.getD j 0)) (autApply gArr (gA.getD j #[]) n))
    (yFlips.getD j 0)

@[expose] def y3CertOK (t : Array Nat) : Bool :=
  let gA := yAuts ()
  let c := natBfs (yAct gA) 6 32 2241
  let A := (liftImgsN 8).toArray
  (List.range 6).all (fun j => yAct gA j 7 == 7) && frameA t 32 &&
    natCertOK (yAct gA) 6 (fun p => decide (p < 2 ^ 23)) 32 c.1 c.2.1 c.2.2.1 c.2.2.2 &&
    c.1.size == 2240 &&
    innerTy t 128 == 1 && autApply gArr A 128 == 128 && qmul gArr 128 9 == qmul gArr 9 128 &&
    qmul gArr (sqCode 8) (qmul gArr (autApply gArr A 9) 9) == 7618823 &&
    innerTy t 7618823 == 3 && qmul gArr 128 7618823 == qmul gArr 7618823 128 &&
    innerTy t (qmul gArr 128 7618823) == 3

end CFSG.Monster.B.GSide
