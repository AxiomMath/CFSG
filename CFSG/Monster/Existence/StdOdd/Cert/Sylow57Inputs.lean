module

public import CFSG.Monster.Existence.StdOdd.Cert.RepsInputs
public import CFSG.LieType.Chevalley.C2E6StdMatrixModelInputs
public import CFSG.Monster.Existence.StdOdd.Cert.Sylow57Data

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.MatrixModel

@[expose] def sylowFusionCheck (p : ℕ) (X Y : Native.Mat) (C r : ℕ → Native.Mat) : Bool :=
  Native.ordP Y p && Native.eqM (Native.mul X Y) (Native.mul Y X) &&
    (List.range p).all (fun k => !Native.eqM (Native.pow X k) Y) &&
    (List.range p).all fun i => Native.eqM (Native.mul (C i) (r i))
      (Native.mul (Native.mul (Native.pow X i) Y) (C i))

@[expose] def sylow5Check : Bool :=
  let V := Native.slpRun #[nativeAB.1, nativeAB.2] sylow5Prog
  let X := Native.wordMat nativeAB.1 nativeAB.2 repWord5
  sylowFusionCheck 5 X (V.getD sylow5Y Native.one)
    (fun i => V.getD (sylow5Conj.getD i 0) Native.one) fun _ => X

@[expose] def sylow7Check : Bool :=
  let V := Native.slpRun #[nativeAB.1, nativeAB.2] sylow7Prog
  let X := Native.wordMat nativeAB.1 nativeAB.2 repWord7B
  let XA := Native.wordMat nativeAB.1 nativeAB.2 repWord7A
  sylowFusionCheck 7 X (V.getD sylow7Z Native.one)
    (fun i => V.getD (sylow7Conj.getD i 0) Native.one)
    fun i => if sylow7IsA.getD i false then XA else X

end CFSG.Monster.Existence.StdOdd.Cert
