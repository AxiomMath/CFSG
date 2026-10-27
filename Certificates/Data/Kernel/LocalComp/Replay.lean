module

public import Certificates.Data.Kernel.LocalQT.Sec
public import Certificates.Data.CFSGNative.SectionRank.Elem3

public section

namespace CFSG.KC.LocalComp.Replay

open CFSG.KC.LQT CFSG.SectionRank.Native

@[expose] def expoFail : Nat := 2 ^ 64

@[expose] noncomputable def expoK (P : Nat → Nat) (a : Nat) : Nat → Nat → Nat
  | 0, _ => expoFail
  | f + 1, t => if t = a then 1 else if t = 2 then 0 else if t < 2 then expoFail else
      expoK P a f (Nat.land (P t) 1048575) + expoK P a f (Nat.shiftRight (P t) 20)

@[expose] noncomputable def replayK (c : Lay) (V P T : Nat → Nat) (N : Nat) :
    List Op → Nat → List Nat → Bool × List Nat
  | [], _, R => (true, R)
  | .mul i j k :: ops, s, R =>
    let r := replayK c V P T N ops (s + 1) (R.set k (T s))
    (decide (3 ≤ T s) && decide (T s < N) &&
      Nat.beq (P (T s)) (R.getD i 0 + 1048576 * R.getD j 0) && r.1, r.2)
  | .pow e i k :: ops, s, R =>
    let r := replayK c V P T N ops (s + 1) (R.set k (T s))
    ((if e = 0 then Nat.beq (T s) 2
      else decide (T s < N) && decide (e < expoFail) &&
        Nat.beq (expoK P (R.getD i 0) 64 (T s)) e) && r.1, r.2)

@[expose] noncomputable def replayOK (c : Lay) (V P T : Nat → Nat) (N : Nat) (D : Data)
    (O W : Nat → Nat) : Bool :=
  let r := replayK c V P T N D.prog 0
    ((List.range D.nregs).map fun x => if x = 0 then 0 else if x = 1 then 1 else 2)
  decide (N ≤ 1048576) && decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) && D.outs.all (decide <| · < D.nregs) &&
    r.1 && (List.range D.outs.length).all (fun i => Nat.beq (O i) (r.2.getD (D.outs.getD i 0) 0)) &&
    (List.range (3 ^ D.outs.length - 1)).all fun n => D.tests.contains (W (n + 1))

end CFSG.KC.LocalComp.Replay

end
