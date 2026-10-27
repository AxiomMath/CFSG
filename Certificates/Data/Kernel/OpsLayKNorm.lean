module

public import Certificates.Data.Kernel.OpsLayK
public import Certificates.Data.CoverCenterThreeON

public section

namespace CFSG.KC.OpsLayK

open CFSG.KC.LQT CFSG.SectionRank.Native

@[expose] noncomputable def powProdK (c : Lay) : List Nat → (Nat → Nat) → Nat
  | [], _ => c.ONE
  | X :: xs, f => c.mul (powK c X (f 0)) (powProdK c xs fun k => f (k + 1))

@[expose] noncomputable def normCK (c : Lay) (A B : Nat) (D : NormData) : Bool :=
  let r := D.base.outs.length
  progOK D.base.nregs D.base.prog && D.base.outs.all (decide <| · < D.base.nregs) &&
    D.base.tests.all (decide <| · < c.d) && decide (0 < D.og) && decide (D.og < 65536) &&
    D.gens.all (decide <| · < D.base.nregs) &&
    ((List.range D.gens.length).all fun j => (List.range r).all fun i =>
      (List.range r).all fun k => decide (D.expo j k i < 65536)) &&
  runC c D.base.prog (initR c A B D.base.nregs) fun R =>
    let xs := D.base.outs.map (getR c R)
    elemK c xs D.base.tests &&
      (List.range D.gens.length).all fun j =>
        let G := getR c R (D.gens.getD j 0)
        Nat.beq (powK c G D.og) c.ONE &&
          (List.range r).all fun i =>
            conjK c G (xs.getD i c.ONE) (powProdK c xs fun k => D.expo j k i)

end CFSG.KC.OpsLayK

end
