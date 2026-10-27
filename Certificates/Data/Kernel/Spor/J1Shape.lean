module

public import Certificates.Data.Kernel.Spor.Co2Shape
public import CFSG.Sporadic.Schreier.J1CertTypes

public section

namespace CFSG.KS.J1Shape

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2Shape CFSG.Sporadic.Schreier
open CFSG.Monster.B.Mathieu

@[expose] noncomputable def j1ShapeK (r : J1CertificateFile) : Bool :=
  bAnd(Nat.beq r.schemaVersion (nat_lit 1), bAnd(Nat.beq r.prime (nat_lit 11),
  bAnd(Nat.beq r.dimension (nat_lit 7),
  bAnd(Nat.beq (lenL r.vectors) (nat_lit 3080),
  bAnd(allL (fun v => bAnd(Nat.beq (lenL v) (nat_lit 7), allL (fun x => Nat.ble x (nat_lit 10)) v))
    r.vectors,
  bAnd(eqNL r.basisIndices [nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 3, nat_lit 4, nat_lit 5,
    nat_lit 6],
  bAnd(Nat.beq r.chain.degree (nat_lit 3080),
  bAnd(Nat.beq (lenL r.chain.generators) (nat_lit 2),
  bAnd(allL (permL (nat_lit 3080)) r.chain.generators,
  bAnd(allL (permL (nat_lit 3080)) r.chain.strongGenerators,
  bAnd(eqNL (List.rec (motive := fun _ => List Nat) [] (fun s _ ih => List.cons s.prime ih)
      r.sylows) [nat_lit 2, nat_lit 3, nat_lit 5, nat_lit 7, nat_lit 11, nat_lit 19],
    allL (fun s => bAnd(allL (permL (nat_lit 3080)) s.generators,
      allL (fun ng => bAnd(permL (nat_lit 3080) ng.representative,
        Nat.beq ng.chain.degree (nat_lit 3080))) s.normalGeneration)) r.sylows)))))))))))

end CFSG.KS.J1Shape

end
