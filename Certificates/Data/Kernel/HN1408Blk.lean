module

public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.Certificates.Kernel.Lie.CT.Core

public section

namespace CFSG.KC.Blk

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim
open CFSG.KLie.CT (andB orB notB anyN)

@[expose] noncomputable def blkLeK (N wb B k : Nat) : Bool :=
  allN N fun p => Nat.ble (pg wb (mask wb) B p) k

@[expose] noncomputable def blkSurjK (N wb B k : Nat) : Bool :=
  allN k fun j => anyN N fun p => Nat.beq (pg wb (mask wb) B p) j

@[expose] noncomputable def blkMapK (N wt wb B k T L : Nat) : Bool :=
  allN N fun p => strictB (pg wb (mask wb) B p) fun b => strictB (pg wt (mask wt) T p) fun t =>
    bIf(Nat.blt b k, Nat.beq (pg wb (mask wb) B t) (pg wb (mask wb) L b),
      Nat.ble k (pg wb (mask wb) B t))

@[expose] noncomputable def blkTrivK (N wt wb B T : Nat) : Bool :=
  allN N fun p => Nat.beq (pg wb (mask wb) B (pg wt (mask wt) T p)) (pg wb (mask wb) B p)

end CFSG.KC.Blk

end
