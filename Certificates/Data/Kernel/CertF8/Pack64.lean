module

public import Certificates.Data.Kernel.CertF8.Pack
public import Certificates.Data.Kernel.CertF8.Lane

public section

namespace CFSG.KC.CertF8

open CFSG.KC.G28 (letN)

@[expose] def M6 : Nat :=
  625428669784039352575857779367358949286979988420086455046798308003900345579320803355782004045792311758835364925505

@[expose] def L8w : Nat :=
  139984046386113260483076552323936769829629381004690729274846099254769870219648685538816173958204751873

@[expose] def F48 : Nat := 281474976710655

@[expose] noncomputable def mulS64 (a b : Nat) : Nat :=
  letN a fun a => letN b fun b => letN (lin M6 PX6 b) fun b1 => letN (lin M6 PX6 b1) fun b2 =>
  letN (lin M6 PW6 b) fun b3 => letN (lin M6 PX6 b3) fun b4 => letN (lin M6 PX6 b4) fun b5 =>
    mulG 8 6 48 L8w F48 a [b, b1, b2, b3, b4, b5]

@[expose] noncomputable def frobS64 (a : Nat) : Nat := letN a fun a => lin M6 PF6 a

@[expose] noncomputable def frobK64 (n a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) a (fun _ acc => frobS64 acc) n

@[expose] noncomputable def mulPr64 (p q : Nat × Nat) : Nat × Nat :=
  (mulS64 p.1 (frobK64 p.2 q.1), Nat.mod (Nat.add p.2 q.2) 3)

end CFSG.KC.CertF8

end
