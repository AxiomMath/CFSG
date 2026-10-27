module

public import Certificates.Data.Kernel.CertF8.Pack
public import Certificates.Data.Kernel.CertF8.Lane

public section

namespace CFSG.KC.CertF8

open CFSG.KC.G28 (letN)

@[expose] def M9 : Nat :=
  484012527344627268220161489275239119442527101959318669107755491375532730149768820294161254522980518570641235667350566221822632161069963228899307544230710700423888008118785

@[expose] def L8 : Nat :=
  52374249726338269920222125828018069694904588741968191740379635527817564034522288814292816431204049121484472467000179395471715146806010973164294207700993

@[expose] def F72 : Nat := 4722366482869645213695

@[expose] noncomputable def mulS512 (a b : Nat) : Nat :=
  letN a fun a => letN b fun b => letN (lin M9 PX9 b) fun b1 => letN (lin M9 PX9 b1) fun b2 =>
  letN (lin M9 PS9 b) fun b3 => letN (lin M9 PX9 b3) fun b4 => letN (lin M9 PX9 b4) fun b5 =>
  letN (lin M9 PS9 b3) fun b6 => letN (lin M9 PX9 b6) fun b7 => letN (lin M9 PX9 b7) fun b8 =>
    mulG 8 9 72 L8 F72 a [b, b1, b2, b3, b4, b5, b6, b7, b8]

@[expose] noncomputable def frobS (a : Nat) : Nat := letN a fun a => lin M9 PF9 a

@[expose] noncomputable def frobK (n a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) a (fun _ acc => frobS acc) n

@[expose] noncomputable def mulPr (p q : Nat × Nat) : Nat × Nat :=
  (mulS512 p.1 (frobK p.2 q.1), Nat.mod (Nat.add p.2 q.2) 3)

end CFSG.KC.CertF8

end
