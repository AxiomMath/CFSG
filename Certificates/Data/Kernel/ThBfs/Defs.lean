module

public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KC.ThBfs

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos

@[expose] noncomputable def keyAt (R : Nat → Nat) (i : Nat) : Nat :=
  Nat.land (R i) (nat_lit 4294967295)

@[expose] noncomputable def discAt (R : Nat → Nat) (i : Nat) : Nat :=
  Nat.shiftRight (R i) (nat_lit 32)

@[expose] noncomputable def imgAt (A : Nat → Nat → Nat) (nG n : Nat) (R C : Nat → Nat)
    (i e k : Nat) : Bool :=
  letB (Nat.add (Nat.mul nG i) k) fun t => letB (C t) fun c =>
    andB (Nat.blt c n) (andB (Nat.beq (keyAt R c) (A e k))
      (orB (Nat.beq c (nat_lit 0)) (Nat.ble (discAt R c) t)))

@[expose] noncomputable def treeK (nG n : Nat) (R C : Nat → Nat) (i d : Nat) : Bool :=
  impB (Nat.blt (nat_lit 0) i) (andB (Nat.blt d (Nat.mul nG i)) (andB (Nat.beq (C d) i)
    (impB (Nat.blt (Nat.succ i) n) (Nat.blt d (discAt R (Nat.succ i))))))

@[expose] noncomputable def bfsAt (A : Nat → Nat → Nat) (B nG n : Nat) (R C S : Nat → Nat)
    (i : Nat) : Bool :=
  letB (keyAt R i) fun e => letB (discAt R i) fun d =>
    andB (Nat.blt e B) (andB (sortAt n (keyAt R) S i)
      (andB (allN nG fun k => imgAt A nG n R C i e k) (treeK nG n R C i d)))

@[expose] noncomputable def orbTab (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (nat_lit 0xfffdfefcf7f5f6f4fbf9faf8f3f1f2f0bfbdbebcb7b5b6b4bbb9bab8b3b1b2b07f7d7e7c777576747b797a78737172703f3d3e3c373536343b393a3833313230efedeeece7e5e6e4ebe9eae8e3e1e2e0afadaeaca7a5a6a4aba9aaa8a3a1a2a06f6d6e6c676566646b696a68636162602f2d2e2c272526242b292a2823212220dfdddedcd7d5d6d4dbd9dad8d3d1d2d09f9d9e9c979596949b999a98939192905f5d5e5c575556545b595a58535152501f1d1e1c171516141b191a1813111210cfcdceccc7c5c6c4cbc9cac8c3c1c2c08f8d8e8c878586848b898a88838182804f4d4e4c474546444b494a48434142400f0d0e0c070506040b090a0803010200)
    (nat_lit 0xedef7b79ecee7a783331a5a73230a4a6e9eb7f7de8ea7e7c3735a1a33634a0a2e5e77371e4e672703b39adaf3a38acaee1e37775e0e276743f3da9ab3e3ca8aabfbd292bbebc282a6163f7f56062f6f4bbb92d2fbab82c2e6567f3f16466f2f0b7b52123b6b42022696bfffd686afefcb3b12527b2b024266d6ffbf96c6efaf81517838114168280cbc95d5fcac85c5e1113878510128684cfcd595bcecc585a1d1f8b891c1e8a88c3c15557c2c05456191b8f8d181a8e8cc7c55153c6c450524745d1d34644d0d2999b0f0d989a0e0c4341d5d74240d4d69d9f0b099c9e0a084f4dd9db4e4cd8da91930705909206044b49dddf4a48dcde9597030194960200)
    (Nat.beq k (nat_lit 1))

@[expose] noncomputable def orbImg (k c : Nat) : Nat :=
  Nat.mod (Nat.shiftRight (orbTab k) (Nat.mul (nat_lit 8) c)) (nat_lit 256)

@[expose] noncomputable def orbAct (e k : Nat) : Nat :=
  Nat.add (orbImg k (Nat.mod e (nat_lit 256)))
    (Nat.add (Nat.mul (nat_lit 256) (orbImg k (Nat.mod (Nat.div e (nat_lit 256)) (nat_lit 256))))
      (Nat.mul (nat_lit 65536) (orbImg k (Nat.mod (Nat.div e (nat_lit 65536)) (nat_lit 256)))))

end CFSG.KC.ThBfs

end
