module

public import Certificates.Data.Kernel.KDenseP.Letters

public section

namespace CFSG.KC.KDenseP

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.KDense
open CFSG.Monster.AxisCount

@[expose] noncomputable def tauInvStepN (n lg : Nat) (F : Fix) (X A W : Nat) : Nat × Nat × Nat :=
  (fun L Xp Xq =>
    (fun d2 U =>
      (Nat.lor (negMN SX n F.sgOddUp (Nat.land (Nat.shiftRight W (nat_lit 65536)) L))
        (Nat.lor (Nat.land (rotN SX n (dvN n (nat_lit 3)) (wht6N n lg
            (netN SX n (nat_lit 17) F.pi6 (negMN SX n F.doct X)))) (repN SX n regOct))
          (Nat.lor (expandN n (nat_lit 114688) (Nat.land (addN SA n lg A d2) (repN SA n upA)))
            (expandN n (nat_lit 115712)
              (Nat.land (addN SA n lg A (negMN SA n upA d2)) (repN SA n upA))))),
       Nat.lor (Nat.land A (repN SA n diagA)) (Nat.lor U (transpN n U)),
       Nat.lor (negMN SX n F.sgWLo (Nat.land X L))
         (Nat.shiftLeft (negMN SX n F.sgWUp (Nat.land W L)) (nat_lit 65536))))
      (rotN SA n (dvN n (nat_lit 1)) (addN SA n lg Xp Xq))
      (Nat.land (rotN SA n (dvN n (nat_lit 1)) (addN SA n lg Xp (negMN SA n upA Xq))) (repN SA n upA)))
    (repN SX n lo16) (compactN n (nat_lit 114688) X) (compactN n (nat_lit 115712) X)

@[expose] noncomputable def tauInvSt (n lg : Nat) (F : Fix) (s : St) : St :=
  Prod.rec (motive := fun _ => St) (fun ok r => Prod.rec (motive := fun _ => St) (fun X r2 =>
    Prod.rec (motive := fun _ => St) (fun A W =>
      Prod.rec (motive := fun _ => St) (fun X' r5 => (ok, X', r5)) (tauInvStepN n lg F X A W)) r2) r) s

@[expose] noncomputable def isTauLB (g : Native.Gen) : Bool :=
  Native.Gen.rec (motive := fun _ => Bool) (fun _ => false) (fun _ => false) (fun _ => false) false true g

@[expose] noncomputable def headTauLB (w : List Native.Gen) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun g _ _ => isTauLB g) w

end CFSG.KC.KDenseP

end
