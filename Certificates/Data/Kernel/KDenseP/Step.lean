module

public import Certificates.Data.Kernel.KDenseP.Mono

public section

namespace CFSG.KC.KDenseP

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.KDense
open CFSG.Monster.AxisCount

@[expose] noncomputable def monoKeyStep (n : Nat) (MT : MonoTab) (ok : Bool) (key : List Nat) (X A W : Nat) : St :=
  Prod.rec (motive := fun _ => St) (fun f k => (andB ok f, monoStepN n (MT.ents k) X A W))
    (findIdx key MT.keys)

@[expose] noncomputable def stepN (n lg : Nat) (F : Fix) (MT : MonoTab) (g : Native.Gen) (s : St) : St :=
  Prod.rec (motive := fun _ => St) (fun ok r => Prod.rec (motive := fun _ => St) (fun X r2 =>
    Prod.rec (motive := fun _ => St) (fun A W =>
      Native.Gen.rec (motive := fun _ => St)
        (fun q => Prod.rec (motive := fun _ => St) (fun qs r3 => Prod.rec (motive := fun _ => St)
          (fun qa qd => Prod.rec (motive := fun _ => St) (fun f r4 => (andB ok f, r4))
            (rhoStepN n F (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) qs) qa qd X A W)) r3) q)
        (fun arr => monoKeyStep n MT ok (arrList arr) X A W)
        (fun a => monoKeyStep n MT ok [a] X A W)
        (Prod.rec (motive := fun _ => St) (fun X' r5 => (ok, X', r5)) (xiStepN n lg F X A W))
        (Prod.rec (motive := fun _ => St) (fun X' r5 => (ok, X', r5)) (tauStepN n lg F X A W)) g) r2) r) s

@[expose] noncomputable def runN (n lg : Nat) (F : Fix) (MT : MonoTab) (w : List Native.Gen) (i m : Nat)
    (s : St) : St :=
  List.rec (motive := fun _ => Nat → Nat → St → St) (fun _ _ t => t)
    (fun g _ ih i' m' t => Bool.rec (motive := fun _ => St)
      (Bool.rec (motive := fun _ => St)
        (forceSt (stepN n lg F MT g t) (fun t' => ih i' (Nat.sub m' (nat_lit 1)) t')) t
        (Nat.beq m' (nat_lit 0)))
      (ih (Nat.sub i' (nat_lit 1)) m' t) (Nat.blt (nat_lit 0) i')) w i m s

end CFSG.KC.KDenseP

end
