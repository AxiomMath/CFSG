module

public import Certificates.Data.Kernel.SporSch.SetReplay

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def ptBitsT (t : Nat) : Nat :=
  Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 64) t))
    (Nat.land (Nat.mul (Nat.succ t) (nat_lit 11400714819323198485)) (nat_lit 18446744073709551615))

@[expose] noncomputable def keyK1 (w s P : Nat) : Nat :=
  strictN P (fun p => strictN (mask w) (fun m =>
    foldN s (fun q acc => strictN (pg w m p q) (fun t => Nat.xor acc (ptBitsT t))) (nat_lit 0)))

@[expose] noncomputable def imgK1 (w s G P : Nat) : Nat :=
  strictN G (fun g => strictN P (fun p => strictN (mask w) (fun m =>
    foldN s (fun q acc => strictN (pg w m g (pg w m p q)) (fun t => Nat.xor acc (ptBitsT t)))
      (nat_lit 0))))

@[expose] noncomputable def eltKeyT (n w s x : Nat) : Nat :=
  strictN (mask w) (fun m =>
    foldN s (fun q acc => strictN (pg w m x q) (fun t =>
      nIf(bAnd(Nat.blt t n, bIf(Nat.beq q (nat_lit 0), true,
          Nat.blt (pg w m x (Nat.sub q (nat_lit 1))) t)),
        Nat.xor acc (ptBitsT t), Nat.lor acc (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 64) n)))))
      (nat_lit 0))

@[expose] noncomputable def eltAtK (n w s : Nat) (X KT : Nat → Nat) (c i : Nat) : Bool :=
  bIf(Nat.blt i c, Nat.beq (KT i) (eltKeyT n w s (X i)), true)

@[expose] noncomputable def sortKT (KT SO SOI : Nat → Nat) (c i : Nat) : Bool :=
  strictB (SO i) (fun j => bAnd(Nat.blt j c, bAnd(Nat.beq (SOI j) i,
    bIf(Nat.blt (Nat.succ i) c, Nat.blt (KT j) (KT (SO (Nat.succ i))), true))))

@[expose] noncomputable def sortAtKT (KT SO SOI : Nat → Nat) (c i : Nat) : Bool :=
  bIf(Nat.blt i c, sortKT KT SO SOI c i, true)

@[expose] noncomputable def stepRKT (w s : Nat) (G X W KT : Nat → Nat) (c bound h k cur : Nat) :
    Nat :=
  nIf(Nat.beq cur bound, cur,
  nIf(Nat.blt h cur,
    strictN (imgK1 w s (G k) (X h)) (fun t =>
    strictN fld(W h, Nat.mul (nat_lit 20) k, nat_lit 1048575) (fun j =>
      nIf(bAnd(Nat.blt j cur, Nat.beq (KT j) t), cur,
      nIf(bAnd(Nat.beq j cur, bAnd(Nat.beq (KT j) t, strictB (X j) (fun xj =>
          bAnd(Nat.beq (parX w s xj) h, Nat.beq (labX w s xj) k)))),
        Nat.succ cur, failC)))),
    nIf(Nat.beq cur c, cur, failC)))

@[expose] noncomputable def headRK (w s : Nat) (G X W KT : Nat → Nat) (kg c bound h cur : Nat) :
    Nat :=
  foldUp kg (fun k cur => stepRKT w s G X W KT c bound h k cur) cur

@[expose] noncomputable def runFromK (w s : Nat) (G X W KT : Nat → Nat) (kg c bound : Nat) :
    Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ cur => cur)
    (fun _ ih h cur => strictN (headRK w s G X W KT kg c bound h cur) (fun c' =>
      strictN (Nat.succ h) (fun h' => ih h' c')))

@[expose] noncomputable def fusedK (n w s kg L : Nat) (G : Nat → Nat) (x : Nat) : Nat :=
  strictN (mask w) (fun m =>
    foldN s (fun q acc => strictN (pg w m x q) (fun t =>
      nIf(bAnd(Nat.blt t n, bIf(Nat.beq q (nat_lit 0), true,
          Nat.blt (pg w m x (Nat.sub q (nat_lit 1))) t)),
        Nat.xor acc (foldN kg (fun k a => Nat.lor (Nat.shiftLeft a L) (ptBitsT (pg w m (G k) t)))
          (ptBitsT t)),
        Nat.lor acc (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.mul kg L) (Nat.add (nat_lit 64) n))))))
      (nat_lit 0))

@[expose] noncomputable def stepRKF (w s : Nat) (X W KT : Nat → Nat) (c bound h k cur t : Nat) :
    Nat :=
  nIf(Nat.beq cur bound, cur,
  nIf(Nat.blt h cur,
    strictN fld(W h, Nat.mul (nat_lit 20) k, nat_lit 1048575) (fun j =>
      nIf(bAnd(Nat.blt j cur, Nat.beq (KT j) t), cur,
      nIf(bAnd(Nat.beq j cur, bAnd(Nat.beq (KT j) t, strictB (X j) (fun xj =>
          bAnd(Nat.beq (parX w s xj) h, Nat.beq (labX w s xj) k)))),
        Nat.succ cur, failC))),
    nIf(Nat.beq cur c, cur, failC)))

@[expose] noncomputable def stepFK (w s L ML : Nat) (X W KT : Nat → Nat) (kg c bound h F k cur : Nat) :
    Nat :=
  nIf(bAnd(Nat.beq k (nat_lit 0), Nat.blt h cur),
    nIf(Nat.beq (Nat.shiftRight F (Nat.mul kg L)) (KT h),
      stepRKF w s X W KT c bound h k cur fld(F, Nat.mul k L, ML), failC),
    stepRKF w s X W KT c bound h k cur fld(F, Nat.mul k L, ML))

@[expose] noncomputable def headRF (n w s : Nat) (G X W KT : Nat → Nat) (kg c bound h cur : Nat) :
    Nat :=
  strictN (Nat.add (nat_lit 64) n) (fun L => strictN (mask L) (fun ML =>
  strictN (fusedK n w s kg L G (X h)) (fun F =>
    foldUp kg (fun k cur => stepFK w s L ML X W KT kg c bound h F k cur) cur)))

@[expose] noncomputable def runFromF (n w s : Nat) (G X W KT : Nat → Nat) (kg c bound : Nat) :
    Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ cur => cur)
    (fun _ ih h cur => strictN (headRF n w s G X W KT kg c bound h cur) (fun c' =>
      strictN (Nat.succ h) (fun h' => ih h' c')))

end CFSG.KS.SporSch

end
