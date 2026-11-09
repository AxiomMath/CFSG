module

public import Certificates.Data.Kernel.SporSch.HNXPt

public section

namespace CFSG.KC.LL.HNX

open CFSG.KC.Loop CFSG.KC.LL

@[expose] noncomputable def sOnes (w n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (Nat.mul w i))) n

@[expose] noncomputable def sKeep (RB LW i : Nat) : Nat :=
  Nat.mul (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul LW (Nat.shiftLeft (nat_lit 1) i))) (nat_lit 1))
    (sOnes (Nat.mul RB (Nat.shiftLeft (nat_lit 2) i)) (Nat.shiftRight (nat_lit 32) i))

@[expose] noncomputable def sLeafA (L RB Q LW g : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    (Nat.land (Nat.shiftRight L (Nat.mul (Nat.mul (nat_lit 3) Q) g))
      (Nat.mul (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 3) Q)) (nat_lit 1))
        (sOnes RB (nat_lit 64))))
    (fun i x => strictN x (fun x => strictN (Nat.land x (sKeep RB LW i)) (fun k =>
      Nat.lor k (Nat.shiftRight (Nat.sub x k)
        (Nat.mul (Nat.sub RB LW) (Nat.shiftLeft (nat_lit 1) i))))))
    (nat_lit 6)

@[expose] noncomputable def sPre (L RB Q LW NG CMS W J GO : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun g acc0 => strictN (sLeafA L RB Q LW g) (fun A =>
      strictN (fldW GO (Nat.mul (nat_lit 8) g) (nat_lit 8)) (fun t0 =>
      Nat.rec (motive := fun _ => Nat) acc0
        (fun k acc => strictN (Nat.add t0 k) (fun t =>
          Nat.add acc (Nat.mul
            (Nat.land (Nat.shiftRight A
              (Nat.mul (nat_lit 3) (fldW J (Nat.mul (nat_lit 8) t) (nat_lit 8)))) CMS)
            (fldW W (Nat.mul LW t) LW))))
        (Nat.sub (fldW GO (Nat.mul (nat_lit 8) (Nat.succ g)) (nat_lit 8)) t0)))) NG

@[expose] noncomputable def fixLeafS (T : Nat → Nat)
    (RB CM3 M G Q LW NG CMS SL SH W J GO b c : Nat) : Nat :=
  strictN (CFSG.KC.Ord.redP (nat_lit 13) SL SH (nat_lit 5) (nat_lit 9)
      (sPre (T b) RB Q LW NG CMS W J GO)) (fun Y =>
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun r acc => Nat.add acc (nIf(Nat.beq (fldW Y (Nat.mul LW r) LW) (nat_lit 0),
        nIf(fixAt T RB CM3 M G (Nat.add (Nat.shiftLeft b (nat_lit 6)) r), nat_lit 1, nat_lit 0),
        nat_lit 0))) c)

@[expose] noncomputable def fixSumS (T : Nat → Nat) (CM3 M G F W J GO lo n : Nat) : Nat :=
  strictN (Nat.mul (nat_lit 13) F) (fun LW =>
  strictN (Nat.div LW (nat_lit 3)) (fun Q =>
  strictN (sOnes (nat_lit 13) (Nat.mul (nat_lit 64) F)) (fun SL =>
  strictN (Nat.mul (nat_lit 7) (sOnes LW (nat_lit 64))) (fun CMS =>
  strictN (Nat.div (Nat.add (nat_lit 132) Q) Q) (fun NG =>
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => strictN acc (fun a => Nat.add a
        (fixLeafS T (nat_lit 464) CM3 M G Q LW NG CMS SL (Nat.shiftLeft SL (nat_lit 12)) W J GO
          (Nat.add lo i) (CFSG.KS.SporSch.hnxC (Nat.add lo i))))) n)))))

@[expose] noncomputable def sCnt (GO g : Nat) : Nat :=
  Nat.sub (fldW GO (Nat.mul (nat_lit 8) (Nat.succ g)) (nat_lit 8)) (fldW GO (Nat.mul (nat_lit 8) g) (nat_lit 8))

@[expose] noncomputable def sTermOK (W J GO g k : Nat) : Bool :=
  letB (Nat.add (fldW GO (Nat.mul (nat_lit 8) g) (nat_lit 8)) k) (fun t =>
  letB (fldW J (Nat.mul (nat_lit 8) t) (nat_lit 8)) (fun j =>
  bAnd(Nat.blt j (nat_lit 69), bAnd(Nat.blt (Nat.add (Nat.mul (nat_lit 69) g) j) (nat_lit 133),
    CFSG.KC.Enum.allN (nat_lit 16) (fun s =>
      Nat.blt (fldW W (Nat.add (Nat.mul (nat_lit 208) t) (Nat.mul (nat_lit 13) s)) (nat_lit 13))
        (nat_lit 5))))))

@[expose] noncomputable def sColSum (W J GO s j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun g acc => Nat.rec (motive := fun _ => Nat) acc
      (fun k acc2 => Nat.add acc2
        (nIf(Nat.beq (Nat.add (Nat.mul (nat_lit 69) g)
            (fldW J (Nat.mul (nat_lit 8) (Nat.add (fldW GO (Nat.mul (nat_lit 8) g) (nat_lit 8)) k))
              (nat_lit 8))) j,
          fldW W (Nat.add (Nat.mul (nat_lit 208) (Nat.add (fldW GO (Nat.mul (nat_lit 8) g) (nat_lit 8)) k))
            (Nat.mul (nat_lit 13) s)) (nat_lit 13), nat_lit 0)))
      (sCnt GO g)) (nat_lit 2)

@[expose] noncomputable def sOKc (SC : Nat) : Bool :=
  bAnd(Nat.blt SC (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 1729) (nat_lit 64))),
    CFSG.KC.Enum.allN (nat_lit 64) (fun s =>
      Nat.blt (fldW SC (Nat.mul (nat_lit 1729) s) (nat_lit 1729)) (Nat.shiftLeft (nat_lit 1) (nat_lit 399))))

@[expose] noncomputable def sOKt (W J GO : Nat) : Bool :=
  bAnd(Nat.ble (Nat.add (sCnt GO (nat_lit 0)) (sCnt GO (nat_lit 1))) (nat_lit 146),
    CFSG.KC.Enum.allN (nat_lit 2) (fun g => CFSG.KC.Enum.allN (sCnt GO g) (sTermOK W J GO g)))

@[expose] noncomputable def sOKd (W J GO SD : Nat) : Bool :=
  CFSG.KC.Enum.allN (nat_lit 16) (fun s => CFSG.KC.Enum.allN (nat_lit 133) (fun j =>
    Nat.beq (Nat.mod (sColSum W J GO s j) (nat_lit 5))
      (fldW SD (Nat.add (Nat.mul (nat_lit 1729) s) (Nat.mul (nat_lit 13) j)) (nat_lit 13))))

@[expose] noncomputable def sPreOK (CM3 V W J GO SC SD : Nat) : Bool :=
  bAnd(sOKc SC, bAnd(sOKt W J GO, bAnd(sOKd W J GO SD, Nat.beq (mulC CM3 SC V) SD)))

end CFSG.KC.LL.HNX

end
