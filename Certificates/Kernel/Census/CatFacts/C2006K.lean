module

public import Certificates.Data.Kernel.Census.CatFacts.PkWord
public import Certificates.Data.Kernel.Census.CatFacts.C2006Lit
public import Certificates.Data.Kernel.Census.CatFacts.C2006Sub
public import CFSG.GH74.KGroups.A6Inputs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelCatFacts

open CFSG.Certificates.Kernel.PkEnum

local notation "V10" => VP 10

@[expose] def rep2006 (a : V10) (k : Nat) : List V10 :=
  Nat.rec (motive := fun _ => List V10) [] (fun _ l => a :: l) k

@[expose] def comm2006 (a b : V10) : Bool := eqW [a, b] [b, a]

@[expose] def sq2006 (a : V10) : Bool := isOneW [a, a]

@[expose] def fix2006 (P : List V10) (s : V10) : Nat := (P.filter fun g => comm2006 g s).length

@[expose] def cent2006 (L C : List V10) : Nat :=
  (L.filter fun g => C.all fun y => comm2006 y g).length

@[expose] def pow15K2006 (a : V10) : Bool := forceV (mulV a (mulV a a)) fun c => isOneW (rep2006 c 5)

@[expose] def pow120K2006 (a : V10) : Bool :=
  forceV (mulV a a) fun b => forceV (mulV b b) fun c => forceV (mulV c c) pow15K2006

@[expose] def pow32K2006 (a : V10) : Bool :=
  forceV (mulV a a) fun b => forceV (mulV b b) fun c => forceV (mulV c c) fun d =>
    forceV (mulV d d) sq2006

@[expose] def pow8K2006 (a : V10) : Bool := forceV (mulV a a) fun b => forceV (mulV b b) sq2006

@[expose] def cmt2006(o n : V10) : V10 := mulV (mulV (mulV o n) (invV o)) (invV n)

@[expose] def expK2006 (A : List V10) : Bool := A.all pow120K2006

@[expose] def diagK2006 (A P : List V10) : Bool :=
  forceL (A.filter sq2006) fun I => forceL (A.filter fun o => !isOneW [o] && pow15K2006 o) fun O =>
    I.all fun s => forceL (P.filter fun n => comm2006 n s) fun Cs => decide (Cs.length = 10) ||
      O.all fun o => !comm2006 o s || Cs.any fun n => !forceV (cmt2006 o n) pow15K2006

@[expose] def innerK2006 (A P : List V10) : Bool :=
  forceL (A.filter fun a => !pow32K2006 a) fun N =>
    (P.filter fun x => sq2006 x && !isOneW [x]).all fun x =>
      forceL (P.filter fun y => comm2006 x y) fun C =>
        decide (C.length = 8) && N.all (fun a => !comm2006 a x) &&
          (decide (cent2006 A C = 4) && decide (cent2006 P C = 2))

@[expose] def diagI2006 (A : List V10) : List V10 := A.filter sq2006

@[expose] def diagO2006 (A : List V10) : List V10 := A.filter fun o => !isOneW [o] && pow15K2006 o

@[expose] def diagX2006 (P O : List V10) (s : V10) : Bool :=
  forceL (P.filter fun n => comm2006 n s) fun Cs => decide (Cs.length = 10) ||
    O.all fun o => !comm2006 o s || Cs.any fun n => !forceV (cmt2006 o n) pow15K2006

@[expose] def diagC2006 (j : Nat) (P O I : List V10) : Bool :=
  ((I.drop (j * 28)).take 28).all (diagX2006 P O)

@[expose] def innerN2006 (A : List V10) : List V10 := A.filter fun a => !pow32K2006 a

@[expose] def innerE2006 (A : List V10) : List V10 := A.filter fun a => !pow8K2006 a

@[expose] def innerI2006(P : List V10) : List V10 := P.filter fun x => sq2006 x && !isOneW [x]

@[expose] def innerX2006 (A P N : List V10) (x : V10) : Bool :=
  forceL (P.filter fun y => comm2006 x y) fun C =>
    decide (C.length = 8) && N.all (fun a => !comm2006 a x) &&
      (decide (cent2006 A C.reverse = 4) && decide (cent2006 P C.reverse = 2))

@[expose] def innerC2006 (j : Nat) (A P N X : List V10) : Bool :=
  ((X.drop (j * 24)).take 24).all (innerX2006 A P N)

@[expose] def noCommK2006 (A P : List V10) : Bool :=
  forceL (A.filter sq2006) fun I =>
    I.all fun s₁ => !decide (fix2006 P s₁ = 10) ||
      I.all fun s₂ => !comm2006 s₁ s₂ || P.any (fun g => eqW [g] [s₂]) ||
        !decide (fix2006 P s₂ % 8 = 0)

@[expose] def ncF2006 (P I : List V10) : List V10 := I.filter fun s => decide (fix2006 P s = 10)

@[expose] def ncB2006 (P I : List V10) : List V10 :=
  I.filter fun s => !(P.any (fun g => eqW [g] [s]) || !decide (fix2006 P s % 8 = 0))

@[expose] def ncC2006 (F B : List V10) : Bool := F.all fun s₁ => B.all fun s₂ => !comm2006 s₁ s₂

theorem pkOK2006 {p : Nat × Nat} (h : ((List.range 10).all fun i =>
    decide (CFSG.KS.PK.fd (wd 10) p.1 i < 10 ∧ CFSG.KS.PK.fd (wd 10) p.2 i < 10 ∧
      CFSG.KS.PK.fd (wd 10) p.2 (CFSG.KS.PK.fd (wd 10) p.1 i) = i ∧
      CFSG.KS.PK.fd (wd 10) p.1 (CFSG.KS.PK.fd (wd 10) p.2 i) = i)) = true) : PkOK 10 p :=
  fun i hi => of_decide_eq_true (List.all_eq_true.1 h i (List.mem_range.2 hi))

@[expose] def mkV2006 (p : Nat × Nat) : V10 :=
  if h : ((List.range 10).all fun i =>
      decide (CFSG.KS.PK.fd (wd 10) p.1 i < 10 ∧ CFSG.KS.PK.fd (wd 10) p.2 i < 10 ∧
        CFSG.KS.PK.fd (wd 10) p.2 (CFSG.KS.PK.fd (wd 10) p.1 i) = i ∧
        CFSG.KS.PK.fd (wd 10) p.1 (CFSG.KS.PK.fd (wd 10) p.2 i) = i)) = true then
    ⟨p, pkOK2006 h⟩
  else oneV 10

@[expose] def A2006 : List V10 := lit2006A.map mkV2006

@[expose] def P2006 : List V10 := lit2006P.map mkV2006

@[expose] def I2006 : List V10 := lit2006I.map mkV2006

@[expose] def O2006 : List V10 := lit2006O.map mkV2006

@[expose] def X2006 : List V10 := lit2006X.map mkV2006

@[expose] def N2006 : List V10 := lit2006N.map mkV2006

@[expose] def F2006 : List V10 := lit2006F.map mkV2006

@[expose] def B2006 : List V10 := lit2006B.map mkV2006

open CFSG.GH74.KGroups.A6

theorem enumA2006 : enumV (strongV QA) QA.base = A2006 := by
  decide +kernel

theorem enumP2006 : enumV (strongV QP) QP.base = P2006 := by
  decide +kernel

theorem exp2006K : forceL A2006 expK2006 = true := by
  decide +kernel

theorem subI2006 : diagI2006 A2006 = I2006 := by
  decide +kernel

theorem subO2006 : diagO2006 A2006 = O2006 := by
  decide +kernel

theorem subX2006 : innerI2006 P2006 = X2006 := by
  decide +kernel

theorem subN2006 : innerE2006 A2006 = N2006 := by
  decide +kernel

theorem diagLen2006 : I2006.length ≤ 4 * 28 := by
  decide +kernel

theorem diag2006K0 : forceL P2006 (fun P => forceL O2006 (fun O => forceL I2006 (diagC2006 0 P O))) =
    true := by
  decide +kernel

theorem diag2006K1 : forceL P2006 (fun P => forceL O2006 (fun O => forceL I2006 (diagC2006 1 P O))) =
    true := by
  decide +kernel

theorem diag2006K2 : forceL P2006 (fun P => forceL O2006 (fun O => forceL I2006 (diagC2006 2 P O))) =
    true := by
  decide +kernel

theorem diag2006K3 : forceL P2006 (fun P => forceL O2006 (fun O => forceL I2006 (diagC2006 3 P O))) =
    true := by
  decide +kernel

theorem innerLen2006 : X2006.length ≤ 2 * 24 := by
  decide +kernel

theorem inner2006K0 : forceL A2006 (fun A => forceL P2006 (fun P => forceL N2006 (fun N =>
    forceL X2006 (innerC2006 0 A P N)))) = true := by
  decide +kernel

theorem inner2006K1 : forceL A2006 (fun A => forceL P2006 (fun P => forceL N2006 (fun N =>
    forceL X2006 (innerC2006 1 A P N)))) = true := by
  decide +kernel

theorem subFB2006 :
    forceL P2006 (fun P => forceL I2006 fun I => (ncF2006 P I, ncB2006 P I)) = (F2006, B2006) := by
  decide +kernel

theorem noComm2006C : forceL F2006 (fun F => forceL B2006 (ncC2006 F)) = true := by
  decide +kernel

end CertificateChecks.KernelCatFacts
