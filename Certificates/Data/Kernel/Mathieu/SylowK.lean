module

public import Certificates.Data.Kernel.SporSch.MathieuOC
public import CFSG.Certificates.Kernel.Spor.BindList
public import CFSG.Monster.B.Mathieu.CertData
public import Mathlib.Data.List.Lex
public import CFSG.Certificates.Kernel.Spor.RawSound
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.KC.MathieuK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Mathieu CFSG.KS.M11 CFSG.KS.Prim
open CFSG.KS.SporSch.MOC (powK abWordK abOK)

@[expose] def baseVec (n : Nat) [NeZero n] (B : List Nat) : Vector (Fin n) B.length :=
  ⟨(B.map (Fin.ofNat n)).toArray, by simp⟩

@[expose] noncomputable def unpackL (n w P : Nat) : List Nat :=
  (List.range n).map (pg w (mask w) P)

@[expose] noncomputable def elemOK (n w : Nat) (x : List Nat) : Bool :=
  bindListK n w (packL w x) x &&
    permOK n w (mask w) (n * w) (packL w x) (pinvS n w (mask w) (packL w x)) &&
    canonK n w (mask w) (n * w) (packL w x)

@[expose] noncomputable def repK (n w p : Nat) (LR TRI : Nat → Nat) (BP nb : Nat) (x : List Nat) :
    Bool :=
  elemOK n w x && siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 (packL w x) &&
    ordIs n w (mask w) (pidn n w) (packL w x) (p - 1) &&
    (List.range p).all fun j =>
      j == 0 || decide (x ≤ unpackL n w (powK n w (mask w) (pidn n w) (packL w x) j))

@[expose] noncomputable def conjK (n w A Ai B Bi R : Nat) (wd : List Int) : Nat :=
  strictN (abWordK n w (mask w) (pidn n w) A Ai B Bi wd) fun W =>
    pcomp n w (mask w) (pcomp n w (mask w) (pinvS n w (mask w) W) R) W

@[expose] noncomputable def ngK (n w A Ai B Bi : Nat) (PS : Nat → Nat) (x : List Nat)
    (C : List (List Int)) : Bool :=
  C.all abOK && (List.range C.length).all fun j =>
    Nat.beq (PS j) (conjK n w A Ai B Bi (packL w x) (C.getD j []))

@[expose] noncomputable def bindsL (n w : Nat) (PS : Nat → Nat) : Nat → List (List Nat) → Bool
  | _, [] => true
  | i, l :: S => bindListK n w (PS i) l && bindsL n w PS (i + 1) S

@[expose] noncomputable def ngB (n w N A Ai B Bi : Nat) (PS : Nat → Nat) (BP : Nat)
    (LR : Nat → Nat) (ng : CFSG.Monster.B.Mathieu.NormalGenRecord) : Bool :=
  ng.chain.degree == n &&
    ng.chain.generators.length + ng.chain.derivations.length ==
      ng.chain.strongGenerators.length &&
    ng.chain.strongGenerators.take ng.chain.generators.length == ng.chain.generators &&
    bindsL n w PS 0 ng.chain.strongGenerators && bindFromK w BP ng.chain.base 0 &&
    decide ng.chain.base.Nodup &&
    ((List.range ng.chain.base.length).map fun i => rcnt (LR i)).prod == N &&
    ng.chain.generators.length == ng.conjugators.length &&
    ngK n w A Ai B Bi PS ng.representative ng.conjugators

@[expose] noncomputable def memL (y : Nat) : List Nat → Bool
  | [] => false
  | z :: L => Nat.beq y z || memL y L

@[expose] noncomputable def covK (n w p : Nat) (L : List Nat) (y : Nat) : Bool :=
  Nat.beq y (pidn n w) || !Nat.beq (powK n w (mask w) (pidn n w) y p) (pidn n w) ||
    (List.range p).any fun j => !Nat.beq j 0 && memL (powK n w (mask w) (pidn n w) y j) L

@[expose] noncomputable def sylowB (n w N k : Nat) (LR0 TRI0 : Nat → Nat) (BP0 nb0 : Nat)
    (PS LR TR TRI : Nat → Nat) (BP nb : Nat) (s : CFSG.Monster.B.Mathieu.SylowRecord) : Bool :=
  s.generators.all (elemOK n w) &&
    (List.range s.generators.length).all
      (fun j => Nat.beq (PS j) (packL w (s.generators.getD j []))) &&
    s.generators.all (fun x =>
      siftK n w (mask w) (n * w) (pidn n w) LR0 TRI0 BP0 nb0 0 (packL w x)) &&
    Nat.beq (CFSG.KS.SporSch.MOC.ordK LR nb) (s.prime ^ k) && Nat.beq (N % s.prime ^ k) 0 &&
    !Nat.beq (N % s.prime ^ (k + 1)) 0 &&
    s.normalGeneration.all (fun ng => repK n w s.prime LR TRI BP nb ng.representative) &&
    decide (s.normalGeneration.map (·.representative)).Nodup &&
    Nat.beq (CFSG.KS.SporSch.MOC.enumFrom n w (mask w) (n * w) LR TR
      (covK n w s.prime ((s.normalGeneration.map (·.representative)).map (packL w))) nb 0
      (pidn n w) 0) (CFSG.KS.SporSch.MOC.ordK LR nb)

end CFSG.KC.MathieuK

end
