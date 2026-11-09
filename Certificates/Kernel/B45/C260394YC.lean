module

public import Certificates.Kernel.B45.C260394Y
public import CFSG.Certificates.Kernel.Spor.PK.Perm.CompC
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelB45.C260394

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.LQT.TC CFSG.KC.B45P.RuSyl
  CertificateChecks.KernelMisc CertificateChecks.KernelSporSch.RuG CFSG.Quasithin.B45Exc.Ru

@[expose] noncomputable def wordPB (n w idn : Nat) (G GI : List Nat) (wd : List Int)
    (k : Nat → Nat → Bool) : Bool :=
  List.rec (motive := fun _ => (Nat → Nat → Bool) → Bool) (fun k => k idn idn)
    (fun z _ ih k => ih fun A AI => letGP idn G GI z fun L LI =>
      strictB (pcompC n w (mask w) L A) fun B => strictB (pcompC n w (mask w) AI LI) fun BI =>
        k B BI) wd k

@[expose] noncomputable def ppwB (n w p e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn n w)
    (fun _ ih => strictN ih (fun q => pcompC n w (mask w) p q)) e

@[expose] noncomputable def xPB (TR : Nat → Nat) (o0 o1 c : Nat) : Nat :=
  pcompC 4060 12 (mask 12) (TR (Nat.add o0 (Nat.shiftRight c 3))) (TR (Nat.add o1 (Nat.land c 7)))

@[expose] noncomputable def cjPB (g gi x : Nat) : Nat :=
  pcompC 4060 12 (mask 12) (pcompC 4060 12 (mask 12) g x) gi

@[expose] noncomputable def yPB (TR CD : Nat → Nat) (o0 o1 : Nat) (e : Nat → Nat) (g gi : Nat) :
    Nat :=
  pcompC 4060 12 (mask 12)
    (pcompC 4060 12 (mask 12)
      (pcompC 4060 12 (mask 12) (xPB TR o0 o1 (CD (e 0))) (cjPB g gi (xPB TR o0 o1 (CD (e 1)))))
      (xPB TR o0 o1 (CD (e 2))))
    (cjPB g gi (xPB TR o0 o1 (CD (e 3))))

@[expose] noncomputable def dblCB (TR CD : Nat → Nat) (o0 o1 idn : Nat) (G GI : List Nat)
    (e : Nat → Nat) (wd : List Int) : Bool :=
  bAnd(allN 4 (fun t => Nat.blt (e t) 495),
    wordPB 4060 12 idn G GI wd fun g gi =>
      strictB (yPB TR CD o0 o1 e g gi) fun Y =>
        bAnd(Nat.beq (ppwB 4060 12 Y 29) idn,
          bIf(allN 4060 (fun p => Nat.beq (rdC 12 (mask 12) Y p) p), false, true)))

@[expose] noncomputable def itemB (q d : Nat) : Bool :=
  bIf(Nat.blt (Nat.add (Nat.mul 12 q) d) (WN 0),
    dblCB RuSqS.TR CD (roff 4060 48720 (RuSqS.LR 0)) (roff 4060 48720 (RuSqS.LR 1)) (pidn 4060 12)
      [A0, A1] [A0I, A1I] (quadC WQ (Nat.add (Nat.mul 12 q) d)) (wdOf (Nat.add (Nat.mul 12 q) d)),
    true)

@[expose] noncomputable def dblBC (q : Nat) : Bool :=
  bAnd(idK 4060 12 (mask 12), bAnd(gensTc 4060 12 [A0, A1] [A0I, A1I],
    allN 12 (fun d => itemB q d)))

theorem pcomp_fun_B : pcomp 4060 12 (mask 12) = pcompC 4060 12 (mask 12) :=
  funext fun p => funext fun q => (CFSG.KS.PK.pcompC_eq 4060 12 p q).symm

theorem pg_fun_B : pg 12 (mask 12) = rdC 12 (mask 12) :=
  funext fun p => funext fun i => (CFSG.KS.PK.rdC_eq 12 p i).symm

theorem strictB_eqB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem dblB_eq_C (q : Nat) : dblB q = dblBC q := by
  unfold dblB dblBC itemB
  simp only [strictB_eqB]
  unfold CFSG.KC.B45P.RuSyl.dblC dblCB CFSG.KC.LQT.TC.wordP wordPB
    CFSG.KC.B45P.RuSyl.yP yPB CFSG.KC.B45P.RuSyl.cjP cjPB CFSG.KC.B45P.RuSyl.xP xPB
    CFSG.KC.PkPow.ppw ppwB
  rw [pcomp_fun_B, pg_fun_B]

theorem allBlk_ofB {b : Nat} {f : Nat → Bool} :
    ∀ {len : Nat}, (∀ l < len, f (Nat.add b l) = true) → allBlk b f len = true
  | 0, _ => rfl
  | len + 1, h => by
    show bAnd(f (Nat.add b len), allBlk b f len) = true
    rw [h len (by omega)]
    exact allBlk_ofB fun l hl => h l (by omega)

theorem allN12_of {f : Nat → Bool} (h : ∀ d < 12, f d = true) : allN 12 f = true := by
  show bAnd(allBlk 0 f 12, true) = true
  rw [allBlk_ofB (fun l hl => by simpa using h l hl)]

theorem all12 {P : Nat → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) (h5 : P 5)
    (h6 : P 6) (h7 : P 7) (h8 : P 8) (h9 : P 9) (h10 : P 10) (h11 : P 11) : ∀ d < 12, P d := by
  intro d hd
  match d, hd with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3
  | 4, _ => exact h4
  | 5, _ => exact h5
  | 6, _ => exact h6
  | 7, _ => exact h7
  | 8, _ => exact h8
  | 9, _ => exact h9
  | 10, _ => exact h10
  | 11, _ => exact h11

theorem idK_okB : idK 4060 12 (mask 12) = true := by quickRfl

theorem gensTc_okB : gensTc 4060 12 [A0, A1] [A0I, A1I] = true := by quickRfl

theorem dblBC_of (q : Nat) (h : ∀ d < 12, itemB q d = true) : dblBC q = true := by
  unfold dblBC
  rw [idK_okB, gensTc_okB]
  exact allN12_of h

end CertificateChecks.KernelB45.C260394

end
