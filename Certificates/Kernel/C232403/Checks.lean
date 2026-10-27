module

public import Certificates.Kernel.C232403.Data
public import Certificates.Kernel.Item434.M22Chain
public import Certificates.Data.Inputs2324QM22
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelC232403

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KC.WCnt
open CertificateChecks.KernelItem434 CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2324Q
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen

theorem k232403c0 : Nat.beq (cntK 0) 0 = true := by quickRfl
theorem k232403c1 : Nat.beq (cntK 1) 0 = true := by quickRfl
theorem k232403c2 : Nat.beq (cntK 2) 0 = true := by quickRfl

@[expose] noncomputable def siftT (G : Nat) : Bool :=
  Nat.beq (Nat.shiftRight G (22 * 5)) 0 && allN 22 (fun t => Nat.blt (pg 5 (mask 5) G t) 22) &&
    siftK 22 5 (mask 5) (22 * 5) (pidn 22 5) M22C.LR M22C.TRI M22C.BP 5 0 G

@[expose] noncomputable def vOK (k : Nat) : Bool :=
  arrBind (m22VArr k) 22 5 (vK k) && permB 22 5 (vK k) && siftT (vK k) &&
    Nat.beq (cm 22 5 (vK k) (vK k)) (pidn 22 5)

theorem k232403v : ∀ k < 6, vOK k = true := by
  intro k hk
  interval_cases k <;> quickRfl

@[expose] noncomputable def eRel (j : Nat) : Bool :=
  !(Nat.beq (eK j) (pidn 22 5)) &&
    Nat.beq (cm 22 5 (vK (2 * j)) (vK (2 * j + 1))) (cm 22 5 (vK (2 * j + 1)) (vK (2 * j))) &&
    Nat.beq (cm 22 5 (vK (2 * j)) (eK j)) (cm 22 5 (eK j) (vK (2 * j))) &&
    Nat.beq (cm 22 5 (vK (2 * j + 1)) (eK j)) (cm 22 5 (eK j) (vK (2 * j + 1))) &&
    Nat.beq (wK j) (cm 22 5 (vK (2 * j)) (vK (2 * j + 1)))

theorem k232403e : (arrBind m22E12 22 5 (eK 2) && permB 22 5 (eK 2) &&
    Nat.beq (eK 0) (M22E 2) && Nat.beq (eK 1) (M22E 3) &&
    Nat.beq (cm 22 5 (M22E 2) (M22E 3)) (eK 2) && eRel 0 && eRel 1 && eRel 2) = true := by
  quickRfl

theorem k232403g : (permB 22 5 (M22E 0) && permB 22 5 (M22E 1) &&
    Nat.beq (prodV m22VWordA) (M22E 0) && Nat.beq (prodV m22VWordB) (M22E 1)) = true := by
  quickRfl

theorem k232403ptV : ∀ k : Fin 6, ∀ i : Fin 22,
    pt (vK k.val) i.val = (m22Fn (m22VArr k.val) i).val := by decide +kernel

theorem k232403ptE : ∀ j : Fin 3, ∀ i : Fin 22,
    pt (eK j.val) i.val = (m22Fn (m22EArr j.val) i).val := by decide +kernel

theorem k232403ptW : ∀ j : Fin 3, ∀ i : Fin 22,
    pt (wK j.val) i.val = pt (vK (2 * j.val)) (pt (vK (2 * j.val + 1)) i.val) := by
  decide +kernel

theorem k232403entries : ∀ k : Fin 6, ∀ i : Fin 22, (m22VArr k.val)[i.val]! < 22 := by
  decide +kernel

theorem k232403fix : ∀ j : Fin 3, ∀ y : Fin 22,
    (inM (fK j.val) y.val = true → pt (eK j.val) y.val = y.val) ∧
      (pt (eK j.val) y.val = y.val → inM (fK j.val) y.val = true) := by decide +kernel

theorem k232403pts : ∀ j : Fin 3, xP.getD j.val 0 < 22 ∧ yP.getD j.val 0 < 22 ∧
    pP.getD j.val 0 < 22 ∧ pt (eK j.val) (xP.getD j.val 0) = yP.getD j.val 0 ∧
    pt (eK j.val) (xP.getD j.val 0) ≠ xP.getD j.val 0 ∧
    pt (eK j.val) (pP.getD j.val 0) = pP.getD j.val 0 ∧
    pt (dK j.val) (xP.getD j.val 0) = 0 ∧ pt (dK j.val) (yP.getD j.val 0) = 1 ∧
    pt (dK j.val) (pP.getD j.val 0) = 2 := by decide +kernel

end CertificateChecks.KernelC232403

end
