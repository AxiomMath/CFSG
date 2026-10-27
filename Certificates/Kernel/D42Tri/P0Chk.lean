module

public import Certificates.Kernel.D42Tri.P0Rec
public import Certificates.Kernel.OmegaEight.Arr3009K
public import CFSG.Quasithin.Recognition.CertU33PresInputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelD42Tri

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CertificateChecks.KernelO8

@[expose] noncomputable def pq (p q : Nat) : Nat := pcomp 360 9 (mask 9) p q

@[expose] noncomputable def nq (p q : Nat) : Bool := bIf(Nat.beq p q, false, true)

@[expose] noncomputable def rpK (j : Nat) : Nat := nIf(Nat.beq j 0, AP.S 8, RPH.F (Nat.pred j))

@[expose] noncomputable def cjK (j : Nat) : Nat := nIf(Nat.beq j 0, pid, CJH.F (Nat.pred j))

@[expose] noncomputable def siftO (X : Nat) : Bool :=
  siftK 360 9 (mask 9) (360 * 9) (pidn 360 9) OmP.LR OmP.TRI OmP.BP 7 0 X

@[expose] noncomputable def tabsK (F : Nat → Nat) (N : Nat) : Bool :=
  allN N (fun j => bAnd(cn (F j), pm (F j)))

@[expose] noncomputable def recK (G GI F : Nat → Nat) (k cnt c R : Nat) (T PL POS SRT SRI : Nat → Nat) :
    Bool :=
  bAnd(Nat.beq c cnt, bAnd(Nat.beq R pid, bAnd(penumHdK R c 512 T PL,
    bAnd(allN k (fun j => bAnd(Nat.beq (G j) (F j), bAnd(Nat.beq (GI j) pid,
      bAnd(canonK 360 9 (mask 9) (360 * 9) (G j), canonK 360 9 (mask 9) (360 * 9) (GI j))))),
    penumSlK 360 9 (mask 9) (360 * 9) false G GI k c T PL POS SRT SRI 0 cnt))))

@[expose] noncomputable def ch17627RelK (w : List (Fin 5 × Bool)) : Nat :=
  w.foldl (fun acc l => pq acc (nIf(l.2, L0H.F l.1.val, pinv (L0H.F l.1.val)))) pid

@[expose] noncomputable def ch17627Row (i v : Nat) : Bool :=
  strictB (r32 P0CC i) (fun c => strictB (r32 P0CK i) (fun k => bAnd(Nat.blt c 243,
    bAnd(Nat.blt k 26, strictB (P0.T c) (fun C => strictB (rpK (Nat.div k 2)) (fun r =>
      bIf(Nat.beq (Nat.mod k 2) 0, Nat.beq (pq C v) (pq r C), Nat.beq (pq r (pq C v)) C)))))))

theorem ch17627_tabs : bAnd(tabsK P0H.F 3, bAnd(tabsK K2H.F 2, bAnd(tabsK L0H.F 5,
    bAnd(tabsK CJH.F 12, tabsK RPH.F 12)))) = true := by quickRfl

theorem ch17627_sift : bAnd(allN 3 (fun j => siftO (P0H.F j)), bAnd(allN 12 (fun j => siftO (CJH.F j)),
    bAnd(allN 5 (fun j => siftO (L0H.F j)), allN 2 (fun j => siftO (K2H.F j))))) = true := by
  quickRfl

theorem ch17627_p0 : recK P0.G P0.GI P0H.F 3 243 P0.cnt P0.R P0.T P0.PL P0.POS P0.SRT P0.SRI = true := by
  quickRfl

theorem ch17627_k2 : recK K2.G K2.GI K2H.F 2 216 K2.cnt K2.R K2.T K2.PL K2.POS K2.SRT K2.SRI = true := by
  quickRfl

theorem ch17627_norm : bAnd(allN 3 (fun j => strictB (r32 P0NI j) (fun q => bAnd(Nat.blt q 243,
      Nat.beq (pq (AP.S 8) (P0H.F j)) (pq (P0.T q) (AP.S 8))))),
    bAnd(Nat.beq (pq (AP.S 8) (pq (AP.S 8) (AP.S 8))) pid, allN 243 (fun i => nq (P0.T i) (AP.S 8)))) =
      true := by
  quickRfl

theorem ch17627_coset : allN 243 (fun i => strictB (pq (P0.T i) (AP.S 8)) (fun v =>
    bIf(Nat.beq (pq v (pq v v)) pid, ch17627Row i v, true))) = true := by
  quickRfl

theorem ch17627_reps : allN 13 (fun j => strictB (pq (cjK j) (rpK j)) (fun x =>
    bIf(Nat.beq x (pq (AP.S 8) (cjK j)), true, Nat.beq x (pq (RPH.F 0) (cjK j))))) = true := by
  quickRfl

theorem ch17627_l0 : bAnd(allN 5 (fun j => Nat.beq (pq (L0H.F j) (AP.S 8)) (pq (AP.S 8) (L0H.F j))),
    bAnd(CFSG.Quasithin.u33PresRels.all (fun w => Nat.beq (ch17627RelK w) pid),
      nq (L0H.F 0) pid)) = true := by
  quickRfl

theorem ch17627_k2c : allN 2 (fun j => Nat.beq (pq (K2H.F j) (RPH.F 0)) (pq (RPH.F 0) (K2H.F j))) =
    true := by
  quickRfl

end CertificateChecks.KernelD42Tri

end
