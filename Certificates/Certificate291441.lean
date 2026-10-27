module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelPointsDefs
import Certificates.Kernel.Misc.ON.PointsFacts
public import Mathlib.GroupTheory.Nilpotent

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelMisc.ON

open CFSG.RankThree.Native.ONTriple hiding ptMat in
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37 CFSG.KC.Misc.F7 in
theorem certificate291441 :
    (∀ i j : ℕ, i < nPt → j < nPt → ptS i = ptS j → i = j) ∧
    (∀ k : ℕ, k < nPt → k ≠ 0 →
      rPar (ptRec k) < k ∧ rLet (ptRec k) < 16 ∧
        (k ≠ startOf k → rLet (ptRec k) % 2 = 1 ∧ rLet (ptRec k) < 12 ∧
          startOf k ≤ rPar (ptRec k)) ∧
        ptS k = ptAct (letU (rLet (ptRec k))) (ptS (rPar (ptRec k)))) ∧
    (∀ l : Fin 6, ptAct (gM l.castSucc.castSucc) (ptS 0) = ptS 0) ∧
    (∀ o < 5, orbStart o ≤ fixP o ∧ fixP o < orbStart (o + 1) ∧ ∃ hl : fixL o < 6,
      ptAct (gM ⟨fixL o, by omega⟩) (ptS (fixP o)) = ptS (fixP o)) ∧
    ((gM 7 : Mat45ˣ) : Mat45) = (2 : ZMod 7) • (1 : Mat45) ∧
    Pivots (ptMat 0) (Fin.castLE (by norm_num)) ∧
    ∀ l : Fin 6, (resW ((gM l.castSucc.castSucc : Mat45ˣ) : Mat45)).det = -1 :=
  ⟨ptS_injK, tree_stepK, fixes_WK, orbFix_partsK, gM_seven_eqK, pivots_ptMat_zeroK,
    det_resW_gMK⟩

end Certificates
