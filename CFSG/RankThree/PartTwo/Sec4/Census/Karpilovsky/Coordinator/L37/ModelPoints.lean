module

public import Certificates.Certificate291441

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

open CFSG.KC.Misc.F7 CFSG.KC.Loop CFSG.RankThree.Native.ONTriple


theorem ptS_inj {i j : ℕ} (hi : i < nPt) (hj : j < nPt) (e : ptS i = ptS j) : i = j :=
  Certificates.certificate291441.1 i j hi hj e

theorem tree_step {k : ℕ} (hk : k < nPt) (h0 : k ≠ 0) :
    rPar (ptRec k) < k ∧ rLet (ptRec k) < 16 ∧
      (k ≠ startOf k → rLet (ptRec k) % 2 = 1 ∧ rLet (ptRec k) < 12 ∧
        startOf k ≤ rPar (ptRec k)) ∧
      ptS k = ptAct (letU (rLet (ptRec k))) (ptS (rPar (ptRec k))) :=
  Certificates.certificate291441.2.1 k hk h0

theorem fixes_W {l : ℕ} (hl : l < 6) :
    ptAct (gM ⟨l, by omega⟩) (ptS 0) = ptS 0 :=
  Certificates.certificate291441.2.2.1 ⟨l, hl⟩

theorem orbFix_parts {o : ℕ} (ho : o < 5) :
    orbStart o ≤ fixP o ∧ fixP o < orbStart (o + 1) ∧ ∃ hl : fixL o < 6,
      ptAct (gM ⟨fixL o, by omega⟩) (ptS (fixP o)) = ptS (fixP o) :=
  Certificates.certificate291441.2.2.2.1 o ho

theorem gM_seven_eq : ((gM 7 : Mat45ˣ) : Mat45) = (2 : ZMod 7) • (1 : Mat45) :=
  Certificates.certificate291441.2.2.2.2.1

theorem pivots_ptMat_zero : Pivots (ptMat 0) (Fin.castLE (by norm_num)) :=
  Certificates.certificate291441.2.2.2.2.2.1

theorem det_resW_gM {l : ℕ} (hl : l < 6) :
    (resW ((gM ⟨l, by omega⟩ : Mat45ˣ) : Mat45)).det = -1 :=
  Certificates.certificate291441.2.2.2.2.2.2 ⟨l, hl⟩

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37
