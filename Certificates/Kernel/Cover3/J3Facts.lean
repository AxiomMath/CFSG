module

public import Certificates.Kernel.Cover3.J3Checks
public import Certificates.Kernel.SporSch.J3K426.Sift
public import CFSG.Certificates.Kernel.Item434.PkSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCover3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Item434 CFSG.KC.Misc.HexFlat
open CFSG.Monster.B.Co2.Native CFSG.RankThree.PartTwo.Sec4.Item434SporGen
open CFSG.SectionRank.QTK.Insp443.J3Cover
open CFSG.KC.B3S3K (cm pw)

theorem pkJ {k : ℕ} (hk : k < 6) : Pk 6156 13 (j3CovArr k) (JC.F k) := by
  refine ⟨?_, CFSG.KS.Raw.Orb.allN_iff.1 c589303P k hk⟩
  unfold j3CovArr
  rw [JC.eq]
  exact hexTable_sound JC.all k hk

theorem sJ {k : ℕ} (hk : k < 6) (h : wordJ k = true) : j3CovSift (j3CovArr k) = true := by
  unfold j3CovSift
  rw [isInvA_pk (pkJ hk), Bool.true_and, (pkJ hk).1]
  exact CertificateChecks.KernelSporSch.J3KT.sift_of h

theorem pkProdJ (u : ℕ) : Pk 6156 13 (j3CovProd u) (prJ u) := by
  unfold j3CovProd pN prJ
  exact pk_comp c589303W (pk_powN c589303W (pkJ (by norm_num)) _)
    (pk_powN c589303W (pkJ (by norm_num)) _)

theorem distJ : j3CovDistinct = true := by
  unfold j3CovDistinct
  refine List.all_eq_true.2 fun u hu => List.all_eq_true.2 fun v hv => ?_
  rw [List.mem_range] at hu hv
  rw [eqA_pk c589303W (pkProdJ u) (pkProdJ v),
    ← Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 c589303D u hu),
    ← Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 c589303D v hv)]
  exact CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 c589303E u hu) v hv

theorem conjJ {j k : ℕ} (hj : j < 6) (hk : k < 6) :
    Pk 6156 13 (j3CovConj (j3CovArr j) (j3CovArr k)) (cjJ (JC.F j) (JC.F k)) :=
  pk_comp c589303W (pk_comp c589303W (pkJ hj) (pkJ hk)) (pk_inv c589303W (pkJ hj))

theorem commJ {j k : ℕ} (hj : j < 6) (hk : k < 6) (h : cmJ (JC.F j) (JC.F k) = true) :
    commN 6156 (j3CovArr j) (j3CovArr k) = true := by
  rw [commN_pk c589303W (pkJ hj) (pkJ hk)]
  exact h

theorem inQ_of {j k : ℕ} (hj : j < 6) (hk : k < 6) (h : inQJ (cjJ (JC.F j) (JC.F k)) = true) :
    j3CovInQ (j3CovArr j) (j3CovArr k) = true := by
  unfold j3CovInQ
  rw [eqA_pk c589303W (conjJ hj hk) (pkJ (by norm_num)),
    eqA_pk c589303W (conjJ hj hk) (pkJ (by norm_num)),
    eqA_pk c589303W (conjJ hj hk) (pk_comp c589303W (pkJ (by norm_num)) (pkJ (by norm_num)))]
  exact h

open Certificates in
open CFSG.SectionRank.QTK.Insp443.J3Cover in
open CFSG.Monster.B.Co2.Native (eqA compA idA invCand) in
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen (powN commN) in
theorem facts589303 : j3CovSift (j3CovArr 0) = true ∧ j3CovSift (j3CovArr 1) = true ∧
    j3CovSift (j3CovArr 2) = true ∧ j3CovSift (j3CovArr 3) = true ∧
    j3CovSift (j3CovArr 4) = true ∧ j3CovSift (j3CovArr 5) = true ∧
    eqA 6156 (compA 6156 (j3CovArr 0) (j3CovArr 0)) (idA 6156) = true ∧
    eqA 6156 (compA 6156 (j3CovArr 1) (j3CovArr 1)) (idA 6156) = true ∧
    commN 6156 (j3CovArr 0) (j3CovArr 1) = true ∧
    eqA 6156 (j3CovArr 0) (idA 6156) = false ∧
    eqA 6156 (powN 6156 (j3CovArr 2) 3) (idA 6156) = true ∧
    eqA 6156 (powN 6156 (j3CovArr 3) 3) (idA 6156) = true ∧
    commN 6156 (j3CovArr 2) (j3CovArr 3) = true ∧
    j3CovDistinct = true ∧
    j3CovInQ (j3CovArr 2) (j3CovArr 0) = true ∧ j3CovInQ (j3CovArr 2) (j3CovArr 1) = true ∧
    j3CovInQ (j3CovArr 3) (j3CovArr 0) = true ∧ j3CovInQ (j3CovArr 3) (j3CovArr 1) = true ∧
    eqA 6156 (j3CovConj (j3CovArr 4) (j3CovArr 2)) (invCand 6156 (j3CovArr 2)) = true ∧
    commN 6156 (j3CovArr 5) (j3CovArr 2) = true ∧
    eqA 6156 (j3CovConj (j3CovArr 5) (j3CovArr 3)) (invCand 6156 (j3CovArr 3)) = true := by
  obtain ⟨q1, q2, q12, q0⟩ := c589303Q
  obtain ⟨a3, b3, ab⟩ := c589303O
  obtain ⟨i1, i2, i3, i4⟩ := c589303I
  obtain ⟨g1, g2a, g2b⟩ := c589303G
  refine ⟨sJ (by norm_num) c589303S0, sJ (by norm_num) c589303S1, sJ (by norm_num) c589303S2,
    sJ (by norm_num) c589303S3, sJ (by norm_num) c589303S4, sJ (by norm_num) c589303S5, ?_, ?_,
    commJ (by norm_num) (by norm_num) q12, ?_, ?_, ?_, commJ (by norm_num) (by norm_num) ab, distJ,
    inQ_of (by norm_num) (by norm_num) i1, inQ_of (by norm_num) (by norm_num) i2,
    inQ_of (by norm_num) (by norm_num) i3, inQ_of (by norm_num) (by norm_num) i4, ?_,
    commJ (by norm_num) (by norm_num) g2a, ?_⟩
  · rw [eqA_pk c589303W (pk_comp c589303W (pkJ (by norm_num)) (pkJ (by norm_num)))
      (pk_id c589303W)]
    exact q1
  · rw [eqA_pk c589303W (pk_comp c589303W (pkJ (by norm_num)) (pkJ (by norm_num)))
      (pk_id c589303W)]
    exact q2
  · rw [eqA_pk c589303W (pkJ (by norm_num)) (pk_id c589303W)]
    exact q0
  · rw [eqA_pk c589303W (pk_powN c589303W (pkJ (by norm_num)) 3) (pk_id c589303W)]
    exact a3
  · rw [eqA_pk c589303W (pk_powN c589303W (pkJ (by norm_num)) 3) (pk_id c589303W)]
    exact b3
  · rw [eqA_pk c589303W (conjJ (by norm_num) (by norm_num))
      (pk_inv c589303W (pkJ (by norm_num)))]
    exact g1
  · rw [eqA_pk c589303W (conjJ (by norm_num) (by norm_num))
      (pk_inv c589303W (pkJ (by norm_num)))]
    exact g2b

end CertificateChecks.KernelCover3

end
