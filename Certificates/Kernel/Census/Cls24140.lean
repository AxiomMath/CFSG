module

public import Certificates.Kernel.Census.Cls24140G
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus.Cls24140

open CFSG.EvenSporadicStandard.Wong77.Cls CFSG.KC.RangeSplit

theorem cycS0 : (List.range' 0 512).all (cycTestG mvNF eqVF) = true := by quickRfl

theorem cycS1 : (List.range' 512 512).all (cycTestG mvNF eqVF) = true := by quickRfl

theorem cycS2 : (List.range' 1024 512).all (cycTestG mvNF eqVF) = true := by quickRfl

theorem cycS3 : (List.range' 1536 512).all (cycTestG mvNF eqVF) = true := by quickRfl

theorem cyc : checkCyc = true := by
  have h : (List.range' 0 2048).all (cycTestG mvNF eqVF) = true :=
    all_range'_split (m := 512) (k := 1536) cycS0
      (all_range'_split (m := 512) (k := 1024) cycS1
      (all_range'_split (m := 512) (k := 512) cycS2 cycS3))
  rw [← List.range_eq_range', mvNF_fun, eqVF_fun] at h
  rw [← checkCycG_eq]
  exact h

theorem one0H : oneHeadG mvNF eqVF (compN (aN 0)) (YN 0) (BinvN 0) = true := by quickRfl

theorem one0U0 : (List.range' 0 256).all
    (uniqAtG mvNF eqVF (YN 0) (upG mvNF (compN (aN 0)) (YN 0)) (BinvN 0) (yN 0)) = true := by
  quickRfl

theorem one0U1 : (List.range' 256 256).all
    (uniqAtG mvNF eqVF (YN 0) (upG mvNF (compN (aN 0)) (YN 0)) (BinvN 0) (yN 0)) = true := by
  quickRfl

theorem one0U2 : (List.range' 512 256).all
    (uniqAtG mvNF eqVF (YN 0) (upG mvNF (compN (aN 0)) (YN 0)) (BinvN 0) (yN 0)) = true := by
  quickRfl

theorem one0U3 : (List.range' 768 256).all
    (uniqAtG mvNF eqVF (YN 0) (upG mvNF (compN (aN 0)) (YN 0)) (BinvN 0) (yN 0)) = true := by
  quickRfl

theorem one0U4 : (List.range' 1024 256).all
    (uniqAtG mvNF eqVF (YN 0) (upG mvNF (compN (aN 0)) (YN 0)) (BinvN 0) (yN 0)) = true := by
  quickRfl

theorem one0U5 : (List.range' 1280 256).all
    (uniqAtG mvNF eqVF (YN 0) (upG mvNF (compN (aN 0)) (YN 0)) (BinvN 0) (yN 0)) = true := by
  quickRfl

theorem one0U6 : (List.range' 1536 256).all
    (uniqAtG mvNF eqVF (YN 0) (upG mvNF (compN (aN 0)) (YN 0)) (BinvN 0) (yN 0)) = true := by
  quickRfl

theorem one0U7 : (List.range' 1792 256).all
    (uniqAtG mvNF eqVF (YN 0) (upG mvNF (compN (aN 0)) (YN 0)) (BinvN 0) (yN 0)) = true := by
  quickRfl

theorem one0W : checkWordsG mvNF eqVF (stdAN 0) (stdBN 0) (compN (aN 0)) (YN 0)
    (mulNG mvNF (kryNG mvNF (YN 0) 1 (yN 0)) (BinvN 0)) = true := by
  quickRfl

theorem one0 : checkOne 0 = true := by
  have hU : (List.range' 0 2048).all
      (uniqAtG mvNF eqVF (YN 0) (upG mvNF (compN (aN 0)) (YN 0)) (BinvN 0) (yN 0)) = true :=
    all_range'_split (m := 256) (k := 1792) one0U0
      (all_range'_split (m := 256) (k := 1536) one0U1
      (all_range'_split (m := 256) (k := 1280) one0U2
      (all_range'_split (m := 256) (k := 1024) one0U3
      (all_range'_split (m := 256) (k := 768) one0U4
      (all_range'_split (m := 256) (k := 512) one0U5
      (all_range'_split (m := 256) (k := 256) one0U6 one0U7))))))
  rw [← List.range_eq_range'] at hU
  have h : checkOneG mvNF eqVF 0 = true := by
    unfold checkOneG checkOneAuxG checkUniqG
    exact andT (andT one0H hU) one0W
  rw [mvNF_fun, eqVF_fun, checkOneG_eq] at h
  exact h

theorem one1H : oneHeadG mvNF eqVF (compN (aN 1)) (YN 1) (BinvN 1) = true := by quickRfl

theorem one1U0 : (List.range' 0 256).all
    (uniqAtG mvNF eqVF (YN 1) (upG mvNF (compN (aN 1)) (YN 1)) (BinvN 1) (yN 1)) = true := by
  quickRfl

theorem one1U1 : (List.range' 256 256).all
    (uniqAtG mvNF eqVF (YN 1) (upG mvNF (compN (aN 1)) (YN 1)) (BinvN 1) (yN 1)) = true := by
  quickRfl

theorem one1U2 : (List.range' 512 256).all
    (uniqAtG mvNF eqVF (YN 1) (upG mvNF (compN (aN 1)) (YN 1)) (BinvN 1) (yN 1)) = true := by
  quickRfl

theorem one1U3 : (List.range' 768 256).all
    (uniqAtG mvNF eqVF (YN 1) (upG mvNF (compN (aN 1)) (YN 1)) (BinvN 1) (yN 1)) = true := by
  quickRfl

theorem one1U4 : (List.range' 1024 256).all
    (uniqAtG mvNF eqVF (YN 1) (upG mvNF (compN (aN 1)) (YN 1)) (BinvN 1) (yN 1)) = true := by
  quickRfl

theorem one1U5 : (List.range' 1280 256).all
    (uniqAtG mvNF eqVF (YN 1) (upG mvNF (compN (aN 1)) (YN 1)) (BinvN 1) (yN 1)) = true := by
  quickRfl

theorem one1U6 : (List.range' 1536 256).all
    (uniqAtG mvNF eqVF (YN 1) (upG mvNF (compN (aN 1)) (YN 1)) (BinvN 1) (yN 1)) = true := by
  quickRfl

theorem one1U7 : (List.range' 1792 256).all
    (uniqAtG mvNF eqVF (YN 1) (upG mvNF (compN (aN 1)) (YN 1)) (BinvN 1) (yN 1)) = true := by
  quickRfl

theorem one1W : checkWordsG mvNF eqVF (stdAN 1) (stdBN 1) (compN (aN 1)) (YN 1)
    (mulNG mvNF (kryNG mvNF (YN 1) 1 (yN 1)) (BinvN 1)) = true := by
  quickRfl

theorem one1 : checkOne 1 = true := by
  have hU : (List.range' 0 2048).all
      (uniqAtG mvNF eqVF (YN 1) (upG mvNF (compN (aN 1)) (YN 1)) (BinvN 1) (yN 1)) = true :=
    all_range'_split (m := 256) (k := 1792) one1U0
      (all_range'_split (m := 256) (k := 1536) one1U1
      (all_range'_split (m := 256) (k := 1280) one1U2
      (all_range'_split (m := 256) (k := 1024) one1U3
      (all_range'_split (m := 256) (k := 768) one1U4
      (all_range'_split (m := 256) (k := 512) one1U5
      (all_range'_split (m := 256) (k := 256) one1U6 one1U7))))))
  rw [← List.range_eq_range'] at hU
  have h : checkOneG mvNF eqVF 1 = true := by
    unfold checkOneG checkOneAuxG checkUniqG
    exact andT (andT one1H hU) one1W
  rw [mvNF_fun, eqVF_fun, checkOneG_eq] at h
  exact h

theorem cls : clsCheck = true := by
  unfold clsCheck
  rw [cyc, one0, one1]
  rfl

end CertificateChecks.KernelCensus.Cls24140
