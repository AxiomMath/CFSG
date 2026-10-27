module

public import CFSG.RankThree.PartTwo.Toolkit.M12FactsCertificate9950Inputs
meta import CFSG.RankThree.PartTwo.Toolkit.M12FactsCertificate9950Inputs
public import CFSG.GH74.M12.HypGroup
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import CFSG.RankThree.PartTwo.Toolkit.M12Local
public import CFSG.RankThree.PartTwo.Toolkit.Statements
meta import CFSG.GH74.M12.HypGroup
meta import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
meta import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
meta import CFSG.RankThree.PartTwo.Toolkit.M12Local
meta import CFSG.RankThree.PartTwo.Toolkit.Statements

public section

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Toolkit
  CFSG.RankThree.PartTwo.Toolkit.M12
open CFSG.GH74.M12.Hyp hiding FT
open CFSG.Blueprint CFSG.RankThree.Asc83Table Subgroup
open scoped commutatorElement

namespace CertificateChecks.Batch9950

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Toolkit
  CFSG.RankThree.PartTwo.Toolkit.M12
open CFSG.GH74.M12.Hyp hiding FT
open CFSG.Blueprint CFSG.RankThree.Asc83Table Subgroup
open scoped commutatorElement

private theorem center_tables : ∀ t ∈ P0T, tmul t xT = tmul xT t → tmul t yT = tmul yT t →
    t = tid ∨ t = zT ∨ t = tmul zT zT := by
  decide +kernel

private theorem distinct_tables :
    xT ∉ FT ∧ xT ∉ AT ∧ xT ∉ A'T ∧ yT ∉ AT ∧ yT ∉ A'T ∧ aT ∉ A'T := by
  decide +kernel

private theorem g0_tables :
    predN [xT, yT] P0T (wordT wG0) = true ∧ tconj (wordT wG0) zT = tmul zT zT ∧
    A'T.contains (tconj (wordT wG0) aT) = true ∧ AT.contains (tconj (wordT wG0) a'T) = true ∧
    predN [zT, aT] AT (wordT wG0) = false := by
  decide +kernel

private theorem gl_tables :
    tconj (wordT wER) zT = tmul (tpow zT 2) (tpow xT 0) ∧
      tconj (wordT wER) xT = tmul (tpow zT 2) (tpow xT 2) ∧
    tconj (wordT wES) zT = tmul (tpow zT 2) (tpow xT 0) ∧
      tconj (wordT wES) xT = tmul (tpow zT 0) (tpow xT 1) ∧
    tconj (wordT wEW) zT = tmul (tpow zT 0) (tpow xT 1) ∧
      tconj (wordT wEW) xT = tmul (tpow zT 1) (tpow xT 0) ∧
    tconj (wordT wFR) zT = tmul (tpow zT 2) (tpow yT 0) ∧
      tconj (wordT wFR) yT = tmul (tpow zT 2) (tpow yT 2) ∧
    tconj (wordT wFS) zT = tmul (tpow zT 2) (tpow yT 0) ∧
      tconj (wordT wFS) yT = tmul (tpow zT 0) (tpow yT 1) ∧
    tconj (wordT wFW) zT = tmul (tpow zT 0) (tpow yT 1) ∧
      tconj (wordT wFW) yT = tmul (tpow zT 1) (tpow yT 0) := by
  decide +kernel

private theorem us_tables :
    predN [zT, aT] AT (wordT wU) = true ∧ predN [zT, aT] AT (wordT wS) = true ∧
    (tmul (tcomm (wordT wU) (wordT wS)) aT == tmul aT (tcomm (wordT wU) (wordT wS))) = false := by
  decide +kernel

private theorem conj_tables :
    tconj (wordT wC1) aT = tmul zT aT ∧ tconj (wordT wC2) aT = tmul (tmul zT zT) aT ∧
    tinv (tmul (tpow zT 0) (tpow aT 2)) = tmul (tpow zT 0) (tpow aT 1) ∧
    tinv (tmul (tpow zT 1) (tpow aT 2)) = tmul (tpow zT 2) (tpow aT 1) ∧
    tinv (tmul (tpow zT 2) (tpow aT 2)) = tmul (tpow zT 1) (tpow aT 1) := by
  decide +kernel

end CertificateChecks.Batch9950

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Toolkit
  CFSG.RankThree.PartTwo.Toolkit.M12 in
open CFSG.GH74.M12.Hyp hiding FT in
open CFSG.Blueprint CFSG.RankThree.Asc83Table Subgroup in
open scoped commutatorElement in
theorem certificate9950 : (∀ t ∈ P0T, tmul t xT = tmul xT t → tmul t yT = tmul yT t →
      t = tid ∨ t = zT ∨ t = tmul zT zT)
    ∧ (xT ∉ FT ∧ xT ∉ AT ∧ xT ∉ A'T ∧ yT ∉ AT ∧ yT ∉ A'T ∧ aT ∉ A'T)
    ∧ (predN [xT, yT] P0T (wordT wG0) = true ∧ tconj (wordT wG0) zT = tmul zT zT ∧
      A'T.contains (tconj (wordT wG0) aT) = true ∧ AT.contains (tconj (wordT wG0) a'T) = true ∧
      predN [zT, aT] AT (wordT wG0) = false)
    ∧ (tconj (wordT wER) zT = tmul (tpow zT 2) (tpow xT 0) ∧
        tconj (wordT wER) xT = tmul (tpow zT 2) (tpow xT 2) ∧
      tconj (wordT wES) zT = tmul (tpow zT 2) (tpow xT 0) ∧
        tconj (wordT wES) xT = tmul (tpow zT 0) (tpow xT 1) ∧
      tconj (wordT wEW) zT = tmul (tpow zT 0) (tpow xT 1) ∧
        tconj (wordT wEW) xT = tmul (tpow zT 1) (tpow xT 0) ∧
      tconj (wordT wFR) zT = tmul (tpow zT 2) (tpow yT 0) ∧
        tconj (wordT wFR) yT = tmul (tpow zT 2) (tpow yT 2) ∧
      tconj (wordT wFS) zT = tmul (tpow zT 2) (tpow yT 0) ∧
        tconj (wordT wFS) yT = tmul (tpow zT 0) (tpow yT 1) ∧
      tconj (wordT wFW) zT = tmul (tpow zT 0) (tpow yT 1) ∧
        tconj (wordT wFW) yT = tmul (tpow zT 1) (tpow yT 0))
    ∧ (predN [zT, aT] AT (wordT wU) = true ∧ predN [zT, aT] AT (wordT wS) = true ∧
      (tmul (tcomm (wordT wU) (wordT wS)) aT == tmul aT (tcomm (wordT wU) (wordT wS))) = false)
    ∧ (tconj (wordT wC1) aT = tmul zT aT ∧ tconj (wordT wC2) aT = tmul (tmul zT zT) aT ∧
      tinv (tmul (tpow zT 0) (tpow aT 2)) = tmul (tpow zT 0) (tpow aT 1) ∧
      tinv (tmul (tpow zT 1) (tpow aT 2)) = tmul (tpow zT 2) (tpow aT 1) ∧
      tinv (tmul (tpow zT 2) (tpow aT 2)) = tmul (tpow zT 1) (tpow aT 1)) := by
  exact ⟨CertificateChecks.Batch9950.center_tables, CertificateChecks.Batch9950.distinct_tables, CertificateChecks.Batch9950.g0_tables,
    CertificateChecks.Batch9950.gl_tables, CertificateChecks.Batch9950.us_tables, CertificateChecks.Batch9950.conj_tables⟩

end Certificates
