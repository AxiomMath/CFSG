module

public import Certificates.Kernel.Cover3.McLChecks
public import Certificates.Kernel.Census.McLN
public import CFSG.Certificates.Kernel.Item434.PkSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCover3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Item434 CFSG.KC.Misc.HexFlat
open CFSG.Monster.B.Co2.Native CFSG.RankThree.PartTwo.Sec4.Item434SporGen
open CFSG.SectionRank.QTK.Insp443.McLCover
open CFSG.KC.B3S3K (cm pw)

theorem pkC {k : ℕ} (hk : k < 5) : Pk 275 9 (mclCovArr k) (MC.F k) := by
  refine ⟨?_, CFSG.KS.Raw.Orb.allN_iff.1 c589302P k hk⟩
  unfold mclCovArr
  rw [MC.eq]
  exact hexTable_sound MC.all k hk

theorem covSift_of {x : Array ℕ} {G : ℕ} (hx : Pk 275 9 x G) (h : siftC G = true) :
    mclCovSift x = true := by
  unfold siftC at h
  simp only [Bool.and_eq_true] at h
  unfold mclCovSift
  rw [isInvA_pk hx, Bool.true_and]
  exact siftK_soundR KernelCensus.McLK.binds KernelCensus.McLK.hperm KernelCensus.McLC.hl hx.1
    (Nat.eq_of_beq_eq_true h.1.1) h.1.2 h.2

theorem sC {k : ℕ} (hk : k < 5) : mclCovSift (mclCovArr k) = true :=
  covSift_of (pkC hk) (CFSG.KS.Raw.Orb.allN_iff.1 c589302S k hk)

theorem pkProd (u : ℕ) : Pk 275 9 (mclCovProd u) (prC u) := by
  unfold mclCovProd pN prC
  exact pk_comp c589302W (pk_powN c589302W (pkC (by norm_num)) _)
    (pk_powN c589302W (pkC (by norm_num)) _)

theorem distC : mclCovDistinct = true := by
  unfold mclCovDistinct
  refine List.all_eq_true.2 fun u hu => List.all_eq_true.2 fun v hv => ?_
  rw [List.mem_range] at hu hv
  rw [eqA_pk c589302W (pkProd u) (pkProd v)]
  exact CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 c589302D u hu) v hv

theorem conjC {j k : ℕ} (hj : j < 5) (hk : k < 5) :
    Pk 275 9 (mclCovConj (mclCovArr j) (mclCovArr k)) (cjC (MC.F j) (MC.F k)) :=
  pk_comp c589302W (pk_comp c589302W (pkC hj) (pkC hk)) (pk_inv c589302W (pkC hj))

theorem commC {j k : ℕ} (hj : j < 5) (hk : k < 5) (h : cmC (MC.F j) (MC.F k) = true) :
    commN 275 (mclCovArr j) (mclCovArr k) = true := by
  rw [commN_pk c589302W (pkC hj) (pkC hk)]
  exact h

open Certificates in
open CFSG.SectionRank.QTK.Insp443.McLCover in
open CFSG.Monster.B.Co2.Native (eqA compA idA invCand) in
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen (powN commN) in
theorem facts589302 : mclCovSift (mclCovArr 0) = true ∧ mclCovSift (mclCovArr 1) = true ∧
    mclCovSift (mclCovArr 2) = true ∧ mclCovSift (mclCovArr 3) = true ∧
    mclCovSift (mclCovArr 4) = true ∧
    eqA 275 (compA 275 (mclCovArr 0) (mclCovArr 0)) (idA 275) = true ∧
    eqA 275 (mclCovArr 0) (idA 275) = false ∧
    eqA 275 (powN 275 (mclCovArr 1) 3) (idA 275) = true ∧
    eqA 275 (powN 275 (mclCovArr 2) 3) (idA 275) = true ∧
    commN 275 (mclCovArr 1) (mclCovArr 2) = true ∧
    commN 275 (mclCovArr 1) (mclCovArr 0) = true ∧
    commN 275 (mclCovArr 2) (mclCovArr 0) = true ∧
    mclCovDistinct = true ∧
    eqA 275 (mclCovConj (mclCovArr 3) (mclCovArr 1)) (invCand 275 (mclCovArr 1)) = true ∧
    commN 275 (mclCovArr 4) (mclCovArr 1) = true ∧
    eqA 275 (mclCovConj (mclCovArr 4) (mclCovArr 2)) (invCand 275 (mclCovArr 2)) = true := by
  obtain ⟨c1, c2, c3, c4⟩ := c589302C
  refine ⟨sC (by norm_num), sC (by norm_num), sC (by norm_num), sC (by norm_num),
    sC (by norm_num), ?_, ?_, ?_, ?_, commC (by norm_num) (by norm_num) c1,
    commC (by norm_num) (by norm_num) c2, commC (by norm_num) (by norm_num) c3, distC, ?_,
    commC (by norm_num) (by norm_num) c4, ?_⟩
  · rw [eqA_pk c589302W (pk_comp c589302W (pkC (by norm_num)) (pkC (by norm_num)))
      (pk_id c589302W)]
    exact c589302Z.1
  · rw [eqA_pk c589302W (pkC (by norm_num)) (pk_id c589302W)]
    exact c589302Z.2
  · rw [eqA_pk c589302W (pk_powN c589302W (pkC (by norm_num)) 3) (pk_id c589302W)]
    exact c589302O.1
  · rw [eqA_pk c589302W (pk_powN c589302W (pkC (by norm_num)) 3) (pk_id c589302W)]
    exact c589302O.2
  · rw [eqA_pk c589302W (conjC (by norm_num) (by norm_num))
      (pk_inv c589302W (pkC (by norm_num)))]
    exact c589302G.1
  · rw [eqA_pk c589302W (conjC (by norm_num) (by norm_num))
      (pk_inv c589302W (pkC (by norm_num)))]
    exact c589302G.2

end CertificateChecks.KernelCover3

end
