module

public import CFSG.Certificates.Kernel.BabyMonster.BThirteenFacts
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.All
public import CFSG.Certificates.Kernel.BabyMonster.StripNeSound
public import Certificates.Kernel.BabyMonster.ChainN
public import Certificates.Kernel.BabyMonster.FiveA.Basic
public import Certificates.Kernel.BabyMonster.FiveA.RankLin
public import Certificates.Kernel.BabyMonster.FiveA.Facts13613
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check0
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check1
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check10
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check11
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check12
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check13
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check14
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check15
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check16
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check17
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check18
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check19
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check2
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check20
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check21
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check22
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check23
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check24
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check25
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check26
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check3
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check4
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check5
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check6
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check7
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check8
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check9
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Ne
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.RkT1
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.RkT2
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.RkT4
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Wf

public section

namespace CertificateChecks.KernelBM.BThirteen

open CFSG.KC.BM CFSG.KC.BM.BThirteen CertificateChecks.KernelBM.FiveA

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

set_option maxRecDepth 100000

theorem comm_of {A B P : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (h1 : AllStrips [B] A P) (h2 : AllStrips [A] B P) : stripMat A * stripMat B = stripMat B * stripMat A :=
  (mul1 hA hB h1).trans (mul1 hB hA h2).symm

theorem fact17150 : Fact17150 (stripMat X) (stripMat S) (stripMat T2) (stripMat T4) (stripMat T5)
    (stripMat G) := by
  have eX : stripMat X = stripMat v79 ^ 2 := by
    rw [← mul1 wf_v79 wf_v79 (by bm_strips4 CFSG.KC.BM.BThirteen.c_X 69), sq]
  have e81 : stripMat v81 = stripMat v79 ^ 4 := by
    rw [← mul1 wf_X wf_X (by bm_strips4 CFSG.KC.BM.BThirteen.c_v81 69), eX, ← pow_add]
  have e82 : stripMat v82 = stripMat v79 ^ 8 := by
    rw [← mul1 wf_v81 wf_v81 (by bm_strips4 CFSG.KC.BM.BThirteen.c_v82 69), e81, ← pow_add]
  have e83 : stripMat v83 = stripMat v79 ^ 12 := by
    rw [← mul1 wf_v82 wf_v81 (by bm_strips4 CFSG.KC.BM.BThirteen.c_v83 69), e82, e81, ← pow_add]
  have eS : stripMat S = stripMat v79 ^ 13 := by
    rw [← mul1 wf_v83 wf_v79 (by bm_strips4 CFSG.KC.BM.BThirteen.c_S 69), e83, ← pow_succ]
  have hSS : stripMat S * stripMat S = 1 :=
    one1 wf_S wf_S (by bm_strips4 CFSG.KC.BM.BThirteen.sig2 69)
  have hX13 : stripMat X ^ 13 = 1 := by
    rw [eX, ← pow_mul, ← hSS, eS, ← pow_add]
  have hX6 : stripMat v83 = stripMat X ^ 6 := by
    rw [e83, eX, ← pow_mul]
  have hC3sq : stripMat C3 * stripMat C3 = stripMat C3sq :=
    mul1 wf_C3 wf_C3 (by bm_strips4 CFSG.KC.BM.BThirteen.c_C3sq 69)
  have hC3c : stripMat C3sq * stripMat C3 = 1 :=
    one1 wf_C3sq wf_C3 (by bm_strips4 CFSG.KC.BM.BThirteen.c3cube 69)
  have hC3i : stripMat C3 * stripMat C3sq = 1 := by
    rw [← hC3sq, ← mul_assoc, hC3sq, hC3c]
  have hT2 : stripMat S * stripMat C3 = stripMat T2 :=
    mul1 wf_S wf_C3 (by bm_strips4 CFSG.KC.BM.BThirteen.c_T2 69)
  have hT4 : stripMat C3 * stripMat C4 = stripMat T4 :=
    mul1 wf_C3 wf_C4 (by bm_strips4 CFSG.KC.BM.BThirteen.c_T4 69)
  have hT5 : stripMat C4 * stripMat C3 = stripMat T5 :=
    mul1 wf_C4 wf_C3 (by bm_strips4 CFSG.KC.BM.BThirteen.c_T5 69)
  have h22 : stripMat T2 * stripMat T2 = 1 :=
    one1 wf_T2 wf_T2 (by bm_strips4 CFSG.KC.BM.BThirteen.t2sq 69)
  have h44 : stripMat T4 * stripMat T4 = 1 :=
    one1 wf_T4 wf_T4 (by bm_strips4 CFSG.KC.BM.BThirteen.t4sq 69)
  have hT5c : stripMat T5 = stripMat C3sq * stripMat T4 * stripMat C3 := by
    rw [← hT4, ← hT5]
    calc stripMat C4 * stripMat C3
        = stripMat C3sq * stripMat C3 * stripMat C4 * stripMat C3 := by rw [hC3c, one_mul]
      _ = stripMat C3sq * (stripMat C3 * stripMat C4) * stripMat C3 := by
          rw [mul_assoc (stripMat C3sq)]
  have h55 : stripMat T5 * stripMat T5 = 1 := by
    rw [hT5c]
    calc stripMat C3sq * stripMat T4 * stripMat C3 * (stripMat C3sq * stripMat T4 * stripMat C3)
        = stripMat C3sq * (stripMat T4 * ((stripMat C3 * stripMat C3sq) *
            (stripMat T4 * stripMat C3))) := by simp only [mul_assoc]
      _ = stripMat C3sq * (stripMat T4 * (stripMat T4 * stripMat C3)) := by rw [hC3i, one_mul]
      _ = stripMat C3sq * stripMat C3 := by rw [← mul_assoc (stripMat T4), h44, one_mul]
      _ = 1 := hC3c
  have hr1 : (stripMat S - 1).rank = 1860 :=
    rank_sub_one_of_cert (by norm_num) wf_S wf_PT1 wf_QT1
      (by bm_stripsx CFSG.KC.BM.BThirteen.rkT1_ 69) shape_rkT1 ech_rkT1
  have hr2 : (stripMat T2 - 1).rank = 1860 :=
    rank_sub_one_of_cert (by norm_num) wf_T2 wf_PT2 wf_QT2
      (by bm_stripsx CFSG.KC.BM.BThirteen.rkT2_ 69) shape_rkT2 ech_rkT2
  have hr4 : (stripMat T4 - 1).rank = 1860 :=
    rank_sub_one_of_cert (by norm_num) wf_T4 wf_PT4 wf_QT4
      (by bm_stripsx CFSG.KC.BM.BThirteen.rkT4_ 69) shape_rkT4 ech_rkT4
  have hr5 : (stripMat T5 - 1).rank = 1860 := by
    rw [hT5c, rank_conj hC3c, hr4]
  have cSX : Commute (stripMat S) (stripMat X) :=
    (comm_of (P := SX) wf_X wf_S (by bm_strips4 CFSG.KC.BM.BThirteen.cmX_S 69)
      (by bm_strips4 CFSG.KC.BM.BThirteen.c_SX 69)).symm
  have cC3X : Commute (stripMat C3) (stripMat X) :=
    (comm_of (P := C3X) wf_X wf_C3 (by bm_strips4 CFSG.KC.BM.BThirteen.cmX_C3 69)
      (by bm_strips4 CFSG.KC.BM.BThirteen.c_C3X 69)).symm
  have cC4X : Commute (stripMat C4) (stripMat X) :=
    (comm_of (P := C4X) wf_X wf_C4 (by bm_strips4 CFSG.KC.BM.BThirteen.cmX_C4 69)
      (by bm_strips4 CFSG.KC.BM.BThirteen.c_C4X 69)).symm
  have cGS : Commute (stripMat G) (stripMat S) :=
    comm_of (P := GS) wf_G wf_S (by bm_strips4 CFSG.KC.BM.BThirteen.c_GS 69)
      (by bm_strips4 CFSG.KC.BM.BThirteen.cmG_S 69)
  have cGC3 : Commute (stripMat G) (stripMat C3) :=
    comm_of (P := GC3) wf_G wf_C3 (by bm_strips4 CFSG.KC.BM.BThirteen.c_GC3 69)
      (by bm_strips4 CFSG.KC.BM.BThirteen.cmG_C3 69)
  have cGC4 : Commute (stripMat G) (stripMat C4) :=
    comm_of (P := GC4) wf_G wf_C4 (by bm_strips4 CFSG.KC.BM.BThirteen.c_GC4 69)
      (by bm_strips4 CFSG.KC.BM.BThirteen.cmG_C4 69)
  have cT2X : Commute (stripMat T2) (stripMat X) := by
    rw [← hT2]
    exact cSX.mul_left cC3X
  have cT4X : Commute (stripMat T4) (stripMat X) := by
    rw [← hT4]
    exact cC3X.mul_left cC4X
  have cT5X : Commute (stripMat T5) (stripMat X) := by
    rw [← hT5]
    exact cC4X.mul_left cC3X
  have cGT2 : Commute (stripMat G) (stripMat T2) := by
    rw [← hT2]
    exact cGS.mul_right cGC3
  have cGT5 : Commute (stripMat G) (stripMat T5) := by
    rw [← hT5]
    exact cGC4.mul_right cGC3
  have hGX : stripMat G * stripMat X = stripMat X ^ 6 * stripMat G := by
    rw [mul1 (C := GX) wf_G wf_X (by bm_strips4 CFSG.KC.BM.BThirteen.c_GX 69), ← hX6,
      mul1 (C := GX) wf_v83 wf_G (by bm_strips4 CFSG.KC.BM.BThirteen.gconj 69)]
  have h15 : stripMat S * stripMat T5 = stripMat T5 * stripMat S :=
    comm_of (P := ST5) wf_S wf_T5 (by bm_strips4 CFSG.KC.BM.BThirteen.c_ST5 69)
      (by bm_strips4 CFSG.KC.BM.BThirteen.cm15 69)
  have h12 : stripMat S * stripMat T2 = stripMat C3 := by
    rw [← hT2, ← mul_assoc, hSS, one_mul]
  have h12c : (stripMat S * stripMat T2) ^ 3 = 1 := by
    rw [h12, pow_three, ← mul_assoc, hC3sq, hC3c]
  have ne1 : ∀ {A : List Nat} (hA : wfMat A = true) (h : notB (Nat.beq (A.getD 0 0) (idS 0)) = true),
      stripMat A ≠ 1 := fun hA h => stripMat_ne_one_of_strip hA (by norm_num) h
  have ne15 : stripMat S ≠ stripMat T5 :=
    stripMat_mul_ne_of_strip (Ws := []) (Ds := []) (by simp) (by simp) wf_S wf_T5 (j := 0)
      (by norm_num) CFSG.KC.BM.BThirteen.ne15
  refine ⟨hX13, ne1 wf_X CFSG.KC.BM.BThirteen.neX,
    ⟨hSS, ne_one_of_rank hr1 (by norm_num), hr1, cSX.eq⟩,
    ⟨h22, ne_one_of_rank hr2 (by norm_num), hr2, cT2X.eq⟩,
    ⟨h44, ne_one_of_rank hr4 (by norm_num), hr4, cT4X.eq⟩,
    ⟨h55, ne_one_of_rank hr5 (by norm_num), hr5, cT5X.eq⟩,
    h15, fun h => ne15 h.symm, h12c, by rw [h12]; exact ne1 wf_C3 CFSG.KC.BM.BThirteen.neC3,
    hGX, cGS.eq, cGT2.eq, cGT5.eq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact stripMat_mul_ne_of_strip (Ws := [T2, S, T4]) (Ds := [T2])
      (by simp [wf_T2, wf_S, wf_T4]) (by simp [wf_T2]) wf_T4 wf_S (j := 0) (by norm_num)
      CFSG.KC.BM.BThirteen.w12
  · exact stripMat_mul_ne_of_strip (Ws := [T4, S, T2]) (Ds := [T4])
      (by simp [wf_T2, wf_S, wf_T4]) (by simp [wf_T4]) wf_T2 wf_S (j := 0) (by norm_num)
      CFSG.KC.BM.BThirteen.w14
  · exact stripMat_mul_ne_of_strip (Ws := [T5, S, T2]) (Ds := [T5])
      (by simp [wf_T2, wf_S, wf_T5]) (by simp [wf_T5]) wf_T2 wf_S (j := 0) (by norm_num)
      CFSG.KC.BM.BThirteen.w15
  · exact stripMat_mul_ne_of_strip (Ws := [T4, T2, S]) (Ds := [T4])
      (by simp [wf_T2, wf_S, wf_T4]) (by simp [wf_T4]) wf_S wf_T2 (j := 0) (by norm_num)
      CFSG.KC.BM.BThirteen.w24
  · exact stripMat_mul_ne_of_strip (Ws := [T5, T2, S]) (Ds := [T5])
      (by simp [wf_T2, wf_S, wf_T5]) (by simp [wf_T5]) wf_S wf_T2 (j := 0) (by norm_num)
      CFSG.KC.BM.BThirteen.w25
  · exact stripMat_mul_ne_of_strip (Ws := [T5, T4, S]) (Ds := [T5])
      (by simp [wf_T4, wf_S, wf_T5]) (by simp [wf_T5]) wf_S wf_T4 (j := 0) (by norm_num)
      CFSG.KC.BM.BThirteen.w45

end CertificateChecks.KernelBM.BThirteen

end
