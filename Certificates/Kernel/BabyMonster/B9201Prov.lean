module

public import Certificates.Kernel.BabyMonster.B9201Run
public import Certificates.Kernel.BabyMonster.Chain2
public import CFSG.Certificates.Kernel.BabyMonster.B9201.All
public import CFSG.Certificates.Kernel.BabyMonster.B9201.Check0
public import CFSG.Certificates.Kernel.BabyMonster.B9201.Check1
public import CFSG.Certificates.Kernel.BabyMonster.B9201.Check2
public import CFSG.Certificates.Kernel.BabyMonster.B9201.Check3
public import CFSG.Certificates.Kernel.BabyMonster.B9201.Check4
public import CFSG.Certificates.Kernel.BabyMonster.B9201.Check5
public import CFSG.Certificates.Kernel.BabyMonster.B9201.Check6
public import CFSG.Certificates.Kernel.BabyMonster.B9201.Check7
public import CFSG.Certificates.Kernel.BabyMonster.B9201.Check8
public import CFSG.Certificates.Kernel.BabyMonster.B9201.Check9

public section

namespace CertificateChecks.KernelBM.Run9201

open CFSG.KC.BM

abbrev MM : Type := Matrix (Fin 4370) (Fin 4370) (ZMod 2)

theorem pw_dbl {x y z : MM} {n m : ℕ} (hy : x ^ n = y) (h : y * y = z) (hm : n + n = m) :
    x ^ m = z := by
  rw [← hm, pow_add, hy]
  exact h

theorem pw_add {x y z w : MM} {n m k : ℕ} (hy : x ^ n = y) (hz : x ^ m = z) (h : y * z = w)
    (hk : n + m = k) : x ^ k = w := by
  rw [← hk, pow_add, hy, hz]
  exact h

abbrev PW (A B C : List ℕ) : Prop := wfMat C = true ∧ stripMat A * stripMat B = stripMat C

theorem prodW {A B C : List ℕ} (hA : wfMat A = true) (hB : wfMat B = true)
    (h : AllStrips [B] A C) : PW A B C :=
  ⟨wfMat_of_allStrips hA h, stripMat_mul1 hA hB h⟩

theorem rel11 {A B C D : List ℕ} (hA : wfMat A = true) (hB : wfMat B = true)
    (hC : wfMat C = true) (hD : wfMat D = true) (h : AllStrips2 [B] [D] A C) :
    stripMat A * stripMat B = stripMat C * stripMat D := by
  have e := stripMat_mul_eq_of_allStrips2 (Ws := [B]) (Ds := [D]) (by simpa using hB)
    (by simpa using hD) hA hC h
  rwa [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
    List.foldl_cons, List.foldl_nil] at e

theorem rel2one {A B C : List ℕ} (hA : wfMat A = true) (hB : wfMat B = true)
    (hC : wfMat C = true) (h : AllStrips [B, C] A idStrips) :
    stripMat A * stripMat B * stripMat C = 1 := by
  have e := stripMat_mul_eq_one (Ws := [B, C]) (by simp [hB, hC]) hA h
  rwa [List.map_cons, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_cons,
    List.foldl_nil] at e

theorem wt1 : wfMat BProg.t1 = true := (tM_strip 0 (by norm_num)).2
theorem wt2 : wfMat BProg.t2 = true := (tM_strip 1 (by norm_num)).2
theorem wt3 : wfMat BProg.t3 = true := (tM_strip 2 (by norm_num)).2
theorem wt4 : wfMat BProg.t4 = true := (tM_strip 3 (by norm_num)).2
theorem wt5 : wfMat BProg.t5 = true := (tM_strip 4 (by norm_num)).2
theorem wt6 : wfMat BProg.t6 = true := (tM_strip 5 (by norm_num)).2
theorem wt7 : wfMat BProg.t7 = true := (tM_strip 6 (by norm_num)).2
theorem wt8 : wfMat BProg.t8 = true := (tM_strip 7 (by norm_num)).2
theorem wt9 : wfMat BProg.t9 = true := (tM_strip 8 (by norm_num)).2
theorem wt10 : wfMat BProg.t10 = true := (tM_strip 9 (by norm_num)).2
theorem wt11 : wfMat BProg.t11 = true := (tM_strip 10 (by norm_num)).2

theorem pR2 : PW BProg.t1 BProg.t2 B9201.r2 := prodW wt1 wt2 (by bm_strips CFSG.KC.BM.B9201.c_r2 69)
theorem pR3 : PW B9201.r2 BProg.t3 B9201.r3 := prodW pR2.1 wt3 (by bm_strips CFSG.KC.BM.B9201.c_r3 69)
theorem pR4 : PW B9201.r3 BProg.t4 B9201.r4 := prodW pR3.1 wt4 (by bm_strips CFSG.KC.BM.B9201.c_r4 69)
theorem pR5 : PW B9201.r4 BProg.t5 B9201.r5 := prodW pR4.1 wt5 (by bm_strips CFSG.KC.BM.B9201.c_r5 69)
theorem pR6 : PW B9201.r5 BProg.t6 B9201.r6 := prodW pR5.1 wt6 (by bm_strips CFSG.KC.BM.B9201.c_r6 69)
theorem pR7 : PW B9201.r6 BProg.t7 B9201.r7 := prodW pR6.1 wt7 (by bm_strips CFSG.KC.BM.B9201.c_r7 69)
theorem pR8 : PW B9201.r7 BProg.t8 B9201.r8 := prodW pR7.1 wt8 (by bm_strips CFSG.KC.BM.B9201.c_r8 69)
theorem pS2 : PW BProg.t5 BProg.t9 B9201.s2 := prodW wt5 wt9 (by bm_strips CFSG.KC.BM.B9201.c_s2 69)
theorem pS3 : PW B9201.s2 BProg.t10 B9201.s3 :=
  prodW pS2.1 wt10 (by bm_strips CFSG.KC.BM.B9201.c_s3 69)
theorem pS : PW B9201.s3 BProg.t11 B9201.s := prodW pS3.1 wt11 (by bm_strips CFSG.KC.BM.B9201.c_s 69)
theorem pRQ : PW B9201.r4 B9201.s B9201.rq := prodW pR4.1 pS.1 (by bm_strips CFSG.KC.BM.B9201.c_rq 69)
theorem pU : PW BProg.t7 BProg.t8 B9201.u := prodW wt7 wt8 (by bm_strips CFSG.KC.BM.B9201.c_u 69)
theorem pV : PW BProg.t10 BProg.t11 B9201.v := prodW wt10 wt11 (by bm_strips CFSG.KC.BM.B9201.c_v 69)
theorem pP2 : PW BProg.t5 BProg.t4 B9201.p2 := prodW wt5 wt4 (by bm_strips CFSG.KC.BM.B9201.c_p2 69)
theorem pP : PW B9201.p2 BProg.t3 B9201.p := prodW pP2.1 wt3 (by bm_strips CFSG.KC.BM.B9201.c_p 69)
theorem pX1 : PW B9201.p BProg.t5 B9201.x1 := prodW pP.1 wt5 (by bm_strips CFSG.KC.BM.B9201.c_x1 69)
theorem pX2 : PW B9201.x1 BProg.t6 B9201.x2w :=
  prodW pX1.1 wt6 (by bm_strips CFSG.KC.BM.B9201.c_x2w 69)
theorem pX3 : PW B9201.x2w BProg.t7 B9201.x3 :=
  prodW pX2.1 wt7 (by bm_strips CFSG.KC.BM.B9201.c_x3 69)
theorem pX4 : PW B9201.x3 BProg.t5 B9201.x4w :=
  prodW pX3.1 wt5 (by bm_strips CFSG.KC.BM.B9201.c_x4w 69)
theorem pX5 : PW B9201.x4w BProg.t9 B9201.x5w :=
  prodW pX4.1 wt9 (by bm_strips CFSG.KC.BM.B9201.c_x5w 69)
theorem pX : PW B9201.x5w BProg.t10 B9201.x := prodW pX5.1 wt10 (by bm_strips CFSG.KC.BM.B9201.c_x 69)
theorem pXX2 : PW B9201.x B9201.x B9201.xx2 := prodW pX.1 pX.1 (by bm_strips CFSG.KC.BM.B9201.c_xx2 69)
theorem pXX4 : PW B9201.xx2 B9201.xx2 B9201.xx4 :=
  prodW pXX2.1 pXX2.1 (by bm_strips CFSG.KC.BM.B9201.c_xx4 69)
theorem pXX5 : PW B9201.xx4 B9201.x B9201.xx5 :=
  prodW pXX4.1 pX.1 (by bm_strips CFSG.KC.BM.B9201.c_xx5 69)
theorem pP6 : PW B9201.p BProg.t6 B9201.p6 := prodW pP.1 wt6 (by bm_strips CFSG.KC.BM.B9201.c_p6 69)
theorem pY1 : PW B9201.p6 BProg.t7 B9201.y1 := prodW pP6.1 wt7 (by bm_strips CFSG.KC.BM.B9201.c_y1 69)
theorem pY2 : PW B9201.y1 BProg.t8 B9201.y2w :=
  prodW pY1.1 wt8 (by bm_strips CFSG.KC.BM.B9201.c_y2w 69)
theorem pY : PW B9201.y2w BProg.t9 B9201.y := prodW pY2.1 wt9 (by bm_strips CFSG.KC.BM.B9201.c_y 69)
theorem pYY2 : PW B9201.y B9201.y B9201.yy2 := prodW pY.1 pY.1 (by bm_strips CFSG.KC.BM.B9201.c_yy2 69)
theorem pYY4 : PW B9201.yy2 B9201.yy2 B9201.yy4 :=
  prodW pYY2.1 pYY2.1 (by bm_strips CFSG.KC.BM.B9201.c_yy4 69)
theorem pYY8 : PW B9201.yy4 B9201.yy4 B9201.yy8 :=
  prodW pYY4.1 pYY4.1 (by bm_strips CFSG.KC.BM.B9201.c_yy8 69)
theorem pZ1 : PW B9201.p6 BProg.t9 B9201.z1 := prodW pP6.1 wt9 (by bm_strips CFSG.KC.BM.B9201.c_z1 69)
theorem pZ2 : PW B9201.z1 BProg.t10 B9201.z2w :=
  prodW pZ1.1 wt10 (by bm_strips CFSG.KC.BM.B9201.c_z2w 69)
theorem pZ : PW B9201.z2w BProg.t11 B9201.z := prodW pZ2.1 wt11 (by bm_strips CFSG.KC.BM.B9201.c_z 69)
theorem pZZ2 : PW B9201.z B9201.z B9201.zz2 := prodW pZ.1 pZ.1 (by bm_strips CFSG.KC.BM.B9201.c_zz2 69)
theorem pZZ4 : PW B9201.zz2 B9201.zz2 B9201.zz4 :=
  prodW pZZ2.1 pZZ2.1 (by bm_strips CFSG.KC.BM.B9201.c_zz4 69)
theorem pZZ8 : PW B9201.zz4 B9201.zz4 B9201.zz8 :=
  prodW pZZ4.1 pZZ4.1 (by bm_strips CFSG.KC.BM.B9201.c_zz8 69)
theorem pRR2 : PW B9201.r8 B9201.r8 B9201.rr2 :=
  prodW pR8.1 pR8.1 (by bm_strips CFSG.KC.BM.B9201.c_rr2 69)
theorem pRR4 : PW B9201.rr2 B9201.rr2 B9201.rr4 :=
  prodW pRR2.1 pRR2.1 (by bm_strips CFSG.KC.BM.B9201.c_rr4 69)
theorem pRR6 : PW B9201.rr4 B9201.rr2 B9201.rr6 :=
  prodW pRR4.1 pRR2.1 (by bm_strips CFSG.KC.BM.B9201.c_rr6 69)
theorem pRR7 : PW B9201.rr6 B9201.r8 B9201.rr7 :=
  prodW pRR6.1 pR8.1 (by bm_strips CFSG.KC.BM.B9201.c_rr7 69)
theorem pW : PW B9201.rr7 B9201.s B9201.w := prodW pRR7.1 pS.1 (by bm_strips CFSG.KC.BM.B9201.c_w 69)
theorem pW2 : PW B9201.w B9201.w B9201.w2 := prodW pW.1 pW.1 (by bm_strips CFSG.KC.BM.B9201.c_w2 69)
theorem pW3 : PW B9201.w2 B9201.w B9201.w3 := prodW pW2.1 pW.1 (by bm_strips CFSG.KC.BM.B9201.c_w3 69)
theorem pW6 : PW B9201.w3 B9201.w3 B9201.w6 :=
  prodW pW3.1 pW3.1 (by bm_strips CFSG.KC.BM.B9201.c_w6 69)
theorem pW12 : PW B9201.w6 B9201.w6 B9201.w12 :=
  prodW pW6.1 pW6.1 (by bm_strips CFSG.KC.BM.B9201.c_w12 69)
theorem pAP : PW B9201.w12 B9201.w3 B9201.ap :=
  prodW pW12.1 pW3.1 (by bm_strips CFSG.KC.BM.B9201.c_ap 69)
theorem pSR : PW B9201.s B9201.r8 B9201.sr := prodW pS.1 pR8.1 (by bm_strips CFSG.KC.BM.B9201.c_sr 69)
theorem pH2 : PW B9201.sr B9201.sr B9201.h2 :=
  prodW pSR.1 pSR.1 (by bm_strips CFSG.KC.BM.B9201.c_h2 69)
theorem pH4 : PW B9201.h2 B9201.h2 B9201.h4 :=
  prodW pH2.1 pH2.1 (by bm_strips CFSG.KC.BM.B9201.c_h4 69)
theorem pH5 : PW B9201.h4 B9201.sr B9201.h5 :=
  prodW pH4.1 pSR.1 (by bm_strips CFSG.KC.BM.B9201.c_h5 69)
theorem pH : PW B9201.h5 B9201.h5 B9201.h := prodW pH5.1 pH5.1 (by bm_strips CFSG.KC.BM.B9201.c_h 69)
theorem pK : PW B9201.Gp B9201.h B9201.K :=
  prodW B9201.wf_Gp pH.1 (by bm_strips CFSG.KC.BM.B9201.c_K 69)

theorem t1sq : stripMat BProg.t1 * stripMat BProg.t1 = 1 :=
  stripMat_mul1_one wt1 wt1 (by bm_strips CFSG.KC.BM.B9201.t1sq 69)
theorem braid12 : stripMat B9201.r2 * stripMat B9201.r2 * stripMat B9201.r2 = 1 :=
  rel2one pR2.1 pR2.1 pR2.1 (by bm_strips CFSG.KC.BM.B9201.braid12 69)
theorem com3 : stripMat BProg.t1 * stripMat BProg.t3 = stripMat BProg.t3 * stripMat BProg.t1 :=
  rel11 wt1 wt3 wt3 wt1 (by bm_strips2 CFSG.KC.BM.B9201.com1_3 69)
theorem com4 : stripMat BProg.t1 * stripMat BProg.t4 = stripMat BProg.t4 * stripMat BProg.t1 :=
  rel11 wt1 wt4 wt4 wt1 (by bm_strips2 CFSG.KC.BM.B9201.com1_4 69)
theorem com5 : stripMat BProg.t1 * stripMat BProg.t5 = stripMat BProg.t5 * stripMat BProg.t1 :=
  rel11 wt1 wt5 wt5 wt1 (by bm_strips2 CFSG.KC.BM.B9201.com1_5 69)
theorem com6 : stripMat BProg.t1 * stripMat BProg.t6 = stripMat BProg.t6 * stripMat BProg.t1 :=
  rel11 wt1 wt6 wt6 wt1 (by bm_strips2 CFSG.KC.BM.B9201.com1_6 69)
theorem com7 : stripMat BProg.t1 * stripMat BProg.t7 = stripMat BProg.t7 * stripMat BProg.t1 :=
  rel11 wt1 wt7 wt7 wt1 (by bm_strips2 CFSG.KC.BM.B9201.com1_7 69)
theorem com8 : stripMat BProg.t1 * stripMat BProg.t8 = stripMat BProg.t8 * stripMat BProg.t1 :=
  rel11 wt1 wt8 wt8 wt1 (by bm_strips2 CFSG.KC.BM.B9201.com1_8 69)
theorem com9 : stripMat BProg.t1 * stripMat BProg.t9 = stripMat BProg.t9 * stripMat BProg.t1 :=
  rel11 wt1 wt9 wt9 wt1 (by bm_strips2 CFSG.KC.BM.B9201.com1_9 69)
theorem com10 : stripMat BProg.t1 * stripMat BProg.t10 = stripMat BProg.t10 * stripMat BProg.t1 :=
  rel11 wt1 wt10 wt10 wt1 (by bm_strips2 CFSG.KC.BM.B9201.com1_10 69)
theorem com11 : stripMat BProg.t1 * stripMat BProg.t11 = stripMat BProg.t11 * stripMat BProg.t1 :=
  rel11 wt1 wt11 wt11 wt1 (by bm_strips2 CFSG.KC.BM.B9201.com1_11 69)
theorem tr1 : stripMat B9201.r8 * stripMat BProg.t1 = stripMat BProg.t2 * stripMat B9201.r8 :=
  rel11 pR8.1 wt1 wt2 pR8.1 (by bm_strips2 CFSG.KC.BM.B9201.tr1 69)
theorem tr2 : stripMat B9201.r8 * stripMat BProg.t2 = stripMat BProg.t3 * stripMat B9201.r8 :=
  rel11 pR8.1 wt2 wt3 pR8.1 (by bm_strips2 CFSG.KC.BM.B9201.tr2 69)
theorem tr3 : stripMat B9201.r8 * stripMat BProg.t3 = stripMat BProg.t4 * stripMat B9201.r8 :=
  rel11 pR8.1 wt3 wt4 pR8.1 (by bm_strips2 CFSG.KC.BM.B9201.tr3 69)
theorem tr4 : stripMat B9201.r8 * stripMat BProg.t4 = stripMat BProg.t5 * stripMat B9201.r8 :=
  rel11 pR8.1 wt4 wt5 pR8.1 (by bm_strips2 CFSG.KC.BM.B9201.tr4 69)
theorem tr5 : stripMat B9201.r8 * stripMat BProg.t5 = stripMat BProg.t6 * stripMat B9201.r8 :=
  rel11 pR8.1 wt5 wt6 pR8.1 (by bm_strips2 CFSG.KC.BM.B9201.tr5 69)
theorem tr6 : stripMat B9201.r8 * stripMat BProg.t6 = stripMat BProg.t7 * stripMat B9201.r8 :=
  rel11 pR8.1 wt6 wt7 pR8.1 (by bm_strips2 CFSG.KC.BM.B9201.tr6 69)
theorem tr7 : stripMat B9201.r8 * stripMat BProg.t7 = stripMat BProg.t8 * stripMat B9201.r8 :=
  rel11 pR8.1 wt7 wt8 pR8.1 (by bm_strips2 CFSG.KC.BM.B9201.tr7 69)
theorem trq1 : stripMat B9201.rq * stripMat BProg.t1 = stripMat BProg.t2 * stripMat B9201.rq :=
  rel11 pRQ.1 wt1 wt2 pRQ.1 (by bm_strips2 CFSG.KC.BM.B9201.trq1 69)
theorem trq2 : stripMat B9201.rq * stripMat BProg.t2 = stripMat BProg.t3 * stripMat B9201.rq :=
  rel11 pRQ.1 wt2 wt3 pRQ.1 (by bm_strips2 CFSG.KC.BM.B9201.trq2 69)
theorem trq3 : stripMat B9201.rq * stripMat BProg.t3 = stripMat BProg.t4 * stripMat B9201.rq :=
  rel11 pRQ.1 wt3 wt4 pRQ.1 (by bm_strips2 CFSG.KC.BM.B9201.trq3 69)
theorem trq4 : stripMat B9201.rq * stripMat BProg.t4 = stripMat BProg.t5 * stripMat B9201.rq :=
  rel11 pRQ.1 wt4 wt5 pRQ.1 (by bm_strips2 CFSG.KC.BM.B9201.trq4 69)
theorem trq5 : stripMat B9201.rq * stripMat BProg.t5 = stripMat BProg.t9 * stripMat B9201.rq :=
  rel11 pRQ.1 wt5 wt9 pRQ.1 (by bm_strips2 CFSG.KC.BM.B9201.trq5 69)
theorem trq6 : stripMat B9201.rq * stripMat BProg.t9 = stripMat BProg.t10 * stripMat B9201.rq :=
  rel11 pRQ.1 wt9 wt10 pRQ.1 (by bm_strips2 CFSG.KC.BM.B9201.trq6 69)
theorem trq7 : stripMat B9201.rq * stripMat BProg.t10 = stripMat BProg.t11 * stripMat B9201.rq :=
  rel11 pRQ.1 wt10 wt11 pRQ.1 (by bm_strips2 CFSG.KC.BM.B9201.trq7 69)
theorem cross69 : stripMat BProg.t6 * stripMat BProg.t9 = stripMat BProg.t9 * stripMat BProg.t6 :=
  rel11 wt6 wt9 wt9 wt6 (by bm_strips2 CFSG.KC.BM.B9201.cross_6_9 69)
theorem cross6v : stripMat BProg.t6 * stripMat B9201.v = stripMat B9201.v * stripMat BProg.t6 :=
  rel11 wt6 pV.1 pV.1 wt6 (by bm_strips2 CFSG.KC.BM.B9201.cross_6_v 69)
theorem crossu9 : stripMat B9201.u * stripMat BProg.t9 = stripMat BProg.t9 * stripMat B9201.u :=
  rel11 pU.1 wt9 wt9 pU.1 (by bm_strips2 CFSG.KC.BM.B9201.cross_u_9 69)
theorem crossuv : stripMat B9201.u * stripMat B9201.v = stripMat B9201.v * stripMat B9201.u :=
  rel11 pU.1 pV.1 pV.1 pU.1 (by bm_strips2 CFSG.KC.BM.B9201.cross_u_v 69)
theorem spider : stripMat B9201.xx5 * stripMat B9201.xx5 = 1 :=
  stripMat_mul1_one pXX5.1 pXX5.1 (by bm_strips CFSG.KC.BM.B9201.spider 69)
theorem extra1 : stripMat B9201.yy8 * stripMat B9201.y = 1 :=
  stripMat_mul1_one pYY8.1 pY.1 (by bm_strips CFSG.KC.BM.B9201.extra1 69)
theorem extra2 : stripMat B9201.zz8 * stripMat B9201.z = 1 :=
  stripMat_mul1_one pZZ8.1 pZ.1 (by bm_strips CFSG.KC.BM.B9201.extra2 69)
theorem conjA : stripMat Seeds.A1 * stripMat B9201.K = stripMat B9201.K * stripMat B9201.ap :=
  rel11 Seeds.wf_A1 pK.1 pK.1 pAP.1 (by bm_strips2 CFSG.KC.BM.B9201.conjA 69)
theorem conjB : stripMat Seeds.A2 * stripMat B9201.Gp = stripMat B9201.Gp * stripMat B9201.r2 :=
  rel11 Seeds.wf_A2 B9201.wf_Gp B9201.wf_Gp pR2.1 (by bm_strips2 CFSG.KC.BM.B9201.conjB 69)
theorem conjI : stripMat B9201.Gp * stripMat B9201.Gip = 1 :=
  stripMat_mul1_one B9201.wf_Gp B9201.wf_Gip (by bm_strips CFSG.KC.BM.B9201.conjI 69)

theorem lp8 (t : ℕ → MM) (i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ℕ) :
    B9201.lp t [i₀, i₁, i₂, i₃, i₄, i₅, i₆, i₇] =
      t i₀ * t i₁ * t i₂ * t i₃ * t i₄ * t i₅ * t i₆ * t i₇ := by
  change t i₀ * (t i₁ * (t i₂ * (t i₃ * (t i₄ * (t i₅ * (t i₆ * (t i₇ * 1))))))) = _
  rw [Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem lp7 (t : ℕ → MM) (i₀ i₁ i₂ i₃ i₄ i₅ i₆ : ℕ) :
    B9201.lp t [i₀, i₁, i₂, i₃, i₄, i₅, i₆] = t i₀ * t i₁ * t i₂ * t i₃ * t i₄ * t i₅ * t i₆ := by
  change t i₀ * (t i₁ * (t i₂ * (t i₃ * (t i₄ * (t i₅ * (t i₆ * 1)))))) = _
  rw [Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem lp9 (t : ℕ → MM) (i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ : ℕ) :
    B9201.lp t [i₀, i₁, i₂, i₃, i₄, i₅, i₆, i₇, i₈] =
      t i₀ * t i₁ * t i₂ * t i₃ * t i₄ * t i₅ * t i₆ * t i₇ * t i₈ := by
  change t i₀ * (t i₁ * (t i₂ * (t i₃ * (t i₄ * (t i₅ * (t i₆ * (t i₇ * (t i₈ * 1)))))))) = _
  rw [Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem lp4 (t : ℕ → MM) (i₀ i₁ i₂ i₃ : ℕ) :
    B9201.lp t [i₀, i₁, i₂, i₃] = t i₀ * t i₁ * t i₂ * t i₃ := by
  change t i₀ * (t i₁ * (t i₂ * (t i₃ * 1))) = _
  rw [Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem b9201Facts_of {a b : MM} {t : ℕ → MM} {R RQ S X Y Z G Gi : MM}
    (ht : ∀ k < 11, B9201.tM a b k = t k)
    (hR : t 0 * t 1 * t 2 * t 3 * t 4 * t 5 * t 6 * t 7 = R)
    (hRQ : t 0 * t 1 * t 2 * t 3 * t 4 * t 8 * t 9 * t 10 = RQ)
    (hS : t 4 * t 8 * t 9 * t 10 = S)
    (hX : t 4 * t 3 * t 2 * t 4 * t 5 * t 6 * t 4 * t 8 * t 9 = X)
    (hY : t 4 * t 3 * t 2 * t 5 * t 6 * t 7 * t 8 = Y)
    (hZ : t 4 * t 3 * t 2 * t 5 * t 8 * t 9 * t 10 = Z)
    (h1 : t 0 * t 0 = 1) (h2 : t 0 * t 1 * (t 0 * t 1) * (t 0 * t 1) = 1)
    (h3 : ∀ j ∈ [2, 3, 4, 5, 6, 7, 8, 9, 10], t 0 * t j = t j * t 0)
    (h4 : ∀ i < 7, R * t i = t (i + 1) * R)
    (h5 : ∀ i < 7, RQ * t (B9201.chain2.getD i 0) = t (B9201.chain2.getD (i + 1) 0) * RQ)
    (h6 : t 5 * t 8 = t 8 * t 5) (h7 : t 5 * (t 9 * t 10) = t 9 * t 10 * t 5)
    (h8 : t 6 * t 7 * t 8 = t 8 * (t 6 * t 7))
    (h9 : t 6 * t 7 * (t 9 * t 10) = t 9 * t 10 * (t 6 * t 7))
    (hx : X ^ 10 = 1) (hy : Y ^ 9 = 1) (hz : Z ^ 9 = 1)
    (hb : b * G = G * (t 0 * t 1))
    (ha : a * (G * (S * R) ^ 10) = G * (S * R) ^ 10 * (R ^ 7 * S) ^ 15)
    (hi : G * Gi = 1) : B9201.B9201Facts a b := by
  have eR : B9201.rT t = R := (lp8 t 0 1 2 3 4 5 6 7).trans hR
  have eRQ : B9201.rqT t = RQ := (lp8 t 0 1 2 3 4 8 9 10).trans hRQ
  have eS : B9201.sT t = S := (lp4 t 4 8 9 10).trans hS
  have eX : B9201.lp t [4, 3, 2, 4, 5, 6, 4, 8, 9] = X := (lp9 t 4 3 2 4 5 6 4 8 9).trans hX
  have eY : B9201.lp t [4, 3, 2, 5, 6, 7, 8] = Y := (lp7 t 4 3 2 5 6 7 8).trans hY
  have eZ : B9201.lp t [4, 3, 2, 5, 8, 9, 10] = Z := (lp7 t 4 3 2 5 8 9 10).trans hZ
  refine ⟨t, ht, ⟨h1, ?_, h3, ?_, ?_, h6, h7, h8, h9, ?_, ?_, ?_⟩, G, Gi, hb, ?_, hi⟩
  · rw [pow_three']
    exact h2
  · rw [eR]
    exact h4
  · rw [eRQ]
    exact h5
  · rw [eX]
    exact hx
  · rw [eY]
    exact hy
  · rw [eZ]
    exact hz
  · rw [B9201.hT, B9201.apT, eR, eS]
    exact ha

@[expose] noncomputable def tS (k : ℕ) : MM := stripMat (tL.getD k [])

theorem pw1 (x : MM) : x ^ 1 = x := pow_one x

theorem x_pow : stripMat B9201.x ^ 10 = 1 := by
  have h2 : stripMat B9201.x ^ 2 = stripMat B9201.xx2 := pw_dbl (pw1 _) pXX2.2 rfl
  have h4 : stripMat B9201.x ^ 4 = stripMat B9201.xx4 := pw_dbl h2 pXX4.2 rfl
  have h5 : stripMat B9201.x ^ 5 = stripMat B9201.xx5 := pw_add h4 (pw1 _) pXX5.2 rfl
  exact pw_dbl h5 spider rfl

theorem y_pow : stripMat B9201.y ^ 9 = 1 := by
  have h2 : stripMat B9201.y ^ 2 = stripMat B9201.yy2 := pw_dbl (pw1 _) pYY2.2 rfl
  have h4 : stripMat B9201.y ^ 4 = stripMat B9201.yy4 := pw_dbl h2 pYY4.2 rfl
  have h8 : stripMat B9201.y ^ 8 = stripMat B9201.yy8 := pw_dbl h4 pYY8.2 rfl
  exact pw_add h8 (pw1 _) extra1 rfl

theorem z_pow : stripMat B9201.z ^ 9 = 1 := by
  have h2 : stripMat B9201.z ^ 2 = stripMat B9201.zz2 := pw_dbl (pw1 _) pZZ2.2 rfl
  have h4 : stripMat B9201.z ^ 4 = stripMat B9201.zz4 := pw_dbl h2 pZZ4.2 rfl
  have h8 : stripMat B9201.z ^ 8 = stripMat B9201.zz8 := pw_dbl h4 pZZ8.2 rfl
  exact pw_add h8 (pw1 _) extra2 rfl

theorem ap_eq : (stripMat B9201.r8 ^ 7 * stripMat B9201.s) ^ 15 = stripMat B9201.ap := by
  have r2 : stripMat B9201.r8 ^ 2 = stripMat B9201.rr2 := pw_dbl (pw1 _) pRR2.2 rfl
  have r4 : stripMat B9201.r8 ^ 4 = stripMat B9201.rr4 := pw_dbl r2 pRR4.2 rfl
  have r6 : stripMat B9201.r8 ^ 6 = stripMat B9201.rr6 := pw_add r4 r2 pRR6.2 rfl
  have r7 : stripMat B9201.r8 ^ 7 = stripMat B9201.rr7 := pw_add r6 (pw1 _) pRR7.2 rfl
  rw [r7, pW.2]
  have w2 : stripMat B9201.w ^ 2 = stripMat B9201.w2 := pw_dbl (pw1 _) pW2.2 rfl
  have w3 : stripMat B9201.w ^ 3 = stripMat B9201.w3 := pw_add w2 (pw1 _) pW3.2 rfl
  have w6 : stripMat B9201.w ^ 6 = stripMat B9201.w6 := pw_dbl w3 pW6.2 rfl
  have w12 : stripMat B9201.w ^ 12 = stripMat B9201.w12 := pw_dbl w6 pW12.2 rfl
  exact pw_add w12 w3 pAP.2 rfl

theorem h_eq : (stripMat B9201.s * stripMat B9201.r8) ^ 10 = stripMat B9201.h := by
  rw [pSR.2]
  have h2 : stripMat B9201.sr ^ 2 = stripMat B9201.h2 := pw_dbl (pw1 _) pH2.2 rfl
  have h4 : stripMat B9201.sr ^ 4 = stripMat B9201.h4 := pw_dbl h2 pH4.2 rfl
  have h5 : stripMat B9201.sr ^ 5 = stripMat B9201.h5 := pw_add h4 (pw1 _) pH5.2 rfl
  exact pw_dbl h5 pH.2 rfl

theorem b9201Facts_strip : B9201.B9201Facts (stripMat Seeds.A1) (stripMat Seeds.A2) := by
  refine b9201Facts_of (t := tS) (R := stripMat B9201.r8) (RQ := stripMat B9201.rq)
    (S := stripMat B9201.s) (X := stripMat B9201.x) (Y := stripMat B9201.y) (Z := stripMat B9201.z)
    (G := stripMat B9201.Gp) (Gi := stripMat B9201.Gip) (fun k hk => (tM_strip k hk).1)
    ?_ ?_ ?_ ?_ ?_ ?_ t1sq ?_ ?_ ?_ ?_ cross69 ?_ ?_ ?_ x_pow y_pow z_pow ?_ ?_ conjI
  · change stripMat BProg.t1 * stripMat BProg.t2 * stripMat BProg.t3 * stripMat BProg.t4 *
      stripMat BProg.t5 * stripMat BProg.t6 * stripMat BProg.t7 * stripMat BProg.t8 = _
    rw [pR2.2, pR3.2, pR4.2, pR5.2, pR6.2, pR7.2, pR8.2]
  · change stripMat BProg.t1 * stripMat BProg.t2 * stripMat BProg.t3 * stripMat BProg.t4 *
      stripMat BProg.t5 * stripMat BProg.t9 * stripMat BProg.t10 * stripMat BProg.t11 = _
    rw [pR2.2, pR3.2, pR4.2, ← pRQ.2, ← pS.2, ← pS3.2, ← pS2.2]
    simp only [Matrix.mul_assoc]
  · change stripMat BProg.t5 * stripMat BProg.t9 * stripMat BProg.t10 * stripMat BProg.t11 = _
    rw [pS2.2, pS3.2, pS.2]
  · change stripMat BProg.t5 * stripMat BProg.t4 * stripMat BProg.t3 * stripMat BProg.t5 *
      stripMat BProg.t6 * stripMat BProg.t7 * stripMat BProg.t5 * stripMat BProg.t9 *
      stripMat BProg.t10 = _
    rw [pP2.2, pP.2, pX1.2, pX2.2, pX3.2, pX4.2, pX5.2, pX.2]
  · change stripMat BProg.t5 * stripMat BProg.t4 * stripMat BProg.t3 * stripMat BProg.t6 *
      stripMat BProg.t7 * stripMat BProg.t8 * stripMat BProg.t9 = _
    rw [pP2.2, pP.2, pP6.2, pY1.2, pY2.2, pY.2]
  · change stripMat BProg.t5 * stripMat BProg.t4 * stripMat BProg.t3 * stripMat BProg.t6 *
      stripMat BProg.t9 * stripMat BProg.t10 * stripMat BProg.t11 = _
    rw [pP2.2, pP.2, pP6.2, pZ1.2, pZ2.2, pZ.2]
  · change stripMat BProg.t1 * stripMat BProg.t2 * (stripMat BProg.t1 * stripMat BProg.t2) *
      (stripMat BProg.t1 * stripMat BProg.t2) = 1
    rw [pR2.2]
    exact braid12
  · intro j hj
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [com3, com4, com5, com6, com7, com8, com9, com10, com11]
  · intro i hi
    interval_cases i
    exacts [tr1, tr2, tr3, tr4, tr5, tr6, tr7]
  · intro i hi
    interval_cases i
    exacts [trq1, trq2, trq3, trq4, trq5, trq6, trq7]
  · change stripMat BProg.t6 * (stripMat BProg.t10 * stripMat BProg.t11) =
      stripMat BProg.t10 * stripMat BProg.t11 * stripMat BProg.t6
    rw [pV.2]
    exact cross6v
  · change stripMat BProg.t7 * stripMat BProg.t8 * stripMat BProg.t9 =
      stripMat BProg.t9 * (stripMat BProg.t7 * stripMat BProg.t8)
    rw [pU.2]
    exact crossu9
  · change stripMat BProg.t7 * stripMat BProg.t8 * (stripMat BProg.t10 * stripMat BProg.t11) =
      stripMat BProg.t10 * stripMat BProg.t11 * (stripMat BProg.t7 * stripMat BProg.t8)
    rw [pU.2, pV.2]
    exact crossuv
  · change stripMat Seeds.A2 * stripMat B9201.Gp =
      stripMat B9201.Gp * (stripMat BProg.t1 * stripMat BProg.t2)
    rw [pR2.2]
    exact conjB
  · rw [h_eq, ap_eq, pK.2]
    exact conjA

end CertificateChecks.KernelBM.Run9201

end
