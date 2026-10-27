module

public import Certificates.Kernel.BabyMonster.SevenElem
public import CFSG.Certificates.Kernel.BabyMonster.SevenLocal.All

public section

namespace CertificateChecks.KernelBM.SevenFacts

open CFSG.KC.BM CFSG.KC.BM.SevenFacts CertificateChecks.KernelBM.SevenGen
  CertificateChecks.KernelBM.FiveA
open scoped Matrix

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

set_option maxRecDepth 100000

theorem e2_eq : stripMat SevenElem.e2 = stripMat Seven.e3 ^ 2 := by
  rw [← p1 SevenElem.e2 Seven.wf_e3 Seven.wf_e3 (by bm_strips4 CFSG.KC.BM.SevenElem.c_e2 69), sq]

theorem pp0 : stripMat SevenLocal.p0 = stripMat Seven.y * stripMat Seven.e3 :=
  (p1 _ Seven.wf_y Seven.wf_e3 (by bm_strips4 CFSG.KC.BM.SevenLocal.c_p0 69)).symm

theorem pp1 : stripMat SevenLocal.p1 = stripMat SevenElem.e2 * stripMat Seven.r43 :=
  (p1 _ SevenElem.wf_e2 Seven.wf_r43 (by bm_strips4 CFSG.KC.BM.SevenLocal.c_p1 69)).symm

theorem pp2 : stripMat SevenLocal.p2 = stripMat SevenElem.e2 * stripMat Seven.t2 :=
  (p1 _ SevenElem.wf_e2 Seven.wf_t2 (by bm_strips4 CFSG.KC.BM.SevenLocal.c_p2 69)).symm

theorem pp3 : stripMat SevenLocal.p3 = stripMat SevenLocal.p0 * stripMat Seven.y4 :=
  (p1 _ SevenLocal.wf_p0 Seven.wf_y4 (by bm_strips4 CFSG.KC.BM.SevenLocal.c_p3 69)).symm

theorem pp4 : stripMat SevenLocal.p4 = stripMat SevenLocal.p3 * stripMat Seven.t2 :=
  (p1 _ SevenLocal.wf_p3 Seven.wf_t2 (by bm_strips4 CFSG.KC.BM.SevenLocal.c_p4 69)).symm

theorem pp5 : stripMat SevenLocal.p5 = stripMat Seven.y4 * stripMat Seven.e3 :=
  (p1 _ Seven.wf_y4 Seven.wf_e3 (by bm_strips4 CFSG.KC.BM.SevenLocal.c_p5 69)).symm

theorem ps3 : stripMat SevenLocal.s3 = stripMat SevenElem.e2 * stripMat SevenLocal.p4 *
    stripMat Seven.y4 * stripMat SevenLocal.p1 * stripMat Seven.r43 := by
  have e := stripMat_mul_of_allStrips
    (Ws := [SevenLocal.p4, Seven.y4, SevenLocal.p1, Seven.r43]) (C := SevenLocal.s3)
    (by simp [SevenLocal.wf_p4, Seven.wf_y4, SevenLocal.wf_p1, Seven.wf_r43]) SevenElem.wf_e2
    (by bm_strips4 CFSG.KC.BM.SevenLocal.c_s3 69)
  simpa using e.symm

theorem ps4 : stripMat SevenLocal.s4 = stripMat SevenElem.e2 * stripMat Seven.y4 *
    stripMat SevenLocal.p2 * stripMat SevenLocal.p0 := by
  have e := stripMat_mul_of_allStrips (Ws := [Seven.y4, SevenLocal.p2, SevenLocal.p0]) (C := SevenLocal.s4)
    (by simp [Seven.wf_y4, SevenLocal.wf_p2, SevenLocal.wf_p0]) SevenElem.wf_e2
    (by bm_strips4 CFSG.KC.BM.SevenLocal.c_s4 69)
  simpa using e.symm

theorem pf : stripMat SevenLocal.f = stripMat Seven.y * stripMat Seven.r43 *
    stripMat SevenLocal.p2 * stripMat Seven.y * stripMat SevenElem.e2 * stripMat Seven.y *
    stripMat SevenLocal.p0 := by
  have e := stripMat_mul_of_allStrips
    (Ws := [Seven.r43, SevenLocal.p2, Seven.y, SevenElem.e2, Seven.y, SevenLocal.p0])
    (C := SevenLocal.f)
    (by simp [Seven.wf_r43, SevenLocal.wf_p2, Seven.wf_y, SevenElem.wf_e2, SevenLocal.wf_p0])
    Seven.wf_y (by bm_strips4 CFSG.KC.BM.SevenLocal.c_f 69)
  simpa using e.symm

theorem pu1 : stripMat SevenLocal.u1 = stripMat SevenLocal.p5 * stripMat SevenLocal.p5 *
    stripMat SevenLocal.p0 * stripMat SevenLocal.p0 := by
  have e := stripMat_mul_of_allStrips (Ws := [SevenLocal.p5, SevenLocal.p0, SevenLocal.p0]) (C := SevenLocal.u1)
    (by simp [SevenLocal.wf_p5, SevenLocal.wf_p0]) SevenLocal.wf_p5
    (by bm_strips4 CFSG.KC.BM.SevenLocal.c_u1 69)
  simpa using e.symm

theorem pu2 : stripMat SevenLocal.u2 = stripMat SevenLocal.p4 * stripMat Seven.y2 *
    stripMat SevenLocal.p1 := by
  have e := stripMat_mul_of_allStrips (Ws := [Seven.y2, SevenLocal.p1]) (C := SevenLocal.u2)
    (by simp [Seven.wf_y2, SevenLocal.wf_p1]) SevenLocal.wf_p4
    (by bm_strips4 CFSG.KC.BM.SevenLocal.c_u2 69)
  simpa using e.symm

theorem words_comm {Z : MatB} (hy : Commute (stripMat Seven.y) Z)
    (ht : Commute (stripMat Seven.t1) Z) (ht2 : Commute (stripMat Seven.t2) Z)
    (he : Commute (stripMat Seven.e3) Z) :
    Commute (stripMat SevenLocal.s3) Z ∧ Commute (stripMat SevenLocal.s4) Z ∧
      Commute (stripMat SevenLocal.f) Z ∧ Commute (stripMat SevenLocal.u1) Z ∧
      Commute (stripMat SevenLocal.u2) Z := by
  have hy2 : Commute (stripMat Seven.y2) Z := by rw [y2_eq]; exact cpow hy 2
  have hy4 : Commute (stripMat Seven.y4) Z := by rw [y4_eq]; exact cpow hy 4
  have he2 : Commute (stripMat SevenElem.e2) Z := by rw [e2_eq]; exact cpow he 2
  have h43 : Commute (stripMat Seven.r43) Z := by rw [r43_eq]; exact ht.mul_left hy
  have h0 : Commute (stripMat SevenLocal.p0) Z := by rw [pp0]; exact hy.mul_left he
  have h1 : Commute (stripMat SevenLocal.p1) Z := by rw [pp1]; exact he2.mul_left h43
  have h2 : Commute (stripMat SevenLocal.p2) Z := by rw [pp2]; exact he2.mul_left ht2
  have h3 : Commute (stripMat SevenLocal.p3) Z := by rw [pp3]; exact h0.mul_left hy4
  have h4 : Commute (stripMat SevenLocal.p4) Z := by rw [pp4]; exact h3.mul_left ht2
  have h5 : Commute (stripMat SevenLocal.p5) Z := by rw [pp5]; exact hy4.mul_left he
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [ps3]
    exact (((he2.mul_left h4).mul_left hy4).mul_left h1).mul_left h43
  · rw [ps4]
    exact ((he2.mul_left hy4).mul_left h2).mul_left h0
  · rw [pf]
    exact (((((hy.mul_left h43).mul_left h2).mul_left hy).mul_left he2).mul_left hy).mul_left h0
  · rw [pu1]
    exact ((h5.mul_left h5).mul_left h0).mul_left h0
  · rw [pu2]
    exact (h4.mul_left hy2).mul_left h1

theorem vecMul_pow_fix {v : Fin 4370 → ZMod 2} {X : MatB} (h : v ᵥ* X = v) :
    ∀ i : ℕ, v ᵥ* X ^ i = v
  | 0 => by rw [pow_zero, Matrix.vecMul_one]
  | i + 1 => by rw [pow_succ, ← Matrix.vecMul_vecMul, vecMul_pow_fix h i, h]

theorem move_row_f : vrow (rowOf CFSG.KC.BM.SevenGen.vf 0) ᵥ* stripMat SevenLocal.f ≠
    vrow (rowOf CFSG.KC.BM.SevenGen.vf 0) := by
  intro e
  have h1 := mulS_rows SevenLocal.wf_f CFSG.KC.BM.SevenGen.vf (t := 0) (by norm_num)
  rw [e] at h1
  have hm := CFSG.KC.BM.SevenLocal.move_f
  rw [rowOf_inj h1, Nat.beq_refl] at hm
  exact absurd hm (by decide)

theorem rk (M P R : List Nat) {k : ℕ} (hk : k ≤ 4370) (hM : wfMat M = true)
    (hP : wfMat P = true) (hR : wfMat R = true) (hrk : CFSG.KC.BM.Fix.AllStripsX M P R)
    (hs : shapeOK R k = true) (he : echFrom P k = true) : (stripMat M - 1).rank = k :=
  rank_sub_one_of_cert hk hM hP hR hrk hs he

theorem fact17450 : CFSG.KC.BM.SevenFacts.Fact17450 := by
  obtain ⟨hg_al, hy_al, ht_al⟩ := al_comm
  obtain ⟨hy_x, ht_x⟩ := x_comm
  obtain ⟨-, -, he_x, ht2_x⟩ := ty_comm ht_x hy_x
  obtain ⟨-, -, he_al, ht2_al⟩ := ty_comm ht_al hy_al
  obtain ⟨hs3_x, hs4_x, hf_x, hu1_x, hu2_x⟩ := words_comm hy_x ht_x ht2_x he_x
  obtain ⟨-, -, hf_al, -, -⟩ := words_comm hy_al ht_al ht2_al he_al
  have hw3 : stripMat SevenLocal.s3 = w3W (stripMat Seven.y) (stripMat Seven.t1)
      (stripMat Seven.t2) (stripMat Seven.e3) := by
    rw [ps3, pp4, pp3, pp0, pp1, r43_eq, e2_eq, y4_eq, w3W]
    simp only [mul_assoc]
  have hw4 : stripMat SevenLocal.s4 = w4W (stripMat Seven.y) (stripMat Seven.t2)
      (stripMat Seven.e3) := by
    rw [ps4, pp2, pp0, e2_eq, y4_eq, w4W]
    simp only [mul_assoc]
  have hwf : stripMat SevenLocal.f = fW (stripMat Seven.y) (stripMat Seven.t1)
      (stripMat Seven.t2) (stripMat Seven.e3) := by
    rw [pf, pp2, pp0, r43_eq, e2_eq, fW]
    simp only [mul_assoc]
  have hv1 : stripMat SevenLocal.u1 = v1W (stripMat Seven.y) (stripMat Seven.e3) := by
    rw [pu1, pp5, pp0, y4_eq, v1W]
    simp only [mul_assoc]
  have hv2 : stripMat SevenLocal.u2 = v2W (stripMat Seven.y) (stripMat Seven.t1)
      (stripMat Seven.t2) (stripMat Seven.e3) := by
    rw [pu2, pp4, pp3, pp0, pp1, r43_eq, e2_eq, y4_eq, y2_eq, v2W]
    simp only [mul_assoc, sq]
  have hs3sq : stripMat SevenLocal.s3 * stripMat SevenLocal.s3 = 1 :=
    p1one SevenLocal.wf_s3 SevenLocal.wf_s3 (by bm_strips4 CFSG.KC.BM.SevenLocal.inv_s3 69)
  have hs4sq : stripMat SevenLocal.s4 * stripMat SevenLocal.s4 = 1 :=
    p1one SevenLocal.wf_s4 SevenLocal.wf_s4 (by bm_strips4 CFSG.KC.BM.SevenLocal.inv_s4 69)
  have hu1c : stripMat SevenLocal.u1 ^ 3 = 1 := by
    rw [← pow3, p1 SevenLocal.u1p2 SevenLocal.wf_u1 SevenLocal.wf_u1
      (by bm_strips4 CFSG.KC.BM.SevenLocal.c_u1p2 69)]
    exact p1one SevenLocal.wf_u1p2 SevenLocal.wf_u1 (by bm_strips4 CFSG.KC.BM.SevenLocal.ord_u1 69)
  have hu2c : stripMat SevenLocal.u2 ^ 3 = 1 := by
    rw [← pow3, p1 SevenLocal.u2p2 SevenLocal.wf_u2 SevenLocal.wf_u2
      (by bm_strips4 CFSG.KC.BM.SevenLocal.c_u2p2 69)]
    exact p1one SevenLocal.wf_u2p2 SevenLocal.wf_u2 (by bm_strips4 CFSG.KC.BM.SevenLocal.ord_u2 69)
  have ef2 : stripMat SevenLocal.f2 = stripMat SevenLocal.f ^ 2 := by
    rw [← p1 SevenLocal.f2 SevenLocal.wf_f SevenLocal.wf_f
      (by bm_strips4 CFSG.KC.BM.SevenLocal.c_f2 69), sq]
  have ef3 : stripMat SevenLocal.f3 = stripMat SevenLocal.f ^ 3 := by
    rw [← p1 SevenLocal.f3 SevenLocal.wf_f2 SevenLocal.wf_f
      (by bm_strips4 CFSG.KC.BM.SevenLocal.c_f3 69), ef2, ← pow_succ]
  have ef4 : stripMat SevenLocal.f4 = stripMat SevenLocal.f ^ 4 := by
    rw [← p1 SevenLocal.f4 SevenLocal.wf_f2 SevenLocal.wf_f2
      (by bm_strips4 CFSG.KC.BM.SevenLocal.c_f4 69), ef2, ← pow_add]
  have ef5 : stripMat SevenLocal.f5 = stripMat SevenLocal.f ^ 5 := by
    rw [← p1 SevenLocal.f5 SevenLocal.wf_f4 SevenLocal.wf_f
      (by bm_strips4 CFSG.KC.BM.SevenLocal.c_f5 69), ef4, ← pow_succ]
  have ef6 : stripMat SevenLocal.f6 = stripMat SevenLocal.f ^ 6 := by
    rw [← p1 SevenLocal.f6 SevenLocal.wf_f3 SevenLocal.wf_f3
      (by bm_strips4 CFSG.KC.BM.SevenLocal.c_f6 69), ef3, ← pow_add]
  have hf7 : stripMat SevenLocal.f ^ 7 = 1 := by
    rw [pow_succ, ← ef6]
    exact p1one SevenLocal.wf_f6 SevenLocal.wf_f (by bm_strips4 CFSG.KC.BM.SevenLocal.ord_f 69)
  have et1x : stripMat Seven.t1 * stripMat Seven.x = stripMat SevenElem.t1x :=
    p1 SevenElem.t1x Seven.wf_t1 Seven.wf_x (by bm_strips4 CFSG.KC.BM.SevenElem.c_t1x 69)
  have ealx : stripMat Seven.al * stripMat Seven.x = stripMat SevenLocal.alx :=
    p1 SevenLocal.alx Seven.wf_al Seven.wf_x (by bm_strips4 CFSG.KC.BM.SevenLocal.c_alx 69)
  have et1xf : ∀ (F G : List Nat), wfMat F = true → AllStrips [F] SevenElem.t1x G →
      stripMat Seven.t1 * (stripMat Seven.x * stripMat F) = stripMat G := fun F G hF h => by
    rw [← mul_assoc, et1x]
    exact p1 G SevenElem.wf_t1x hF h
  have ealxf : ∀ (F G : List Nat), wfMat F = true → AllStrips [F] SevenLocal.alx G →
      stripMat Seven.al * (stripMat Seven.x * stripMat F) = stripMat G := fun F G hF h => by
    rw [← mul_assoc, ealx]
    exact p1 G SevenLocal.wf_alx hF h
  have ets3 : stripMat Seven.t1 * stripMat SevenLocal.s3 = stripMat SevenLocal.ts3 :=
    p1 SevenLocal.ts3 Seven.wf_t1 SevenLocal.wf_s3 (by bm_strips4 CFSG.KC.BM.SevenLocal.c_ts3 69)
  have ets4 : stripMat Seven.t1 * stripMat SevenLocal.s4 = stripMat SevenLocal.ts4 :=
    p1 SevenLocal.ts4 Seven.wf_t1 SevenLocal.wf_s4 (by bm_strips4 CFSG.KC.BM.SevenLocal.c_ts4 69)
  have ets4p2 : (stripMat Seven.t1 * stripMat SevenLocal.s4) ^ 2 = stripMat SevenLocal.ts4p2 := by
    rw [ets4, sq]
    exact p1 SevenLocal.ts4p2 SevenLocal.wf_ts4 SevenLocal.wf_ts4
      (by bm_strips4 CFSG.KC.BM.SevenLocal.c_ts4p2 69)
  have eu12 : stripMat SevenLocal.u1 * stripMat SevenLocal.u2 = stripMat SevenLocal.u12 :=
    p1 SevenLocal.u12 SevenLocal.wf_u1 SevenLocal.wf_u2 (by bm_strips4 CFSG.KC.BM.SevenLocal.c_u12 69)
  have hrts4 : (stripMat SevenLocal.ts4p2 - 1).rank = 2048 :=
    rk _ _ _ (by norm_num) SevenLocal.wf_ts4p2 SevenLocal.wf_PrkTs4 SevenLocal.wf_RrkTs4
      (by bm_stripsx CFSG.KC.BM.SevenLocal.rkTs4_ 69) SevenLocal.shape_rkTs4 SevenLocal.ech_rkTs4
  have hru1 : (stripMat SevenLocal.u1 - 1).rank = 2862 :=
    rk _ _ _ (by norm_num) SevenLocal.wf_u1 SevenLocal.wf_PrkU1 SevenLocal.wf_RrkU1
      (by bm_stripsx CFSG.KC.BM.SevenLocal.rkU1_ 69) SevenLocal.shape_rkU1 SevenLocal.ech_rkU1
  have hru2 : (stripMat SevenLocal.u2 - 1).rank = 2862 :=
    rk _ _ _ (by norm_num) SevenLocal.wf_u2 SevenLocal.wf_PrkU2 SevenLocal.wf_RrkU2
      (by bm_stripsx CFSG.KC.BM.SevenLocal.rkU2_ 69) SevenLocal.shape_rkU2 SevenLocal.ech_rkU2
  have hu2ne : stripMat SevenLocal.u2 ≠ 1 := ne_one_of_rank hru2 (by norm_num)
  have hfix := fix_row
  have hw3sq := hs3sq
  rw [hw3] at hw3sq
  have hw4sq := hs4sq
  rw [hw4] at hw4sq
  have hv1c := hu1c
  rw [hv1] at hv1c
  have hv2c := hu2c
  rw [hv2] at hv2c
  refine ⟨sevenWords, by rw [hw3, pow7_of_sq hw3sq], by rw [hw4, pow7_of_sq hw4sq], hwf,
    by rw [hv1, pow7_of_cube hv1c], by rw [hv2, pow7_of_cube hv2c], ?_⟩
  refine ⟨?_, ?_, ?_, hs3sq, ?_, hs3_x.eq, ?_, ?_, hs4sq, ?_, hs4_x.eq, ?_, ?_, ?_, hf7,
    notId_sound SevenLocal.wf_f SevenLocal.ne_f, hf_x.eq, hf_al.eq, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, hu1c, ne_one_of_rank hru1 (by norm_num), hu2c, hu2ne, hu1_x.eq, hu2_x.eq, ?_, ?_,
    hru1, hru2, ?_, ?_⟩
  · rw [ealx]
    exact rk _ _ _ (by norm_num) SevenLocal.wf_alx SevenLocal.wf_PrkAlX SevenLocal.wf_RrkAlX
      (by bm_stripsx CFSG.KC.BM.SevenLocal.rkAlX_ 69) SevenLocal.shape_rkAlX SevenLocal.ech_rkAlX
  · rw [p1 CFSG.KC.BM.SevenGen.alt1 Seven.wf_al Seven.wf_t1
      (by bm_strips CFSG.KC.BM.SevenGen.c_alt1 69)]
    exact rk _ _ _ (by norm_num) CFSG.KC.BM.SevenGen.wf_alt1 SevenLocal.wf_PrkAlT1
      SevenLocal.wf_RrkAlT1 (by bm_stripsx CFSG.KC.BM.SevenLocal.rkAlT1_ 69)
      SevenLocal.shape_rkAlT1 SevenLocal.ech_rkAlT1
  · rw [et1x]
    exact rk _ _ _ (by norm_num) SevenElem.wf_t1x SevenLocal.wf_PrkT1X SevenLocal.wf_RrkT1X
      (by bm_stripsx CFSG.KC.BM.SevenLocal.rkT1X_ 69) SevenLocal.shape_rkT1X SevenLocal.ech_rkT1X
  · exact rk _ _ _ (by norm_num) SevenLocal.wf_s3 SevenLocal.wf_PrkS3 SevenLocal.wf_RrkS3
      (by bm_stripsx CFSG.KC.BM.SevenLocal.rkS3_ 69) SevenLocal.shape_rkS3 SevenLocal.ech_rkS3
  · rw [ets3, ← pow3, p1 SevenLocal.ts3p2 SevenLocal.wf_ts3 SevenLocal.wf_ts3
      (by bm_strips4 CFSG.KC.BM.SevenLocal.c_ts3p2 69)]
    exact p1one SevenLocal.wf_ts3p2 SevenLocal.wf_ts3
      (by bm_strips4 CFSG.KC.BM.SevenLocal.ord_ts3 69)
  · rw [ets3]
    exact notId_sound SevenLocal.wf_ts3 SevenLocal.ne_ts3
  · exact rk _ _ _ (by norm_num) SevenLocal.wf_s4 SevenLocal.wf_PrkS4 SevenLocal.wf_RrkS4
      (by bm_stripsx CFSG.KC.BM.SevenLocal.rkS4_ 69) SevenLocal.shape_rkS4 SevenLocal.ech_rkS4
  · rw [show 4 = 2 * 2 by norm_num, pow_mul, ets4p2, sq]
    exact p1one SevenLocal.wf_ts4p2 SevenLocal.wf_ts4p2
      (by bm_strips4 CFSG.KC.BM.SevenLocal.ord_ts4 69)
  · rw [ets4p2]
    exact ne_one_of_rank hrts4 (by norm_num)
  · rw [ets4p2]
    exact hrts4
  · exact q11 SevenLocal.wf_f Seven.wf_t1 Seven.wf_t1 SevenLocal.wf_f
      (by bm_strips2_4 CFSG.KC.BM.SevenLocal.cm_ft1 69)
  · intro i _ e
    apply move_row_f
    rw [e, vecMul_pow_fix hfix i]
  · rw [p1 SevenLocal.alf Seven.wf_al SevenLocal.wf_f (by bm_strips4 CFSG.KC.BM.SevenLocal.c_alf 69)]
    exact rk _ _ _ (by norm_num) SevenLocal.wf_alf SevenLocal.wf_PrkAlF SevenLocal.wf_RrkAlF
      (by bm_stripsx CFSG.KC.BM.SevenLocal.rkAlF_ 69) SevenLocal.shape_rkAlF SevenLocal.ech_rkAlF
  · rw [et1xf SevenLocal.f SevenLocal.t1xf SevenLocal.wf_f (by bm_strips4 CFSG.KC.BM.SevenLocal.c_t1xf 69)]
    exact rk _ _ _ (by norm_num) SevenLocal.wf_t1xf SevenLocal.wf_PrkT1xF SevenLocal.wf_RrkT1xF
      (by bm_stripsx CFSG.KC.BM.SevenLocal.rkT1xF_ 69) SevenLocal.shape_rkT1xF
      SevenLocal.ech_rkT1xF
  · rw [← ef2, et1xf SevenLocal.f2 SevenLocal.t1xf2 SevenLocal.wf_f2 (by bm_strips4 CFSG.KC.BM.SevenLocal.c_t1xf2 69)]
    exact rk _ _ _ (by norm_num) SevenLocal.wf_t1xf2 SevenLocal.wf_PrkT1xF2
      SevenLocal.wf_RrkT1xF2 (by bm_stripsx CFSG.KC.BM.SevenLocal.rkT1xF2_ 69)
      SevenLocal.shape_rkT1xF2 SevenLocal.ech_rkT1xF2
  · rw [← ef3, ealxf SevenLocal.f3 SevenLocal.alxf3 SevenLocal.wf_f3 (by bm_strips4 CFSG.KC.BM.SevenLocal.c_alxf3 69)]
    exact rk _ _ _ (by norm_num) SevenLocal.wf_alxf3 SevenLocal.wf_PrkAlxF3
      SevenLocal.wf_RrkAlxF3 (by bm_stripsx CFSG.KC.BM.SevenLocal.rkAlxF3_ 69)
      SevenLocal.shape_rkAlxF3 SevenLocal.ech_rkAlxF3
  · rw [← ef4, et1xf SevenLocal.f4 SevenLocal.t1xf4 SevenLocal.wf_f4 (by bm_strips4 CFSG.KC.BM.SevenLocal.c_t1xf4 69)]
    exact rk _ _ _ (by norm_num) SevenLocal.wf_t1xf4 SevenLocal.wf_PrkT1xF4
      SevenLocal.wf_RrkT1xF4 (by bm_stripsx CFSG.KC.BM.SevenLocal.rkT1xF4_ 69)
      SevenLocal.shape_rkT1xF4 SevenLocal.ech_rkT1xF4
  · rw [← ef5, ealxf SevenLocal.f5 SevenLocal.alxf5 SevenLocal.wf_f5 (by bm_strips4 CFSG.KC.BM.SevenLocal.c_alxf5 69)]
    exact rk _ _ _ (by norm_num) SevenLocal.wf_alxf5 SevenLocal.wf_PrkAlxF5
      SevenLocal.wf_RrkAlxF5 (by bm_stripsx CFSG.KC.BM.SevenLocal.rkAlxF5_ 69)
      SevenLocal.shape_rkAlxF5 SevenLocal.ech_rkAlxF5
  · rw [← ef6, ealxf SevenLocal.f6 SevenLocal.alxf6 SevenLocal.wf_f6 (by bm_strips4 CFSG.KC.BM.SevenLocal.c_alxf6 69)]
    exact rk _ _ _ (by norm_num) SevenLocal.wf_alxf6 SevenLocal.wf_PrkAlxF6
      SevenLocal.wf_RrkAlxF6 (by bm_stripsx CFSG.KC.BM.SevenLocal.rkAlxF6_ 69)
      SevenLocal.shape_rkAlxF6 SevenLocal.ech_rkAlxF6
  · rw [eu12]
    exact (p1 SevenLocal.u12 SevenLocal.wf_u2 SevenLocal.wf_u1
      (by bm_strips4 CFSG.KC.BM.SevenLocal.cm_u2u1 69)).symm
  · intro i hi
    interval_cases i
    · rw [pow_zero]
      exact hu2ne
    · rw [pow_one]
      exact eqMat_sound SevenLocal.wf_u2 SevenLocal.wf_u1 SevenLocal.ne_u2_u1
    · rw [sq, p1 SevenLocal.u1p2 SevenLocal.wf_u1 SevenLocal.wf_u1
        (by bm_strips4 CFSG.KC.BM.SevenLocal.c_u1p2 69)]
      exact eqMat_sound SevenLocal.wf_u2 SevenLocal.wf_u1p2 SevenLocal.ne_u2_u1p2
  · rw [eu12]
    exact rk _ _ _ (by norm_num) SevenLocal.wf_u12 SevenLocal.wf_PrkU12 SevenLocal.wf_RrkU12
      (by bm_stripsx CFSG.KC.BM.SevenLocal.rkU12_ 69) SevenLocal.shape_rkU12 SevenLocal.ech_rkU12
  · rw [← mul_assoc, eu12, p1 SevenLocal.u122 SevenLocal.wf_u12 SevenLocal.wf_u2
      (by bm_strips4 CFSG.KC.BM.SevenLocal.c_u122 69)]
    exact rk _ _ _ (by norm_num) SevenLocal.wf_u122 SevenLocal.wf_PrkU122
      SevenLocal.wf_RrkU122 (by bm_stripsx CFSG.KC.BM.SevenLocal.rkU122_ 69)
      SevenLocal.shape_rkU122 SevenLocal.ech_rkU122

end CertificateChecks.KernelBM.SevenFacts

end
