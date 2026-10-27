module

public import CFSG.Certificates.Kernel.BabyMonster.SevenFacts
public import CFSG.Certificates.Kernel.BabyMonster.SevenElem.All
public import CFSG.Certificates.Kernel.BabyMonster.SevenRk.All
public import CFSG.Certificates.Kernel.BabyMonster.Chain4
public import CFSG.Certificates.Kernel.BabyMonster.Chain4Pair
public import Certificates.Kernel.BabyMonster.SevenGen
public import Certificates.Kernel.BabyMonster.ChainN
public import Certificates.Kernel.BabyMonster.FiveA.RankLin

public section

namespace CertificateChecks.KernelBM.SevenFacts

open CFSG.KC.BM CFSG.KC.BM.SevenFacts CertificateChecks.KernelBM.SevenGen
  CertificateChecks.KernelBM.FiveA

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

set_option maxRecDepth 100000

theorem foldl_comm {n : ℕ} (Z : Matrix (Fin n) (Fin n) (ZMod 2)) :
    ∀ (L : List (Matrix (Fin n) (Fin n) (ZMod 2))) (a : Matrix (Fin n) (Fin n) (ZMod 2)),
      Commute a Z → (∀ b ∈ L, Commute b Z) → Commute (L.foldl (· * ·) a) Z
  | [], _, ha, _ => ha
  | b :: L, a, ha, hL => foldl_comm Z L (a * b) (ha.mul_left (hL b List.mem_cons_self))
      fun c hc => hL c (List.mem_cons_of_mem _ hc)

theorem cpow {n : ℕ} {a b : Matrix (Fin n) (Fin n) (ZMod 2)} (h : Commute a b) (k : ℕ) :
    Commute (a ^ k) b := h.pow_left k

theorem cself {n : ℕ} (a : Matrix (Fin n) (Fin n) (ZMod 2)) (k : ℕ) : Commute a (a ^ k) :=
  Commute.self_pow a k

theorem cpowpow {n : ℕ} (a : Matrix (Fin n) (Fin n) (ZMod 2)) (k l : ℕ) :
    Commute (a ^ k) (a ^ l) := Commute.pow_pow_self a k l

theorem cmulpow {n : ℕ} {a b : Matrix (Fin n) (Fin n) (ZMod 2)} (h : Commute a b) (k : ℕ) :
    (a * b) ^ k = a ^ k * b ^ k := h.mul_pow k

theorem comm_inv {n : ℕ} {A B Z : Matrix (Fin n) (Fin n) (ZMod 2)} (h1 : A * B = 1)
    (h : Commute A Z) : Commute B Z := by
  have h2 : B * A = 1 := mul_eq_one_comm.mp h1
  change B * Z = Z * B
  calc B * Z = B * Z * (A * B) := by rw [h1, mul_one]
    _ = B * (Z * A) * B := by simp only [mul_assoc]
    _ = B * (A * Z) * B := by rw [← h.eq]
    _ = B * A * Z * B := by simp only [mul_assoc]
    _ = Z * B := by rw [h2, one_mul]

theorem comm_of {Ws : List (List Nat)} {A : List Nat} (C : List Nat) {Z : MatB}
    (hW : ∀ W ∈ Ws, wfMat W = true) (hA : wfMat A = true) (h : AllStrips Ws A C)
    (hcA : Commute (stripMat A) Z) (hcW : ∀ W ∈ Ws, Commute (stripMat W) Z) :
    Commute (stripMat C) Z := by
  rw [← stripMat_mul_of_allStrips hW hA h]
  exact foldl_comm Z _ _ hcA (by simpa using hcW)

theorem c1 {A B : List Nat} (C : List Nat) {Z : MatB} (hA : wfMat A = true)
    (hB : wfMat B = true) (h : AllStrips [B] A C) (ha : Commute (stripMat A) Z)
    (hb : Commute (stripMat B) Z) : Commute (stripMat C) Z := by
  rw [← p1 C hA hB h]
  exact ha.mul_left hb

theorem rank_conj7 {g c ci : MatB} (h : c * ci = 1) : (c * g * ci - 1).rank = (g - 1).rank := by
  have e : c * g * ci - 1 = c * (g - 1) * ci := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h]
  rw [e, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_det_of_left_inverse h),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnit_det_of_right_inverse h)]

theorem pow7_of_sq {a : MatB} (h : a * a = 1) : a ^ 7 = a := by
  have h2 : a ^ 2 = 1 := by rw [sq, h]
  rw [show 7 = 2 * 3 + 1 by norm_num, pow_succ, pow_mul, h2, one_pow, one_mul]

theorem pow7_of_cube {a : MatB} (h : a ^ 3 = 1) : a ^ 7 = a := by
  rw [show 7 = 3 * 2 + 1 by norm_num, pow_succ, pow_mul, h, one_pow, one_mul]

theorem pow3 (a : MatB) : a * a * a = a ^ 3 := by
  simp only [pow_succ, pow_zero, one_mul]

theorem y2_eq : stripMat Seven.y2 = stripMat Seven.y ^ 2 := by
  rw [← p1 Seven.y2 Seven.wf_y Seven.wf_y (by bm_strips CFSG.KC.BM.Seven.c_y2 69), sq]

theorem y3_eq : stripMat Seven.y3 = stripMat Seven.y ^ 3 := by
  rw [← p1 Seven.y3 Seven.wf_y Seven.wf_y2 (by bm_strips CFSG.KC.BM.Seven.c_y3 69), y2_eq,
    ← pow_succ']

theorem y4_eq : stripMat Seven.y4 = stripMat Seven.y ^ 4 := by
  rw [← p1 Seven.y4 Seven.wf_y2 Seven.wf_y2 (by bm_strips CFSG.KC.BM.Seven.c_y4 69), y2_eq,
    ← pow_add]

theorem r43_eq : stripMat Seven.r43 = stripMat Seven.t1 * stripMat Seven.y :=
  (p1 Seven.r43 Seven.wf_t1 Seven.wf_y (by bm_strips CFSG.KC.BM.Seven.c_r43 69)).symm

theorem r40_eq : stripMat Seven.r40 = stripMat Seven.t1 * stripMat Seven.y ^ 4 := by
  rw [← y4_eq]
  exact (p1 Seven.r40 Seven.wf_t1 Seven.wf_y4 (by bm_strips CFSG.KC.BM.Seven.c_r40 69)).symm

theorem t2_eq : stripMat Seven.t2 =
    stripMat Seven.y ^ 3 * stripMat Seven.t1 * stripMat Seven.y ^ 2 := by
  rw [← y3_eq, ← y2_eq]
  exact (p2 Seven.t2 Seven.wf_y3 Seven.wf_t1 Seven.wf_y2
    (by bm_strips CFSG.KC.BM.Seven.c_t2 69)).symm

theorem al_eq : stripMat Seven.al = stripMat Seven.m2 ^ 19 := by
  have e26 : stripMat Seven.r26 = stripMat Seven.m2 ^ 2 := by
    rw [← p1 Seven.r26 Seven.wf_m2 Seven.wf_m2 (by bm_strips CFSG.KC.BM.Seven.c_r26 69), sq]
  have e27 : stripMat Seven.r27 = stripMat Seven.m2 ^ 4 := by
    rw [← p1 Seven.r27 Seven.wf_r26 Seven.wf_r26 (by bm_strips CFSG.KC.BM.Seven.c_r27 69), e26,
      ← pow_add]
  have e28 : stripMat Seven.r28 = stripMat Seven.m2 ^ 8 := by
    rw [← p1 Seven.r28 Seven.wf_r27 Seven.wf_r27 (by bm_strips CFSG.KC.BM.Seven.c_r28 69), e27,
      ← pow_add]
  have e29 : stripMat Seven.r29 = stripMat Seven.m2 ^ 16 := by
    rw [← p1 Seven.r29 Seven.wf_r28 Seven.wf_r28 (by bm_strips CFSG.KC.BM.Seven.c_r29 69), e28,
      ← pow_add]
  have e30 : stripMat Seven.r30 = stripMat Seven.m2 ^ 18 := by
    rw [← p1 Seven.r30 Seven.wf_r26 Seven.wf_r29 (by bm_strips CFSG.KC.BM.Seven.c_r30 69), e26,
      e29, ← pow_add]
  rw [← p1 Seven.al Seven.wf_m2 Seven.wf_r30 (by bm_strips CFSG.KC.BM.Seven.c_al 69), e30,
    ← pow_succ']

theorem sevenWords : SevenWords :=
  ⟨al_eq, g_pows.2.2.1, g_pows.2.2.2, t2_eq⟩

theorem g_t1_comm {Z : MatB} (hm1 : Commute (stripMat Seven.m1) Z)
    (hm2 : Commute (stripMat Seven.m2) Z) :
    Commute (stripMat Seven.g) Z ∧ Commute (stripMat Seven.t1) Z := by
  have hm2i : Commute (stripMat Seven.m2i) Z :=
    comm_inv (p1one Seven.wf_m2 Seven.wf_m2i (by bm_strips CFSG.KC.BM.Seven.c_m2i 69)) hm2
  have h41 := c1 Seven.r41 Seven.wf_m1 Seven.wf_m2i (by bm_strips CFSG.KC.BM.Seven.c_r41 69)
    hm1 hm2i
  have h45 := c1 Seven.r45 Seven.wf_r41 Seven.wf_m2i (by bm_strips CFSG.KC.BM.Seven.c_r45 69)
    h41 hm2i
  have h42 := c1 Seven.r42 Seven.wf_m1 Seven.wf_m2 (by bm_strips CFSG.KC.BM.Seven.c_r42 69)
    hm1 hm2
  have h26 := c1 Seven.r26 Seven.wf_m2 Seven.wf_m2 (by bm_strips CFSG.KC.BM.Seven.c_r26 69)
    hm2 hm2
  have h46 := c1 Seven.r46 Seven.wf_r42 Seven.wf_r26 (by bm_strips CFSG.KC.BM.Seven.c_r46 69)
    h42 h26
  have hg := comm_of (Ws := [Seven.m2, Seven.r45]) Seven.g (by simp [Seven.wf_m2, Seven.wf_r45])
    Seven.wf_r46 (by bm_strips CFSG.KC.BM.Seven.c_g 69) h46 (by simp [hm2, h45])
  have hw := comm_of (Ws := [Seven.r45, Seven.r45, Seven.m2i, Seven.m2i, Seven.r42, Seven.r42])
    Seven.w (by simp [Seven.wf_r45, Seven.wf_m2i, Seven.wf_r42]) Seven.wf_r46
    (by bm_strips CFSG.KC.BM.Seven.c_w 69) h46 (by simp [h45, hm2i, h42])
  have h35 := c1 Seven.r35 Seven.wf_w Seven.wf_w (by bm_strips CFSG.KC.BM.Seven.c_r35 69) hw hw
  have h36 := c1 Seven.r36 Seven.wf_r35 Seven.wf_r35 (by bm_strips CFSG.KC.BM.Seven.c_r36 69)
    h35 h35
  have h37 := c1 Seven.r37 Seven.wf_r36 Seven.wf_r36 (by bm_strips CFSG.KC.BM.Seven.c_r37 69)
    h36 h36
  have h38 := c1 Seven.r38 Seven.wf_r37 Seven.wf_r37 (by bm_strips CFSG.KC.BM.Seven.c_r38 69)
    h37 h37
  have h39 := c1 Seven.r39 Seven.wf_r36 Seven.wf_r38 (by bm_strips CFSG.KC.BM.Seven.c_r39 69)
    h36 h38
  have hz := c1 Seven.z Seven.wf_w Seven.wf_r39 (by bm_strips CFSG.KC.BM.Seven.c_z 69) hw h39
  have hh := comm_of (Ws := [Seven.r41, Seven.r46, Seven.r41, Seven.r42, Seven.r45, Seven.r41,
      Seven.r41, Seven.m1]) Seven.h
    (by simp [Seven.wf_r41, Seven.wf_r46, Seven.wf_r42, Seven.wf_r45, Seven.wf_m1]) Seven.wf_r26
    (by bm_strips CFSG.KC.BM.Seven.c_h 69) h26 (by simp [h41, h46, h42, h45, hm1])
  have hhi : Commute (stripMat Seven.hi) Z :=
    comm_inv (p1one Seven.wf_h Seven.wf_hi (by bm_strips CFSG.KC.BM.Seven.c_hi 69)) hh
  refine ⟨hg, ?_⟩
  exact comm_of (Ws := [Seven.z, Seven.h]) Seven.t1 (by simp [Seven.wf_z, Seven.wf_h])
    Seven.wf_hi (by bm_strips CFSG.KC.BM.Seven.c_t1 69) hhi (by simp [hz, hh])

theorem ty_comm {Z : MatB} (ht : Commute (stripMat Seven.t1) Z)
    (hy : Commute (stripMat Seven.y) Z) :
    Commute (stripMat Seven.y2) Z ∧ Commute (stripMat Seven.y4) Z ∧
      Commute (stripMat Seven.e3) Z ∧ Commute (stripMat Seven.t2) Z := by
  have hy2 := c1 Seven.y2 Seven.wf_y Seven.wf_y (by bm_strips CFSG.KC.BM.Seven.c_y2 69) hy hy
  have hy3 := c1 Seven.y3 Seven.wf_y Seven.wf_y2 (by bm_strips CFSG.KC.BM.Seven.c_y3 69) hy hy2
  have hy4 := c1 Seven.y4 Seven.wf_y2 Seven.wf_y2 (by bm_strips CFSG.KC.BM.Seven.c_y4 69)
    hy2 hy2
  have h43 := c1 Seven.r43 Seven.wf_t1 Seven.wf_y (by bm_strips CFSG.KC.BM.Seven.c_r43 69) ht hy
  have h40 := c1 Seven.r40 Seven.wf_t1 Seven.wf_y4 (by bm_strips CFSG.KC.BM.Seven.c_r40 69)
    ht hy4
  have h44 := c1 Seven.r44 Seven.wf_r40 Seven.wf_r40 (by bm_strips CFSG.KC.BM.Seven.c_r44 69)
    h40 h40
  have h47 := c1 Seven.r47 Seven.wf_r43 Seven.wf_r44 (by bm_strips CFSG.KC.BM.Seven.c_r47 69)
    h43 h44
  have he := comm_of (Ws := [Seven.r47, Seven.r43, Seven.y, Seven.r47, Seven.r44, Seven.r44,
      Seven.r40, Seven.r43, Seven.r40, Seven.y4, Seven.r43]) Seven.e3
    (by simp [Seven.wf_r47, Seven.wf_r43, Seven.wf_y, Seven.wf_r44, Seven.wf_r40, Seven.wf_y4])
    Seven.wf_r43 (by bm_strips CFSG.KC.BM.Seven.c_e3 69) h43
    (by simp [h47, h43, hy, h44, h40, hy4])
  have ht2 := comm_of (Ws := [Seven.t1, Seven.y2]) Seven.t2 (by simp [Seven.wf_t1, Seven.wf_y2])
    Seven.wf_y3 (by bm_strips CFSG.KC.BM.Seven.c_t2 69) hy3 (by simp [ht, hy2])
  exact ⟨hy2, hy4, he, ht2⟩

theorem x_comm : Commute (stripMat Seven.y) (stripMat Seven.x) ∧
    Commute (stripMat Seven.t1) (stripMat Seven.x) := by
  obtain ⟨-, -, ex, ey⟩ := g_pows
  refine ⟨by rw [ex, ey]; exact cpowpow _ 14 10, ?_⟩
  change stripMat Seven.t1 * stripMat Seven.x = stripMat Seven.x * stripMat Seven.t1
  rw [p1 SevenElem.t1x Seven.wf_t1 Seven.wf_x (by bm_strips4 CFSG.KC.BM.SevenElem.c_t1x 69),
    p1 SevenElem.t1x Seven.wf_x Seven.wf_t1 (by bm_strips4 CFSG.KC.BM.SevenElem.cm_xt1 69)]

theorem al_comm : Commute (stripMat Seven.g) (stripMat Seven.al) ∧
    Commute (stripMat Seven.y) (stripMat Seven.al) ∧
    Commute (stripMat Seven.t1) (stripMat Seven.al) := by
  have hm1 : Commute (stripMat Seven.m1) (stripMat Seven.al) :=
    (q11 Seven.wf_al Seven.wf_m1 Seven.wf_m1 Seven.wf_al
      (by bm_strips2_4 CFSG.KC.BM.SevenElem.cm_alm1 69)).symm
  have hm2 : Commute (stripMat Seven.m2) (stripMat Seven.al) := by
    rw [al_eq]
    exact cself _ 19
  obtain ⟨hg, ht⟩ := g_t1_comm hm1 hm2
  refine ⟨hg, ?_, ht⟩
  rw [g_pows.2.2.2]
  exact cpow hg 14

theorem e_cube : stripMat Seven.e3 ^ 3 = 1 := by
  rw [← pow3, p1 SevenElem.e2 Seven.wf_e3 Seven.wf_e3
    (by bm_strips4 CFSG.KC.BM.SevenElem.c_e2 69)]
  exact p1one SevenElem.wf_e2 Seven.wf_e3 (by bm_strips4 CFSG.KC.BM.SevenElem.ord_e 69)

theorem t1_sq : stripMat Seven.t1 * stripMat Seven.t1 = 1 :=
  p1one Seven.wf_t1 Seven.wf_t1 (by bm_strips4 CFSG.KC.BM.SevenElem.inv_t1 69)

theorem et1_comm : Commute (stripMat Seven.t1) (stripMat Seven.e3) := by
  change stripMat Seven.t1 * stripMat Seven.e3 = stripMat Seven.e3 * stripMat Seven.t1
  rw [p1 SevenElem.tw Seven.wf_t1 Seven.wf_e3 (by bm_strips4 CFSG.KC.BM.SevenElem.c_tw 69),
    p1 SevenElem.tw Seven.wf_e3 Seven.wf_t1 (by bm_strips4 CFSG.KC.BM.SevenElem.cm_et1 69)]

theorem rank_al : (stripMat Seven.al - 1).rank = 1860 :=
  rank_sub_one_of_cert (by norm_num) Seven.wf_al SevenElem.wf_PrkAl SevenElem.wf_RrkAl
    (by bm_stripsx CFSG.KC.BM.SevenElem.rkAl_ 69) SevenElem.shape_rkAl SevenElem.ech_rkAl

theorem rank_t1 : (stripMat Seven.t1 - 1).rank = 1860 :=
  rank_sub_one_of_cert (by norm_num) Seven.wf_t1 SevenElem.wf_PrkT1 SevenElem.wf_RrkT1
    (by bm_stripsx CFSG.KC.BM.SevenElem.rkT1_ 69) SevenElem.shape_rkT1 SevenElem.ech_rkT1

theorem t12_eq : stripMat Seven.t1 * stripMat Seven.t2 = stripMat SevenElem.t12 :=
  p1 SevenElem.t12 Seven.wf_t1 Seven.wf_t2 (by bm_strips4 CFSG.KC.BM.SevenElem.c_t12 69)

theorem y_conj : stripMat Seven.y ^ 3 * stripMat Seven.y ^ 2 = 1 := by
  rw [← pow_add, y_pow_five]

theorem fact17101 : CFSG.KC.BM.SevenFacts.Fact17101 := by
  obtain ⟨-, -, ex, ey⟩ := g_pows
  obtain ⟨hg_al, hy_al, ht_al⟩ := al_comm
  obtain ⟨hy_x, ht_x⟩ := x_comm
  obtain ⟨-, -, he_x, ht2_x⟩ := ty_comm ht_x hy_x
  obtain ⟨-, -, he_al, -⟩ := ty_comm ht_al hy_al
  have hx_al : Commute (stripMat Seven.x) (stripMat Seven.al) := by
    rw [ex]
    exact cpow hg_al 10
  have h70 : stripMat Seven.g ^ 70 = 1 := by
    rw [show 70 = 14 * 5 by norm_num, pow_mul, ← ey, y_pow_five]
  have hx7 : stripMat Seven.x ^ 7 = 1 := by rw [ex, ← pow_mul, h70]
  have hne : stripMat Seven.e3 ≠ 1 := notId_sound Seven.wf_e3 SevenElem.ne_e
  have hrt2 : (stripMat Seven.t2 - 1).rank = 1860 := by rw [t2_eq, rank_conj7 y_conj, rank_t1]
  have ht2sq : stripMat Seven.t2 * stripMat Seven.t2 = 1 := by
    rw [t2_eq]
    have h5 : stripMat Seven.y ^ 2 * stripMat Seven.y ^ 3 = 1 := by rw [← pow_add, y_pow_five]
    calc stripMat Seven.y ^ 3 * stripMat Seven.t1 * stripMat Seven.y ^ 2 *
          (stripMat Seven.y ^ 3 * stripMat Seven.t1 * stripMat Seven.y ^ 2)
        = stripMat Seven.y ^ 3 * (stripMat Seven.t1 * (stripMat Seven.y ^ 2 *
          stripMat Seven.y ^ 3) * stripMat Seven.t1) * stripMat Seven.y ^ 2 := by
          simp only [mul_assoc]
      _ = 1 := by rw [h5, mul_one, t1_sq, mul_one, y_conj]
  have ht12 : stripMat Seven.t2 * stripMat Seven.t1 = stripMat SevenElem.t12 :=
    p1 SevenElem.t12 Seven.wf_t2 Seven.wf_t1 (by bm_strips4 CFSG.KC.BM.SevenElem.cm_t2t1 69)
  have hrt12 : (stripMat Seven.t1 * stripMat Seven.t2 - 1).rank = 2048 := by
    rw [t12_eq]
    exact rank_sub_one_of_cert (by norm_num) SevenElem.wf_t12 SevenElem.wf_PrkT12
      SevenElem.wf_RrkT12 (by bm_stripsx CFSG.KC.BM.SevenElem.rkT12_ 69) SevenElem.shape_rkT12
      SevenElem.ech_rkT12
  have ht1sq2 : stripMat Seven.t1 ^ 2 = 1 := by rw [sq, t1_sq]
  have hte3 : (stripMat Seven.t1 * stripMat Seven.e3) ^ 3 = stripMat Seven.t1 := by
    rw [cmulpow et1_comm, e_cube, mul_one, pow_succ, ht1sq2, one_mul]
  have hcc : stripMat Seven.t1 * stripMat Seven.y * stripMat Seven.t1 * stripMat Seven.y ^ 4 =
      stripMat SevenElem.cc := by
    rw [← p1 SevenElem.cc Seven.wf_r43 Seven.wf_r40 (by bm_strips4 CFSG.KC.BM.SevenElem.c_cc 69),
      r43_eq, r40_eq]
    simp only [mul_assoc]
  refine ⟨sevenWords, p1one Seven.wf_al Seven.wf_al (by bm_strips4 CFSG.KC.BM.SevenElem.inv_al 69),
    ne_one_of_rank rank_al (by norm_num), rank_al, hx_al.symm.eq, hy_al.symm.eq, hx7,
    notId_sound Seven.wf_x CFSG.KC.BM.SevenGen.ne_x1, y_pow_five,
    notId_sound Seven.wf_y SevenElem.ne_y, hy_x.symm.eq, t1_sq, rank_t1, ht_x.eq, ht_al.eq,
    eqMat_sound Seven.wf_t1 Seven.wf_al SevenElem.ne_t1_al, ht2sq, hrt2, ht2_x.eq,
    by rw [t12_eq, ht12], eqMat_sound Seven.wf_t1 Seven.wf_t2 SevenElem.ne_t1_t2, hrt12, e_cube,
    hne, he_x.eq, et1_comm.symm.eq, he_al.eq, ?_, ?_, hte3, ?_, ?_⟩
  · rw [show 6 = 3 * 2 by norm_num, pow_mul, hte3, ht1sq2]
  · rw [cmulpow et1_comm, ht1sq2, one_mul]
    intro h2
    apply hne
    rw [← e_cube, pow_succ, h2, one_mul]
  · rw [hcc]
    exact notId_sound SevenElem.wf_cc SevenElem.ne_cc
  · rw [hcc]
    exact eqMat_sound SevenElem.wf_cc Seven.wf_al SevenElem.ne_cc_al

theorem fact17599 : CFSG.KC.BM.SevenFacts.Fact17599 :=
  ⟨g_pows.2.2.2, rank_sub_one_of_cert (by norm_num) Seven.wf_y SevenRk.wf_PrkY SevenRk.wf_RrkY
    (by bm_stripsx CFSG.KC.BM.SevenRk.rkY_ 69) SevenRk.shape_rkY SevenRk.ech_rkY⟩

end CertificateChecks.KernelBM.SevenFacts

end
