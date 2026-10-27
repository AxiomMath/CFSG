module

public import CFSG.Certificates.Kernel.BabyMonster.FiveA.Check2
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.Check3
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.Check9
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.Check13
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.Check14
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.RkT
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.RkW48
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.RkW87
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.RkW88
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.RkW89
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.Wf
public import Certificates.Kernel.BabyMonster.ChainN
public import Certificates.Kernel.BabyMonster.FiveA.Basic
public import Certificates.Kernel.BabyMonster.FiveA.Facts13625
public import Certificates.Kernel.BabyMonster.FiveA.RankLin

public section

namespace CertificateChecks.KernelBM.FiveA

open CFSG.KC.BM CFSG.KC.BM.FiveA

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "MX" => stripMat CFSG.KC.BM.Five.f85
local notation "MH" => stripMat CFSG.KC.BM.Five.f86
local notation "MZ" => stripMat CFSG.KC.BM.Five.Z

set_option maxRecDepth 100000

@[expose] def TwoBWit (W E : MatB) : Prop :=
  W * W = 1 ∧ W ≠ 1 ∧ (W - 1).rank = 2048 ∧ W * E = E * W

theorem comm_of_conj {M : Type*} [Monoid M] {h z : M} (hz5 : z ^ 5 = 1)
    (hc : h * z ^ 2 = z * h) : h ^ 4 * z = z * h ^ 4 := by
  have hz6 : z ^ 6 = z := by rw [pow_succ', hz5, mul_one]
  have h1 : h * z = z ^ 3 * h := by
    calc h * z = h * z ^ 2 * z ^ 2 * z ^ 2 := by
          rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add, hz6]
      _ = z ^ 3 * h := by
          rw [hc, mul_assoc z h, hc, mul_assoc z (z * h), mul_assoc z h, hc]
          simp only [← mul_assoc, ← pow_succ']
          rw [show z * z * z = z ^ 3 by rw [pow_succ, pow_two]]
  have hk : ∀ k : ℕ, h * z ^ k = z ^ (3 * k) * h := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, h1, ← mul_assoc, ← pow_add]
      ring_nf
  have hn : ∀ n : ℕ, h ^ n * z = z ^ (3 ^ n) * h ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_assoc, ih, ← mul_assoc, hk, mul_assoc, ← pow_succ', pow_succ' 3 n]
  rw [hn 4, show (3 : ℕ) ^ 4 = 5 * 16 + 1 by norm_num, pow_add, pow_mul, hz5, one_pow, one_mul,
    pow_one]

open CFSG.KC.BM.Five in
theorem z_sq : stripMat Zp2 = MZ ^ 2 := by
  rw [← mul1 wf_Z wf_Z (by bm_strips CFSG.KC.BM.Five.cZp2 69), sq]

theorem h4_rank : (MH ^ 4 - 1).rank = 2048 := by
  rw [← h_sq2]
  exact rank_sub_one_of_cert (by norm_num) Five.wf_f86_sq2 wf_PrkT wf_RrkT
    (by bm_stripsx CFSG.KC.BM.FiveA.rkT_ 69) shape_rkT ech_rkT

theorem h4_wit {E : MatB} (hE : MH ^ 4 * E = E * MH ^ 4) : TwoBWit (MH ^ 4) E :=
  ⟨by rw [← pow_add, h_eight], ne_one_of_rank h4_rank (by norm_num), h4_rank, hE⟩

theorem wit_of {W E C : List Nat} (hW : wfMat W = true) (hE : wfMat E = true)
    (hsq : AllStrips [W] W idStrips) (hr : (stripMat W - 1).rank = 2048)
    (h1 : AllStrips [E] W C) (h2 : AllStrips [W] E C) : TwoBWit (stripMat W) (stripMat E) :=
  ⟨one1 hW hW hsq, ne_one_of_rank hr (by norm_num), hr, by
    rw [mul1 hW hE h1, mul1 hE hW h2]⟩

open CFSG.KC.BM.Five in
theorem fact13626 :
    TwoBWit (MH ^ 4) MZ ∧
      TwoBWit (MH ^ 4) (stripMat W_sq3 * stripMat Q3 * stripMat Q4 ^ 2) ∧
      TwoBWit (stripMat v40) (stripMat Q3 * stripMat Q4) := by
  have hz := eq1 wf_f86 wf_Zp2 wf_Z wf_f86 (by bm_strips2 CFSG.KC.BM.Five.zh 69)
  rw [z_sq] at hz
  have hq42 : stripMat Q4_sq1 = stripMat Q4 ^ 2 := by
    rw [← mul1 wf_Q4 wf_Q4 (by bm_strips CFSG.KC.BM.Five.cQ4_sq1 69), sq]
  have he42 : stripMat W_sq3 * stripMat Q3 * stripMat Q4 ^ 2 = stripMat e42 := by
    rw [← hq42]
    exact mul2 wf_W_sq3 wf_Q3 wf_Q4_sq1 (by bm_strips4 CFSG.KC.BM.FiveA.ce42 69)
  have hc43a := mul1 (C := c43) wf_f86_sq2 wf_e42 (by bm_strips4 CFSG.KC.BM.FiveA.cc43 69)
  have hc43b := mul1 (C := c43) wf_e42 wf_f86_sq2 (by bm_strips4 CFSG.KC.BM.FiveA.w40e 69)
  have he30 : stripMat Q3 * stripMat Q4 = stripMat v27 :=
    mul1 wf_Q3 wf_Q4 (by bm_strips4 CFSG.KC.BM.FiveA.cv27 69)
  refine ⟨h4_wit (comm_of_conj z_five hz), h4_wit ?_, ?_⟩
  · rw [he42, ← h_sq2, hc43a, hc43b]
  · rw [he30]
    exact wit_of (C := c41) wf_v40 wf_v27 (by bm_strips4 CFSG.KC.BM.FiveA.w48sq 69)
      (rank_sub_one_of_cert (by norm_num) wf_v40 wf_PrkW48 wf_RrkW48
        (by bm_stripsx CFSG.KC.BM.FiveA.rkW48_ 69) shape_rkW48 ech_rkW48)
      (by bm_strips4 CFSG.KC.BM.FiveA.cc41 69) (by bm_strips4 CFSG.KC.BM.FiveA.w48e 69)

open CFSG.KC.BM.Five in
theorem fact13627 :
    TwoBWit (stripMat v177) MX ∧ TwoBWit (stripMat v178) (MX * MZ) ∧
      TwoBWit (stripMat v179) (MX * MZ ^ 2) := by
  have e112 : MX * MZ = stripMat v112 := mul1 wf_f85 wf_Z (by bm_strips4 CFSG.KC.BM.FiveA.cv112 69)
  have e160 : MX * MZ ^ 2 = stripMat v160 := by
    rw [← z_sq]
    exact mul1 wf_f85 wf_Zp2 (by bm_strips4 CFSG.KC.BM.FiveA.cv160 69)
  refine ⟨?_, ?_, ?_⟩
  · exact wit_of (C := c180) wf_v177 wf_f85 (by bm_strips4 CFSG.KC.BM.FiveA.w87sq 69)
      (rank_sub_one_of_cert (by norm_num) wf_v177 wf_PrkW87 wf_RrkW87
        (by bm_stripsx CFSG.KC.BM.FiveA.rkW87_ 69) shape_rkW87 ech_rkW87)
      (by bm_strips4 CFSG.KC.BM.FiveA.cc180 69) (by bm_strips4 CFSG.KC.BM.FiveA.w87e 69)
  · rw [e112]
    exact wit_of (C := c181) wf_v178 wf_v112 (by bm_strips4 CFSG.KC.BM.FiveA.w88sq 69)
      (rank_sub_one_of_cert (by norm_num) wf_v178 wf_PrkW88 wf_RrkW88
        (by bm_stripsx CFSG.KC.BM.FiveA.rkW88_ 69) shape_rkW88 ech_rkW88)
      (by bm_strips4 CFSG.KC.BM.FiveA.cc181 69) (by bm_strips4 CFSG.KC.BM.FiveA.w88e 69)
  · rw [e160]
    exact wit_of (C := c182) wf_v179 wf_v160 (by bm_strips4 CFSG.KC.BM.FiveA.w89sq 69)
      (rank_sub_one_of_cert (by norm_num) wf_v179 wf_PrkW89 wf_RrkW89
        (by bm_stripsx CFSG.KC.BM.FiveA.rkW89_ 69) shape_rkW89 ech_rkW89)
      (by bm_strips4 CFSG.KC.BM.FiveA.cc182 69) (by bm_strips4 CFSG.KC.BM.FiveA.w89e 69)

end CertificateChecks.KernelBM.FiveA

end
