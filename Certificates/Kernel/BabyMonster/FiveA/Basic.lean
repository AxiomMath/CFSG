module

public import CFSG.Certificates.Kernel.BabyMonster.Chain4
public import CFSG.Certificates.Kernel.BabyMonster.Five.All
public import Certificates.Kernel.BabyMonster.Chain
public import Certificates.Kernel.BabyMonster.Chain2
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check10
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check11
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check12
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check13
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check14
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check15
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check16
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check17
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check18
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check19
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check20
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check21
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check22
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check23
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check24
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check25
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check26
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check27
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check28
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check29
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check30
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check31
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check32
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check33
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check34
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check35
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check36
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check37
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check38
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check39
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check4
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check40
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check41
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check42
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check43
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check44
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check45
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check46
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check47
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check48
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check49
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check5
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check50
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check51
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check52
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check53
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check54
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check55
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check56
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check57
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check58
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check59
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check6
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check60
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check61
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check62
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check63
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check64
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check65
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check66
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check67
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check68
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check69
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check7
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check70
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check71
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check72
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check73
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check74
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check75
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check8
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check9

public section

namespace CertificateChecks.KernelBM.FiveA

open CFSG.KC.BM

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "MX" => stripMat CFSG.KC.BM.Five.f85
local notation "MH" => stripMat CFSG.KC.BM.Five.f86

theorem mul1 {A B C : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (h : AllStrips [B] A C) : stripMat A * stripMat B = stripMat C := by
  have e := stripMat_mul_of_allStrips (Ws := [B]) (by simp [hB]) hA h
  simpa using e

theorem mul2 {A B C D : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (hC : wfMat C = true) (h : AllStrips [B, C] A D) :
    stripMat A * stripMat B * stripMat C = stripMat D := by
  have e := stripMat_mul_of_allStrips (Ws := [B, C]) (by simp [hB, hC]) hA h
  simpa using e

theorem one1 {A B : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (h : AllStrips [B] A idStrips) : stripMat A * stripMat B = 1 := by
  have e := stripMat_mul_eq_one (Ws := [B]) (by simp [hB]) hA h
  simpa using e

theorem eq1 {A B C D : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (hC : wfMat C = true) (hD : wfMat D = true) (h : AllStrips2 [B] [D] A C) :
    stripMat A * stripMat B = stripMat C * stripMat D := by
  have e := stripMat_mul_eq_of_allStrips2 (Ws := [B]) (Ds := [D]) (by simp [hB]) (by simp [hD])
    hA hC h
  simpa using e

theorem pow_three' (a : MatB) : a * a * a = a ^ 3 := by
  simp only [pow_succ, pow_zero, one_mul]

open CFSG.KC.BM.Five in
theorem x_sq1 : stripMat f85_sq1 = MX ^ 2 := by
  rw [← mul1 wf_f85 wf_f85 (by bm_strips CFSG.KC.BM.Five.cf85_sq1 69), sq]

open CFSG.KC.BM.Five in
theorem x_sq2 : stripMat f85_sq2 = MX ^ 4 := by
  rw [← mul1 wf_f85_sq1 wf_f85_sq1 (by bm_strips CFSG.KC.BM.Five.cf85_sq2 69), x_sq1, ← pow_add]

open CFSG.KC.BM.Five in
theorem x_five : MX ^ 5 = 1 := by
  have e := one1 wf_f85_sq2 wf_f85 (by bm_strips CFSG.KC.BM.Five.ox_pow 69)
  rwa [x_sq2, ← pow_succ] at e

open CFSG.KC.BM.Five in
theorem h_sq1 : stripMat f86_sq1 = MH ^ 2 := by
  rw [← mul1 wf_f86 wf_f86 (by bm_strips CFSG.KC.BM.Five.cf86_sq1 69), sq]

open CFSG.KC.BM.Five in
theorem h_sq2 : stripMat f86_sq2 = MH ^ 4 := by
  rw [← mul1 wf_f86_sq1 wf_f86_sq1 (by bm_strips CFSG.KC.BM.Five.cf86_sq2 69), h_sq1, ← pow_add]

open CFSG.KC.BM.Five in
theorem h_pp0 : stripMat oh_pp0 = MH ^ 3 := by
  rw [← mul1 wf_f86 wf_f86_sq1 (by bm_strips CFSG.KC.BM.Five.coh_pp0 69), h_sq1, ← pow_succ']

open CFSG.KC.BM.Five in
theorem h_p : stripMat oh_p = MH ^ 7 := by
  rw [← mul1 wf_oh_pp0 wf_f86_sq2 (by bm_strips CFSG.KC.BM.Five.coh_p 69), h_pp0, h_sq2,
    ← pow_add]

open CFSG.KC.BM.Five in
theorem h_eight : MH ^ 8 = 1 := by
  have e := one1 wf_oh_p wf_f86 (by bm_strips CFSG.KC.BM.Five.oh_pow 69)
  rwa [h_p, ← pow_succ] at e

open CFSG.KC.BM.Five in
theorem h_three : stripMat H3 = MH ^ 3 := by
  rw [← mul2 wf_f86 wf_f86 wf_f86 (by bm_strips CFSG.KC.BM.Five.cH3 69), pow_three']

@[expose] noncomputable def xU : MatBˣ :=
  ⟨MX, MX ^ 4, by rw [← pow_succ', x_five], by rw [← pow_succ, x_five]⟩

@[expose] noncomputable def hU : MatBˣ :=
  ⟨MH, MH ^ 7, by rw [← pow_succ', h_eight], by rw [← pow_succ, h_eight]⟩

theorem h_pow_mod (k : ℕ) : MH ^ (k + 8) = MH ^ k := by
  rw [pow_add, h_eight, mul_one]

theorem conj_pow' {G : Type*} [Group G] (a b : G) (n : ℕ) : (a⁻¹ * b * a) ^ n = a⁻¹ * b ^ n * a := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, pow_succ]; group

open CFSG.KC.BM.Five in
theorem q_one : stripMat W_sq3 = (MX * MH ^ 3) ^ 8 := by
  have e0 := mul1 (C := W) wf_f85 wf_H3 (by bm_strips CFSG.KC.BM.Five.cW 69)
  have e1 := mul1 (C := W_sq1) wf_W wf_W (by bm_strips CFSG.KC.BM.Five.cW_sq1 69)
  have e2 := mul1 (C := W_sq2) wf_W_sq1 wf_W_sq1 (by bm_strips CFSG.KC.BM.Five.cW_sq2 69)
  have e3 := mul1 (C := W_sq3) wf_W_sq2 wf_W_sq2 (by bm_strips CFSG.KC.BM.Five.cW_sq3 69)
  rw [← e3, ← e2, ← e1, ← e0, h_three]
  simp only [← sq, ← pow_mul]
  norm_num

open CFSG.KC.BM.Five in
theorem q_five : stripMat W_sq3 ^ 5 = 1 := by
  have e1 := mul1 (C := W_sq3_sq1) wf_W_sq3 wf_W_sq3
    (by bm_strips CFSG.KC.BM.Five.cW_sq3_sq1 69)
  have e2 := mul1 (C := W_sq3_sq2) wf_W_sq3_sq1 wf_W_sq3_sq1
    (by bm_strips CFSG.KC.BM.Five.cW_sq3_sq2 69)
  have e3 := one1 wf_W_sq3_sq2 wf_W_sq3 (by bm_strips CFSG.KC.BM.Five.oq_pow 69)
  rw [← e2, ← e1] at e3
  rw [← e3]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

open CFSG.KC.BM.Five in
theorem q_two : stripMat Q2 = MH ^ 7 * stripMat W_sq3 * MH := by
  have e := eq1 wf_f86 wf_Q2 wf_W_sq3 wf_f86 (by bm_strips2 CFSG.KC.BM.Five.cQ2 69)
  calc stripMat Q2 = MH ^ 7 * MH * stripMat Q2 := by rw [← pow_succ, h_eight, one_mul]
    _ = MH ^ 7 * stripMat W_sq3 * MH := by rw [mul_assoc, e, mul_assoc]

open CFSG.KC.BM.Five in
theorem q_three : stripMat Q3 = MX ^ 4 * stripMat W_sq3 * MX := by
  have e := eq1 wf_f85 wf_Q3 wf_W_sq3 wf_f85 (by bm_strips2 CFSG.KC.BM.Five.cQ3 69)
  calc stripMat Q3 = MX ^ 4 * MX * stripMat Q3 := by rw [← pow_succ, x_five, one_mul]
    _ = MX ^ 4 * stripMat W_sq3 * MX := by rw [mul_assoc, e, mul_assoc]

end CertificateChecks.KernelBM.FiveA

end
