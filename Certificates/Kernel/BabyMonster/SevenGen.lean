module

public import CFSG.Certificates.Kernel.BabyMonster.SevenGenFact
public import CFSG.Certificates.Kernel.BabyMonster.PairSound
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.All
public import CFSG.Certificates.Kernel.BabyMonster.Seven.All
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.All
public import Certificates.Kernel.BabyMonster.Chain2
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check4
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check10
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check4
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check5
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check6
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check7
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check8
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check9

public section

namespace CertificateChecks.KernelBM.SevenGen

open CFSG.KC.BM CFSG.KC.BM.SevenGen
open scoped Matrix

theorem p1 {A B : List Nat} (C : List Nat) (hA : wfMat A = true) (hB : wfMat B = true)
    (h : AllStrips [B] A C) : stripMat A * stripMat B = stripMat C := by
  simpa using stripMat_mul_of_allStrips (Ws := [B]) (by simpa using hB) hA h

theorem p2 {A B D : List Nat} (C : List Nat) (hA : wfMat A = true) (hB : wfMat B = true)
    (hD : wfMat D = true) (h : AllStrips [B, D] A C) :
    stripMat A * stripMat B * stripMat D = stripMat C := by
  simpa using stripMat_mul_of_allStrips (Ws := [B, D]) (by simp [hB, hD]) hA h

theorem p3 {A B D E : List Nat} (C : List Nat) (hA : wfMat A = true) (hB : wfMat B = true)
    (hD : wfMat D = true) (hE : wfMat E = true) (h : AllStrips [B, D, E] A C) :
    stripMat A * stripMat B * stripMat D * stripMat E = stripMat C := by
  simpa using stripMat_mul_of_allStrips (Ws := [B, D, E]) (by simp [hB, hD, hE]) hA h

theorem p1one {A B : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (h : AllStrips [B] A idStrips) : stripMat A * stripMat B = 1 := by
  simpa using stripMat_mul_eq_one (Ws := [B]) (by simpa using hB) hA h

theorem q11 {A B C D : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (hC : wfMat C = true) (hD : wfMat D = true) (h : AllStrips2 [B] [D] A C) :
    stripMat A * stripMat B = stripMat C * stripMat D := by
  simpa using stripMat_mul_eq_of_allStrips2 (Ws := [B]) (Ds := [D]) (by simpa using hB)
    (by simpa using hD) hA hC h

theorem g_pows : stripMat Seven.r32 = stripMat Seven.g ^ 2 ∧
    stripMat Seven.r33 = stripMat Seven.g ^ 4 ∧ stripMat Seven.x = stripMat Seven.g ^ 10 ∧
    stripMat Seven.y = stripMat Seven.g ^ 14 := by
  have e32 : stripMat Seven.r32 = stripMat Seven.g ^ 2 := by
    rw [← p1 Seven.r32 Seven.wf_g Seven.wf_g (by bm_strips CFSG.KC.BM.Seven.c_r32 69), sq]
  have e33 : stripMat Seven.r33 = stripMat Seven.g ^ 4 := by
    rw [← p1 Seven.r33 Seven.wf_r32 Seven.wf_r32 (by bm_strips CFSG.KC.BM.Seven.c_r33 69), e32,
      ← pow_add]
  have e34 : stripMat Seven.r34 = stripMat Seven.g ^ 8 := by
    rw [← p1 Seven.r34 Seven.wf_r33 Seven.wf_r33 (by bm_strips CFSG.KC.BM.Seven.c_r34 69), e33,
      ← pow_add]
  have ex : stripMat Seven.x = stripMat Seven.g ^ 10 := by
    rw [← p1 Seven.x Seven.wf_r32 Seven.wf_r34 (by bm_strips CFSG.KC.BM.Seven.c_x 69), e32, e34,
      ← pow_add]
  refine ⟨e32, e33, ex, ?_⟩
  rw [← p1 Seven.y Seven.wf_r33 Seven.wf_x (by bm_strips CFSG.KC.BM.Seven.c_y 69), e33, ex,
    ← pow_add]

theorem y_pow_five : stripMat Seven.y ^ 5 = 1 := by
  have e2 := p1 Seven.y2 Seven.wf_y Seven.wf_y (by bm_strips CFSG.KC.BM.Seven.c_y2 69)
  have e4 := p1 Seven.y4 Seven.wf_y2 Seven.wf_y2 (by bm_strips CFSG.KC.BM.Seven.c_y4 69)
  have h := p1one Seven.wf_y4 Seven.wf_y (by bm_strips CFSG.KC.BM.SevenGen.ord_y5 69)
  rw [← e4, ← e2] at h
  have e5 : stripMat Seven.y ^ 5 = stripMat Seven.y * stripMat Seven.y *
      (stripMat Seven.y * stripMat Seven.y) * stripMat Seven.y := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e5, h]

theorem fix_row : vrow (rowOf vf 0) ᵥ* stripMat Seven.x = vrow (rowOf vf 0) := by
  have h0 := mulS_rows Seven.wf_x vf (t := 0) (by norm_num)
  rw [Nat.eq_of_beq_eq_true CFSG.KC.BM.SevenGen.fix_x] at h0
  exact h0.symm

theorem move_row : vrow (rowOf vf 0) ᵥ* stripMat f ≠ vrow (rowOf vf 0) := by
  intro e
  have h1 := mulS_rows wf_f vf (t := 0) (by norm_num)
  rw [e] at h1
  have hm := CFSG.KC.BM.SevenGen.move_f
  rw [rowOf_inj h1, Nat.beq_refl] at hm
  exact absurd hm (by decide)

theorem ap_eq : stripMat ap = (stripMat Seven.g ^ 2 * stripMat s2i * stripMat Seven.g *
    stripMat s2i * stripMat Seven.g) ^ 17 := by
  have hw : stripMat apw = stripMat Seven.g ^ 2 * stripMat s2i * stripMat Seven.g *
      stripMat s2i * stripMat Seven.g := by
    rw [← p2 apw Seven.wf_r32 wf_r100 wf_r100 (by bm_strips CFSG.KC.BM.SevenGen.c_apw 69),
      ← p1 r100 wf_s2i Seven.wf_g (by bm_strips CFSG.KC.BM.SevenGen.c_r100 69), g_pows.1]
    simp only [mul_assoc]
  have e2 : stripMat r85 = stripMat apw ^ 2 := by
    rw [← p1 r85 wf_apw wf_apw (by bm_strips CFSG.KC.BM.SevenGen.c_r85 69), sq]
  have e4 : stripMat r86 = stripMat apw ^ 4 := by
    rw [← p1 r86 wf_r85 wf_r85 (by bm_strips CFSG.KC.BM.SevenGen.c_r86 69), e2, ← pow_add]
  have e8 : stripMat r87 = stripMat apw ^ 8 := by
    rw [← p1 r87 wf_r86 wf_r86 (by bm_strips CFSG.KC.BM.SevenGen.c_r87 69), e4, ← pow_add]
  have e16 : stripMat r88 = stripMat apw ^ 16 := by
    rw [← p1 r88 wf_r87 wf_r87 (by bm_strips CFSG.KC.BM.SevenGen.c_r88 69), e8, ← pow_add]
  rw [← p1 ap wf_apw wf_r88 (by bm_strips CFSG.KC.BM.SevenGen.c_ap 69), e16, ← pow_succ', hw]

theorem bp_eq : stripMat bp =
    (stripMat Seven.g * stripMat s2 * stripMat gi * stripMat s2 ^ 2) ^ 13 := by
  have hw : stripMat bpw = stripMat Seven.g * stripMat s2 * stripMat gi * stripMat s2 ^ 2 := by
    rw [← p3 bpw Seven.wf_g wf_s2 wf_gi wf_s2sq (by bm_strips CFSG.KC.BM.SevenGen.c_bpw 69),
      ← p1 s2sq wf_s2 wf_s2 (by bm_strips CFSG.KC.BM.SevenGen.c_s2sq 69), sq]
  have e2 : stripMat r89 = stripMat bpw ^ 2 := by
    rw [← p1 r89 wf_bpw wf_bpw (by bm_strips CFSG.KC.BM.SevenGen.c_r89 69), sq]
  have e4 : stripMat r90 = stripMat bpw ^ 4 := by
    rw [← p1 r90 wf_r89 wf_r89 (by bm_strips CFSG.KC.BM.SevenGen.c_r90 69), e2, ← pow_add]
  have e8 : stripMat r91 = stripMat bpw ^ 8 := by
    rw [← p1 r91 wf_r90 wf_r90 (by bm_strips CFSG.KC.BM.SevenGen.c_r91 69), e4, ← pow_add]
  have e12 : stripMat r92 = stripMat bpw ^ 12 := by
    rw [← p1 r92 wf_r90 wf_r91 (by bm_strips CFSG.KC.BM.SevenGen.c_r92 69), e4, e8, ← pow_add]
  rw [← p1 bp wf_bpw wf_r92 (by bm_strips CFSG.KC.BM.SevenGen.c_bp 69), e12, ← pow_succ', hw]

theorem factSevenGen_of : FactSevenGen := by
  obtain ⟨-, -, ex, ey⟩ := g_pows
  refine ⟨⟨ex, ey, y_pow_five, notId_sound Seven.wf_x CFSG.KC.BM.SevenGen.ne_x1⟩,
    ⟨p1one wf_c wf_ci (by bm_strips CFSG.KC.BM.SevenGen.c_ci 69),
      (p2 s2 wf_ci Seven.wf_g wf_c (by bm_strips CFSG.KC.BM.SevenGen.c_s2 69)).symm,
      (p2 f wf_ci Seven.wf_x wf_c (by bm_strips CFSG.KC.BM.SevenGen.c_f 69)).symm,
      q11 Seven.wf_x wf_f wf_f Seven.wf_x (by bm_strips2 CFSG.KC.BM.SevenGen.comm_xf 69)⟩,
    ⟨fix_row, move_row⟩,
    ⟨p1one Seven.wf_g wf_gi (by bm_strips CFSG.KC.BM.SevenGen.c_gi 69),
      p1one wf_s2 wf_s2i (by bm_strips CFSG.KC.BM.SevenGen.c_s2i 69), ap_eq, bp_eq⟩,
    p1one wf_H wf_Hi (by bm_strips CFSG.KC.BM.SevenGen.int_HHi 69),
    q11 Seeds.wf_A1 wf_H wf_H wf_ap (by bm_strips2 CFSG.KC.BM.SevenGen.int_A1 69),
    q11 Seeds.wf_A2 wf_H wf_H wf_bp (by bm_strips2 CFSG.KC.BM.SevenGen.int_A2 69)⟩

end CertificateChecks.KernelBM.SevenGen

end
