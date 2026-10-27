module

public import CFSG.Certificates.Kernel.BabyMonster.Chain4
public import CFSG.Certificates.Kernel.BabyMonster.PairSound
public import CFSG.Certificates.Kernel.BabyMonster.WfProd
public import CFSG.Monster.B.Final.SeedUnit
public import Certificates.Kernel.BabyMonster.B31Regs
public import Certificates.Kernel.BabyMonster.Chain
public import Certificates.Kernel.BabyMonster.Seeds

public section

namespace CertificateChecks.KernelBM.B31

open CFSG.KC.BM CFSG.Monster.B CFSG.Blueprint
  CFSG.LocalAnalysis.AGL81I.Section3.SporBig.BThirtyOneNative

local notation "sm" => stripMat

set_option maxRecDepth 100000

theorem b31_mul {A B C : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (h : AllStrips [B] A C) : sm A * sm B = sm C := by
  have e := stripMat_mul_of_allStrips (Ws := [B]) (by simp [hB]) hA h
  simpa using e

theorem b31_eq {A B C D : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (hC : wfMat C = true) (hD : wfMat D = true) (h : AllStrips [B] A (C.map (mulW [D]))) :
    sm A * sm B = sm C * sm D := by
  have l := stripMat_mul_of_allStrips (Ws := [B]) (by simp [hB]) hA h
  have r := stripMat_mul_of_allStrips (Ws := [D]) (by simp [hD]) hC (Reg.allStrips_map [D] C)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at l r
  rw [l, r]

theorem wf_a_f3 : wfMat B31.a = true ∧ wfMat B31.f3 = true := by
  have w0 : wfMat Max5.m0 = true := wfMat_of_allStrips (Ws := [Seeds.A2]) Seeds.wf_A1
    (by bm_strips CFSG.KC.BM.Max5.cm0 69)
  have w3 : wfMat B31.n3 = true := wfMat_of_allStrips (Ws := [Max5.m20]) w0
    (by bm_strips4 CFSG.KC.BM.B31.c_n3 69)
  have w6 : wfMat B31.n6 = true := wfMat_of_allStrips (Ws := [B31.n4, B31.n5, Max5.m20]) w3
    (by bm_strips4 CFSG.KC.BM.B31.c_n6 69)
  have w8 : wfMat B31.n8 = true := wfMat_of_allStrips (Ws := [B31.n7]) w6
    (by bm_strips4 CFSG.KC.BM.B31.c_n8 69)
  have w33 : wfMat B31.n33 = true := wfMat_of_allStrips (Ws := [B31.n29]) w8
    (by bm_strips4 CFSG.KC.BM.B31.c_n33 69)
  have w26 : wfMat B31.n26 = true := wfMat_of_allStrips (Ws := [B31.n8]) w8
    (by bm_strips4 CFSG.KC.BM.B31.c_n26 69)
  have w37 : wfMat B31.n37 = true := wfMat_of_allStrips (Ws := [B31.n32, B31.n34]) w26
    (by bm_strips4 CFSG.KC.BM.B31.c_n37 69)
  have w41 : wfMat B31.n41 = true := wfMat_of_allStrips (Ws := [B31.n40]) w37
    (by bm_strips4 CFSG.KC.BM.B31.c_n41 69)
  have w63 : wfMat B31.n63 = true :=
    wfMat_of_allStrips (Ws := [B31.n60, B31.n52, B31.n55, B31.n61, B31.n62]) w41
      (by bm_strips4 CFSG.KC.BM.B31.c_n63 69)
  exact ⟨wfMat_of_allStrips (Ws := [B31.n8, B31.n30]) w33 (by bm_strips4 CFSG.KC.BM.B31.c_a 69),
    wfMat_of_allStrips (Ws := [B31.n64]) w63 (by bm_strips4 CFSG.KC.BM.B31.c_f3 69)⟩

theorem b31_mat : sm B31.a ^ 32 = sm B31.a ∧ sm B31.a ≠ 1 ∧
    sm B31.f3 * sm B31.a = sm B31.a ^ 2 * sm B31.f3 := by
  obtain ⟨wa, wf3⟩ := wf_a_f3
  have w2 : wfMat B31F.a2 = true := wfMat_of_allStrips (Ws := [B31.a]) wa
    (by bm_strips4 CFSG.KC.BM.B31F.c_a2 69)
  have w4 : wfMat B31F.a4 = true := wfMat_of_allStrips (Ws := [B31F.a2]) w2
    (by bm_strips4 CFSG.KC.BM.B31F.c_a4 69)
  have w8 : wfMat B31F.a8 = true := wfMat_of_allStrips (Ws := [B31F.a4]) w4
    (by bm_strips4 CFSG.KC.BM.B31F.c_a8 69)
  have w16 : wfMat B31F.a16 = true := wfMat_of_allStrips (Ws := [B31F.a8]) w8
    (by bm_strips4 CFSG.KC.BM.B31F.c_a16 69)
  have p2 : sm B31F.a2 = sm B31.a ^ 2 := by
    rw [← b31_mul wa wa (by bm_strips4 CFSG.KC.BM.B31F.c_a2 69), sq]
  have p4 : sm B31F.a4 = sm B31.a ^ 4 := by
    rw [← b31_mul w2 w2 (by bm_strips4 CFSG.KC.BM.B31F.c_a4 69), p2, ← pow_add]
  have p8 : sm B31F.a8 = sm B31.a ^ 8 := by
    rw [← b31_mul w4 w4 (by bm_strips4 CFSG.KC.BM.B31F.c_a8 69), p4, ← pow_add]
  have p16 : sm B31F.a16 = sm B31.a ^ 16 := by
    rw [← b31_mul w8 w8 (by bm_strips4 CFSG.KC.BM.B31F.c_a16 69), p8, ← pow_add]
  have h32 : sm B31F.a16 * sm B31F.a16 = sm B31.a :=
    b31_mul w16 w16 (by bm_strips4 CFSG.KC.BM.B31F.ord_a 69)
  refine ⟨?_, notId_sound wa B31F.ne_a, ?_⟩
  · calc sm B31.a ^ 32 = sm B31.a ^ 16 * sm B31.a ^ 16 := by rw [← pow_add]
      _ = sm B31.a := by rw [← p16, h32]
  · rw [← p2]
    exact b31_eq wf3 wa w2 wf3 (by bm_strips4 CFSG.KC.BM.B31F.cj_f3 69)

theorem bThirtyOne_facts :
    (Pinned.runG (bThirtyOneProg ()) bA₁ bA₂ 3) ^ 31 = 1 ∧
    Pinned.runG (bThirtyOneProg ()) bA₁ bA₂ 3 ≠ 1 ∧
    Pinned.runG (bThirtyOneProg ()) bA₁ bA₂ 2 * Pinned.runG (bThirtyOneProg ()) bA₁ bA₂ 3 =
      (Pinned.runG (bThirtyOneProg ()) bA₁ bA₂ 3) ^ 2 *
        Pinned.runG (bThirtyOneProg ()) bA₁ bA₂ 2 := by
  have hR := bMat_runG_of_regsOK KernelBM.genA₁_eq_stripMat KernelBM.genA₂_eq_stripMat
    bThirtyOne_regs
  have ha : bMat (Pinned.runG (bThirtyOneProg ()) bA₁ bA₂ 3) = sm B31.a := hR 0 (by norm_num)
  have hc : bMat (Pinned.runG (bThirtyOneProg ()) bA₁ bA₂ 2) = sm B31.f3 := hR 1 (by norm_num)
  obtain ⟨h32, h1, hcj⟩ := b31_mat
  set x := Pinned.runG (bThirtyOneProg ()) bA₁ bA₂ 3
  set y := Pinned.runG (bThirtyOneProg ()) bA₁ bA₂ 2
  have hx : x ^ 32 = x := bMat_injective (by rw [map_pow, ha, h32])
  refine ⟨?_, ne_one_of_bMat (by rw [ha]; exact h1),
    bMat_injective (by rw [map_mul, map_mul, map_pow, ha, hc, hcj])⟩
  have : x ^ 31 * x = 1 * x := by rw [← pow_succ, one_mul, hx]
  exact mul_right_cancel this

end CertificateChecks.KernelBM.B31

end
