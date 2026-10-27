module

public import Certificates.Kernel.BabyMonster.FiveA.Facts13625
public import Certificates.Kernel.BabyMonster.Five.Regs
public import Certificates.Kernel.BabyMonster.Seeds
public import CFSG.Certificates.Kernel.BabyMonster.PairSound
public import CFSG.Monster.B.Pinned.Primes.FiveWords
public import CFSG.Monster.B.Pinned.Primes.Data
public import CFSG.RankThree.Native.BFiveHCheckInputs
public import CFSG.Monster.B.Cbar.SimpleBase

public section

namespace CertificateChecks.KernelBM.Five

open CFSG.KC.BM CFSG.KC.BM.Reg CFSG.KC.BM.PcFive CFSG.Monster.B CFSG.Monster.B.Pinned
  CFSG.Monster.B.Primes.Native CFSG.Blueprint CertificateChecks.KernelBM.FiveA

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

set_option maxRecDepth 100000

section Hom

variable {G H : Type*} [Group G] [Group H] (f : G →* H) {x h : G}

theorem map_qW (i : Fin 4) : f (qW x h i) = qW (f x) (f h) i := by
  fin_cases i <;> simp [qW, qOne]

theorem map_zW : f (zW x h) = zW (f x) (f h) := by
  simp only [zW, map_mul, map_inv, map_qW]

theorem map_nfQ (a : QV) : f (nfQ (qW x h) (zW x h) a) = nfQ (qW (f x) (f h)) (zW (f x) (f h)) a := by
  simp only [nfQ, map_mul, map_pow, map_qW, map_zW]

variable {f}

theorem FiveRel.of_hom (hf : Function.Injective f) (R : FiveRel (f x) (f h)) : FiveRel x h where
  x5 := hf (by rw [map_pow, map_one]; exact R.x5)
  h8 := hf (by rw [map_pow, map_one]; exact R.h8)
  q5 := hf (by rw [map_pow, map_one, map_qW]; exact R.q5)
  z5 := hf (by rw [map_pow, map_one, map_zW]; exact R.z5)
  z1 := fun e => R.z1 (by rw [← map_zW, e, map_one])
  zq i := hf (by simp only [map_mul, map_qW, map_zW]; exact R.zq i)
  zx := hf (by simp only [map_mul, map_zW]; exact R.zx)
  c01 := hf (by simp only [map_mul, map_qW, map_zW]; exact R.c01)
  c02 := hf (by simp only [map_mul, map_pow, map_qW, map_zW]; exact R.c02)
  c03 := hf (by simp only [map_mul, map_qW, map_zW]; exact R.c03)
  c12 := hf (by simp only [map_mul, map_qW]; exact R.c12)
  c13 := hf (by simp only [map_mul, map_pow, map_qW, map_zW]; exact R.c13)
  c23 := hf (by simp only [map_mul, map_qW, map_zW]; exact R.c23)
  ax2 := hf (by simp only [map_mul, map_inv, map_qW, map_nfQ]; exact R.ax2)
  ax3 := hf (by simp only [map_mul, map_inv, map_qW, map_nfQ]; exact R.ax3)
  ah1 := hf (by simp only [map_mul, map_inv, map_qW, map_nfQ]; exact R.ah1)
  ah2 := hf (by simp only [map_mul, map_inv, map_qW, map_nfQ]; exact R.ah2)
  ah3 := hf (by simp only [map_mul, map_inv, map_qW, map_nfQ]; exact R.ah3)
  ahz := hf (by simp only [map_mul, map_inv, map_pow, map_zW]; exact R.ahz)

end Hom

theorem five_bridge :
    bMat xFive = stripMat CFSG.KC.BM.Five.f85 ∧ bMat hFive = stripMat CFSG.KC.BM.Five.f86 := by
  have hw := pinned_B_five_primary_word_data.2.2.2.2.1 (CFSG.Monster.B.progInit bA₁ bA₂)
    (by simp [CFSG.Monster.B.progInit]) (by simp [CFSG.Monster.B.progInit])
  have hρ := five_regs bMat (CFSG.Monster.B.progInit bA₁ bA₂) ?_ ?_
  · have h0 := hρ 0 (by decide)
    have h1 := hρ 1 (by decide)
    change bMat ((fiveProg ()).foldl insStepG (CFSG.Monster.B.progInit bA₁ bA₂) 1) =
      stripMat CFSG.KC.BM.Five.f85 at h0
    change bMat ((fiveProg ()).foldl insStepG (CFSG.Monster.B.progInit bA₁ bA₂) 2) =
      stripMat CFSG.KC.BM.Five.f86 at h1
    rw [hw.1] at h0
    rw [hw.2] at h1
    exact ⟨h0, h1⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · simpa [CFSG.Monster.B.progInit, bMat_bA₁] using KernelBM.genA₁_eq_stripMat
    · simpa [CFSG.Monster.B.progInit, bMat_bA₂] using KernelBM.genA₂_eq_stripMat
  · intro _ r hr
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hr
    simp [CFSG.Monster.B.progInit, hr.1, hr.2]

theorem bGL_injective : Function.Injective bGL := fun a b e =>
  bMat_injective (by rw [← coe_bGL, ← coe_bGL, e])

theorem fiveRel_B : FiveRel xFive hFive := by
  refine FiveRel.of_hom bGL_injective ?_
  have ex : bGL xFive = xU := Units.ext (by rw [coe_bGL, five_bridge.1]; rfl)
  have eh : bGL hFive = hU := Units.ext (by rw [coe_bGL, five_bridge.2]; rfl)
  rw [ex, eh]
  exact fiveRel

theorem qFive_eq (i : Fin 4) : qFive i = qW xFive hFive i := by
  fin_cases i <;> simp [qFive, qW, qOne, qBaseFive, wFive, mul_assoc]

theorem zFive_eq : zFive = zW xFive hFive := by
  simp only [zFive, zW, bcomm, qFive_eq]

theorem bcomm_of {G : Type*} [Group G] {a b z : G} {k : ℕ} (h : a * b = b * a * z ^ k) :
    bcomm a b = z ^ k := by
  rw [bcomm, mul_assoc (a⁻¹ * b⁻¹), h]
  group

theorem bcomm_of1 {G : Type*} [Group G] {a b z : G} (h : a * b = b * a * z) : bcomm a b = z := by
  rw [bcomm, mul_assoc (a⁻¹ * b⁻¹), h]
  group

section Rows

variable {G : Type*} [Group G] {x h : G}

theorem comm_rows (R : FiveRel x h) (i j : Fin 4) (hij : i < j) :
    bcomm (qW x h i) (qW x h j) = zW x h ^ ((fiveCommRows.getD i []).getD j 0) := by
  fin_cases i <;> fin_cases j <;> simp only [Fin.isValue] at hij ⊢ <;>
    first | exact absurd hij (by decide) | skip
  · simpa [fiveCommRows] using bcomm_of1 R.c01
  · simpa [fiveCommRows] using bcomm_of R.c02
  · simpa [fiveCommRows] using bcomm_of1 R.c03
  · simpa [fiveCommRows] using bcomm_of (z := zW x h) (k := 0) (by rw [pow_zero, mul_one]; exact R.c12)
  · simpa [fiveCommRows] using bcomm_of R.c13
  · simpa [fiveCommRows] using bcomm_of1 R.c23

theorem act_rows (R : FiveRel x h) (i : Fin 4) :
    x⁻¹ * qW x h i * x =
      (List.ofFn fun j => qW x h j ^ (fiveActRows.getD i []).getD j 0).prod *
        zW x h ^ fiveActC.getD i 0 := by
  fin_cases i <;> simp only [Fin.isValue]
  · simp [List.ofFn_succ, fiveActRows, fiveActC] <;> rfl
  · simp [List.ofFn_succ, fiveActRows, fiveActC] <;> rfl
  · refine R.ax2.trans ?_
    simp [nfQ, xAct, List.ofFn_succ, fiveActRows, fiveActC, mul_assoc]
  · refine R.ax3.trans ?_
    simp [nfQ, xAct, List.ofFn_succ, fiveActRows, fiveActC, mul_assoc]

theorem hact_rows (R : FiveRel x h) (i : Fin 4) :
    h⁻¹ * qW x h i * h =
      (List.ofFn fun j => qW x h j ^ (CFSG.RankThree.Native.bFiveHRows.getD i []).getD j 0).prod *
        zW x h ^ CFSG.RankThree.Native.bFiveHC.getD i 0 := by
  fin_cases i <;> simp only [Fin.isValue]
  · simp [List.ofFn_succ, CFSG.RankThree.Native.bFiveHRows, CFSG.RankThree.Native.bFiveHC] <;> rfl
  · refine R.ah1.trans ?_
    simp [nfQ, hAct, List.ofFn_succ, CFSG.RankThree.Native.bFiveHRows,
      CFSG.RankThree.Native.bFiveHC, mul_assoc]
  · refine R.ah2.trans ?_
    simp [nfQ, hAct, List.ofFn_succ, CFSG.RankThree.Native.bFiveHRows,
      CFSG.RankThree.Native.bFiveHC, mul_assoc]
  · refine R.ah3.trans ?_
    simp [nfQ, hAct, List.ofFn_succ, CFSG.RankThree.Native.bFiveHRows,
      CFSG.RankThree.Native.bFiveHC, mul_assoc]

end Rows

theorem x_ne_one : xFive ≠ 1 := by
  intro e
  have h := orbOK_sound (V := CFSG.KC.BM.Five.Vox) (A := CFSG.KC.BM.Five.f85) (m := 5) (m₁ := 4)
    rfl (by norm_num) CFSG.KC.BM.Five.wf_f85 CFSG.KC.BM.Five.ox_orb 1 (by norm_num) (by norm_num)
  rw [pow_one, ← five_bridge.1, e, map_one] at h
  exact h rfl

theorem h4_ne_one : hFive ^ 4 ≠ 1 := by
  intro e
  have h := orbOK_sound (V := CFSG.KC.BM.Five.Voh) (A := CFSG.KC.BM.Five.f86) (m := 8) (m₁ := 7)
    rfl (by norm_num) CFSG.KC.BM.Five.wf_f86 CFSG.KC.BM.Five.oh_orb 4 (by norm_num) (by norm_num)
  rw [← five_bridge.2, ← map_pow, e, map_one] at h
  exact h rfl

theorem w20_ne_one : wFive ^ 20 ≠ 1 := by
  intro e
  have h := orbOK_sound (V := CFSG.KC.BM.Five.Vow) (A := CFSG.KC.BM.Five.W) (m := 40) (m₁ := 39)
    rfl (by norm_num) CFSG.KC.BM.Five.wf_W CFSG.KC.BM.Five.ow_orb 20 (by norm_num) (by norm_num)
  have hW : stripMat CFSG.KC.BM.Five.W = bMat wFive := by
    rw [← mul1 CFSG.KC.BM.Five.wf_f85 CFSG.KC.BM.Five.wf_H3
      (by bm_strips CFSG.KC.BM.Five.cW 69), h_three, wFive, map_mul, map_pow, five_bridge.1,
      five_bridge.2]
  rw [hW, ← map_pow, e, map_one] at h
  exact h rfl

theorem conj_pow_eq {G : Type*} [Group G] (a b : G) (n : ℕ) :
    (a⁻¹ * b * a) ^ n = a⁻¹ * b ^ n * a := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, pow_succ]; group

theorem q_facts (i : Fin 4) : qFive i ^ 5 = 1 ∧ qFive i ≠ 1 := by
  have R := fiveRel_B
  have h0 : qW xFive hFive 0 ^ 5 = 1 ∧ qW xFive hFive 0 ≠ 1 := by
    refine ⟨R.q5, fun e => R.z1 ?_⟩
    have e1 : qW xFive hFive 1 = hFive⁻¹ * qW xFive hFive 0 * hFive := rfl
    rw [zW, e1, e]
    group
  have conj : ∀ a b : NativeSporadic.B, b ^ 5 = 1 ∧ b ≠ 1 →
      (a⁻¹ * b * a) ^ 5 = 1 ∧ a⁻¹ * b * a ≠ 1 := by
    rintro a b ⟨h5, h1⟩
    refine ⟨by rw [conj_pow_eq, h5]; group, fun e => h1 ?_⟩
    calc b = a * (a⁻¹ * b * a) * a⁻¹ := by group
      _ = 1 := by rw [e]; group
  have h1 := conj hFive _ h0
  rw [qFive_eq]
  fin_cases i
  · exact h0
  · exact h1
  · exact conj xFive _ h0
  · exact conj xFive _ h1

theorem fact3159 :
    xFive ^ 5 = 1 ∧ xFive ≠ 1 ∧ hFive ^ 8 = 1 ∧ hFive ^ 4 ≠ 1 ∧ wFive ^ 40 = 1 ∧
      wFive ^ 20 ≠ 1 ∧ wFive ^ 8 ≠ 1 ∧ (∀ i, qFive i ^ 5 = 1 ∧ qFive i ≠ 1) ∧ zFive ^ 5 = 1 ∧
      zFive ≠ 1 ∧ (∀ i, qFive i * zFive = zFive * qFive i) ∧
      (∀ i j : Fin 4, i < j →
        bcomm (qFive i) (qFive j) = zFive ^ ((fiveCommRows.getD i []).getD j 0)) ∧
      xFive * zFive = zFive * xFive ∧
      ∀ i : Fin 4, xFive⁻¹ * qFive i * xFive =
        (List.ofFn fun j => qFive j ^ (fiveActRows.getD i []).getD j 0).prod *
          zFive ^ fiveActC.getD i 0 := by
  have R := fiveRel_B
  have hw8 : wFive ^ 8 = qFive 0 := rfl
  refine ⟨R.x5, x_ne_one, R.h8, h4_ne_one, ?_, w20_ne_one, ?_, q_facts, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (40 : ℕ) = 8 * 5 by norm_num, pow_mul, hw8]
    exact (q_facts 0).1
  · rw [hw8]
    exact (q_facts 0).2
  · rw [zFive_eq]; exact R.z5
  · rw [zFive_eq]; exact R.z1
  · intro i
    rw [zFive_eq, qFive_eq]
    exact R.zq i
  · intro i j hij
    rw [zFive_eq, qFive_eq, qFive_eq]
    exact comm_rows R i j hij
  · rw [zFive_eq]; exact R.zx
  · intro i
    simp only [qFive_eq, zFive_eq]
    exact act_rows R i

theorem fact8120 :
    (∀ i : Fin 4, hFive⁻¹ * qFive i * hFive =
      (List.ofFn fun j => qFive j ^ (CFSG.RankThree.Native.bFiveHRows.getD i []).getD j 0).prod *
        zFive ^ CFSG.RankThree.Native.bFiveHC.getD i 0) ∧
    hFive⁻¹ * zFive * hFive = zFive * zFive := by
  have R := fiveRel_B
  refine ⟨fun i => ?_, ?_⟩
  · simp only [qFive_eq, zFive_eq]
    exact hact_rows R i
  · rw [zFive_eq, R.ahz, sq]

end CertificateChecks.KernelBM.Five

end
