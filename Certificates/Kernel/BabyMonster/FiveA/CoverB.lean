module

public import Certificates.Kernel.BabyMonster.Five.Facts
public import Certificates.Kernel.BabyMonster.FiveA.Facts13626
public import Certificates.Kernel.BabyMonster.FiveA.WitMem
public import CFSG.Monster.B.Final.SeedUnit
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Monster.B.Classical.PlaneAut

public section

namespace CertificateChecks.KernelBM.FiveA

open CFSG.KC.BM CFSG.KC.BM.Reg CFSG.KC.BM.PcFive CFSG.Monster.B CFSG.Blueprint
  CertificateChecks.KernelBM.Five
open CFSG.Monster.B.Pinned (xFive hFive bGL coe_bGL)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "MX" => stripMat CFSG.KC.BM.Five.f85
local notation "MH" => stripMat CFSG.KC.BM.Five.f86
local notation "MW" => stripMat CFSG.KC.BM.Five.W_sq3
local notation "M2" => stripMat CFSG.KC.BM.Five.Q2
local notation "M3" => stripMat CFSG.KC.BM.Five.Q3
local notation "M4" => stripMat CFSG.KC.BM.Five.Q4
local notation "MZ" => stripMat CFSG.KC.BM.Five.Z
local notation "SB" => NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1
  NativeSporadic.BSeed2

set_option maxRecDepth 100000

section Hom

variable {G H : Type*} [Group G] [Group H] (f : G →* H) {x h : G}

theorem map_evalW : ∀ w : List Lt, f (evalW x h w) = evalW (f x) (f h) w
  | [] => by simp [evalW]
  | l :: w => by cases l <;> simp [evalW, map_evalW w]

theorem map_psi (v : V6) :
    f (psi x (qW x h) (zW x h) v) = psi (f x) (qW (f x) (f h)) (zW (f x) (f h)) v := by
  simp only [PcFive.psi, map_mul, map_pow, Five.map_nfQ f]

variable {f}

theorem NaRel.of_hom (hf : Function.Injective f) (R : NaRel (f x) (f h)) : NaRel x h :=
  fun j hj => hf (by rw [map_mul, map_mul, map_inv, map_evalW, map_psi]; exact R j hj)

end Hom


theorem bGL_xFive : bGL xFive = xU := Units.ext (by rw [coe_bGL, five_bridge.1]; rfl)

theorem bGL_hFive : bGL hFive = hU := Units.ext (by rw [coe_bGL, five_bridge.2]; rfl)

theorem naRel_B : NaRel xFive hFive := by
  refine NaRel.of_hom bGL_injective ?_
  rw [bGL_xFive, bGL_hFive]
  exact naRel

theorem fact13625_B : FiveRel xFive hFive ∧ Fact13625 xFive hFive :=
  ⟨fiveRel_B, fact13625_of fiveRel_B naRel_B CertificateChecks.KernelBM.PcFive.phiOK_true⟩

theorem bMat_psi (v : V6) : bMat (psi xFive (qW xFive hFive) (zW xFive hFive) v) =
    MX ^ v.e * (MW ^ v.q.a0 * M2 ^ v.q.a1 * M3 ^ v.q.a2 * M4 ^ v.q.a3 * MZ ^ v.q.c) := by
  rw [← coe_bGL, map_psi, bGL_xFive, bGL_hFive]
  exact psi_val v

theorem bMat_qW (i : Fin 4) : bMat (qW xFive hFive i) = ((qW xU hU i : MatBˣ) : MatB) := by
  rw [← coe_bGL, Five.map_qW, bGL_xFive, bGL_hFive]

theorem bMat_zW : bMat (zW xFive hFive) = MZ := by
  rw [← coe_bGL, Five.map_zW, bGL_xFive, bGL_hFive]
  exact cz

theorem bMat_mem (g : NativeSporadic.B) : bMat g ∈ SB := (g : SB).2

theorem wit_SB : ∀ t ∈ [FiveA.v40, FiveA.v177, FiveA.v178, FiveA.v179], stripMat t ∈ SB := by
  refine wit_mem.2 SB fun a ha => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [← CertificateChecks.KernelBM.genA₁_eq_stripMat]
    exact Submonoid.subset_closure (Set.mem_insert _ _)
  · rw [← CertificateChecks.KernelBM.genA₂_eq_stripMat]
    exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)
  · rw [← cq1, ← bMat_qW]
    exact bMat_mem _
  · rw [← cq2, ← bMat_qW]
    exact bMat_mem _
  · rw [← cq3, ← bMat_qW]
    exact bMat_mem _
  · rw [← bMat_zW]
    exact bMat_mem _

theorem wit_B {W E : NativeSporadic.B} {MW' ME : MatB} (hW : bMat W = MW') (hE : bMat E = ME)
    (h : TwoBWit MW' ME) : W * W = 1 ∧ W ≠ 1 ∧ (bMat W - 1).rank = 2048 ∧ W * E = E * W := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨mul_self_of_bMat (by rw [hW]; exact h1), ne_one_of_bMat (by rw [hW]; exact h2),
    by rw [hW]; exact h3, comm_of_bMat (by rw [hW, hE]; exact h4)⟩

theorem seed_wit {t : List Nat} (ht : stripMat t ∈ SB) {ME : MatB} (h : TwoBWit (stripMat t) ME)
    {E : NativeSporadic.B} (hE : bMat E = ME) : ∃ W : NativeSporadic.B,
      W * W = 1 ∧ W ≠ 1 ∧ (bMat W - 1).rank = 2048 ∧ W * E = E * W :=
  ⟨seedUnit ht two_ne_zero (by rw [sq]; exact h.1),
    wit_B (bMat_seedUnit _ _ _) hE h⟩

local notation "P" => psi xFive (qW xFive hFive) (zW xFive hFive)

theorem wits13626 : ∀ i ∈ [1, 660, 30], ∃ W : NativeSporadic.B,
    W * W = 1 ∧ W ≠ 1 ∧ (bMat W - 1).rank = 2048 ∧ W * P (dec i) = P (dec i) * W := by
  obtain ⟨w1, w2, w3⟩ := fact13626
  have h4 : bMat (hFive ^ 4) = MH ^ 4 := by rw [map_pow, five_bridge.2]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact ⟨_, wit_B h4 (by rw [bMat_psi]; simp [dec, decQ]) w1⟩
  · exact ⟨_, wit_B h4 (by rw [bMat_psi]; simp [dec, decQ]) w2⟩
  · exact seed_wit (wit_SB _ (by simp)) w3 (by rw [bMat_psi]; simp [dec, decQ])

theorem wits13627 : ∀ i ∈ [3125, 3126, 3127], ∃ W : NativeSporadic.B,
    W * W = 1 ∧ W ≠ 1 ∧ (bMat W - 1).rank = 2048 ∧ W * P (dec i) = P (dec i) * W := by
  obtain ⟨w1, w2, w3⟩ := fact13627
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact seed_wit (wit_SB _ (by simp)) w1 (by rw [bMat_psi]; simp [dec, decQ])
  · exact seed_wit (wit_SB _ (by simp)) w2 (by rw [bMat_psi]; simp [dec, decQ])
  · exact seed_wit (wit_SB _ (by simp)) w3 (by rw [bMat_psi]; simp [dec, decQ])

end CertificateChecks.KernelBM.FiveA

end
