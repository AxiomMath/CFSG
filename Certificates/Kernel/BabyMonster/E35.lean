module

public import CFSG.Certificates.Kernel.BabyMonster.E35Fact
public import CFSG.Certificates.Kernel.BabyMonster.E35.All
public import CFSG.Certificates.Kernel.BabyMonster.Fi23.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Fi23.Check8
public import CFSG.Certificates.Kernel.BabyMonster.Chain4
public import CFSG.Certificates.Kernel.BabyMonster.Chain4Pair
public import CFSG.Certificates.Kernel.BabyMonster.Sound
public import CFSG.Certificates.Kernel.BabyMonster.PairSound
public import CFSG.Certificates.Kernel.BabyMonster.VStripSound
public import Certificates.Kernel.BabyMonster.Chain
public import CFSG.Certificates.Kernel.BabyMonster.E35.Check0
public import CFSG.Certificates.Kernel.BabyMonster.E35.Check1
public import CFSG.Certificates.Kernel.BabyMonster.E35.Check2
public import CFSG.Certificates.Kernel.BabyMonster.E35.Check3
public import CFSG.Certificates.Kernel.BabyMonster.E35.Check4
public import CFSG.Certificates.Kernel.BabyMonster.E35.Rel
public import CFSG.Certificates.Kernel.BabyMonster.E35.Wf
public import CFSG.Certificates.Kernel.BabyMonster.E35Cyc

public section

namespace CertificateChecks.KernelBM.E35

open CFSG.KC.BM CFSG.KC.BM.E35
open scoped Matrix

local notation "MX" => stripMat CFSG.KC.BM.E35.x
local notation "MG" => stripMat CFSG.KC.BM.E35.g

theorem mulA {A B C : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (h : AllStrips [B] A C) : stripMat A * stripMat B = stripMat C := by
  simpa using stripMat_mul_of_allStrips (Ws := [B]) (by simp [hB]) hA h

theorem mulB {A B C D : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (hC : wfMat C = true) (h : AllStrips [B, C] A D) :
    stripMat A * stripMat B * stripMat C = stripMat D := by
  simpa using stripMat_mul_of_allStrips (Ws := [B, C]) (by simp [hB, hC]) hA h

theorem oneA {A B : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (h : AllStrips [B] A idStrips) : stripMat A * stripMat B = 1 := by
  simpa using stripMat_mul_eq_one (Ws := [B]) (by simp [hB]) hA h

theorem eqA {A B C D : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (hC : wfMat C = true) (hD : wfMat D = true) (h : AllStrips2 [B] [D] A C) :
    stripMat A * stripMat B = stripMat C * stripMat D := by
  simpa using stripMat_mul_eq_of_allStrips2 (Ws := [B]) (Ds := [D]) (by simp [hB])
    (by simp [hD]) hA hC h

local notation "SUV" => Submonoid.closure {stripMat Fi23.U, stripMat Fi23.V}

theorem memStep (C : List Nat) {A B : List Nat} (hA : stripMat A ∈ SUV) (hB : stripMat B ∈ SUV)
    (wA : wfMat A = true) (wB : wfMat B = true) (h : AllStrips [B] A C) : stripMat C ∈ SUV :=
  mulA wA wB h ▸ Submonoid.mul_mem _ hA hB

theorem x_g_mem : MX ∈ SUV ∧ MG ∈ SUV := by
  have hU : stripMat Fi23.U ∈ SUV := Submonoid.subset_closure (Set.mem_insert _ _)
  have hV : stripMat Fi23.V ∈ SUV :=
    Submonoid.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have h16 := memStep Fi23.g16 hU hV Fi23.wf_U Fi23.wf_V (by bm_strips CFSG.KC.BM.Fi23.cg16 69)
  have hm4 := memStep m4 h16 hV Fi23.wf_g16 Fi23.wf_V (by bm_strips4 CFSG.KC.BM.E35.c_m4 69)
  have hm3s := memStep m3s h16 h16 Fi23.wf_g16 Fi23.wf_g16
    (by bm_strips4 CFSG.KC.BM.E35.c_m3s 69)
  have hm5 := memStep m5 hm3s h16 wf_m3s Fi23.wf_g16 (by bm_strips4 CFSG.KC.BM.E35.c_m5 69)
  have hm4s := memStep m4s hm4 hm4 wf_m4 wf_m4 (by bm_strips4 CFSG.KC.BM.E35.c_m4s 69)
  have hm2 := memStep m2 hm4s hm4 wf_m4s wf_m4 (by bm_strips4 CFSG.KC.BM.E35.c_m2 69)
  have hm6 := memStep m6 hm2 hm5 wf_m2 wf_m5 (by bm_strips4 CFSG.KC.BM.E35.c_m6 69)
  have hh1 := memStep h1 hm6 hm6 wf_m6 wf_m6 (by bm_strips4 CFSG.KC.BM.E35.c_h1 69)
  have hn5 := memStep n5 h16 hm4 Fi23.wf_g16 wf_m4 (by bm_strips4 CFSG.KC.BM.E35.c_n5 69)
  have hn6 := memStep n6 h16 hn5 Fi23.wf_g16 wf_n5 (by bm_strips4 CFSG.KC.BM.E35.c_n6 69)
  have hn3 := memStep n3 hn5 hm4 wf_n5 wf_m4 (by bm_strips4 CFSG.KC.BM.E35.c_n3 69)
  have hn5b := memStep n5b hn6 hn3 wf_n6 wf_n3 (by bm_strips4 CFSG.KC.BM.E35.c_n5b 69)
  have hn4 := memStep n4 hn3 hn6 wf_n3 wf_n6 (by bm_strips4 CFSG.KC.BM.E35.c_n4 69)
  have hh2 := memStep h2 hn5b hn4 wf_n5b wf_n4 (by bm_strips4 CFSG.KC.BM.E35.c_h2 69)
  have hp := memStep p hh1 hh2 wf_h1 wf_h2 (by bm_strips4 CFSG.KC.BM.E35.c_p 69)
  have hq := memStep q hp hh2 wf_p wf_h2 (by bm_strips4 CFSG.KC.BM.E35.c_q 69)
  have hpp := memStep pp hp hp wf_p wf_p (by bm_strips4 CFSG.KC.BM.E35.c_pp 69)
  have hppq := memStep ppq hpp hq wf_pp wf_q (by bm_strips4 CFSG.KC.BM.E35.c_ppq 69)
  have hppqq := memStep ppqq hppq hq wf_ppq wf_q (by bm_strips4 CFSG.KC.BM.E35.c_ppqq 69)
  have hwg := memStep wg hppqq hq wf_ppqq wf_q (by bm_strips4 CFSG.KC.BM.E35.c_wg 69)
  have hwg2 := memStep wg2 hwg hwg wf_wg wf_wg (by bm_strips4 CFSG.KC.BM.E35.c_wg2 69)
  have hg := memStep g hwg2 hwg wf_wg2 wf_wg (by bm_strips4 CFSG.KC.BM.E35.c_g 69)
  have hwx := memStep wx hq hppq wf_q wf_ppq (by bm_strips4 CFSG.KC.BM.E35.c_wx 69)
  have hwx2 := memStep wx2 hwx hwx wf_wx wf_wx (by bm_strips4 CFSG.KC.BM.E35.c_wx2 69)
  have hwx3 := memStep wx3 hwx2 hwx wf_wx2 wf_wx (by bm_strips4 CFSG.KC.BM.E35.c_wx3 69)
  exact ⟨memStep x hwx3 hwx3 wf_wx3 wf_wx3 (by bm_strips4 CFSG.KC.BM.E35.c_x 69), hg⟩

theorem g2_eq : stripMat g2 = MG ^ 2 := by
  rw [← mulA wf_g wf_g (by bm_strips4 CFSG.KC.BM.E35.c_g2 69), sq]

theorem g4_eq : stripMat g4 = MG ^ 4 := by
  rw [← mulA wf_g2 wf_g2 (by bm_strips4 CFSG.KC.BM.E35.c_g4 69), g2_eq, ← pow_add]

theorem z_eq : stripMat z = MG ^ 5 := by
  rw [← mulA wf_g4 wf_g (by bm_strips4 CFSG.KC.BM.E35.c_z 69), g4_eq, ← pow_succ]

theorem gi_eq : stripMat gi = MG ^ 9 := by
  rw [← mulA wf_z wf_g4 (by bm_strips4 CFSG.KC.BM.E35.c_gi 69), z_eq, g4_eq, ← pow_add]

theorem x1_eq : stripMat x1 = MG ^ 9 * MX * MG := by
  rw [← mulB wf_gi wf_x wf_g (by bm_strips4 CFSG.KC.BM.E35.c_x1 69), gi_eq]

theorem y2_eq : stripMat y2 = MG ^ 9 * (MG ^ 9 * MX * MG) * MG := by
  rw [← mulB wf_gi wf_x1 wf_g (by bm_strips4 CFSG.KC.BM.E35.c_y2 69), gi_eq, x1_eq]

theorem x_cube : MX ^ 3 = 1 := by
  have e := oneA wf_x2 wf_x (by bm_strips4 CFSG.KC.BM.E35.ord_x 69)
  rwa [← mulA wf_x wf_x (by bm_strips4 CFSG.KC.BM.E35.c_x2 69), ← sq, ← pow_succ] at e

theorem g_ten : MG ^ 10 = 1 := by
  have e := oneA wf_z wf_z (by bm_strips4 CFSG.KC.BM.E35.ord_z 69)
  rwa [z_eq, ← pow_add] at e

theorem P_ne : (MX * MG ^ 9) ^ 4 * MX * MG ^ 4 ≠ 1 := by
  intro e
  have h64 : nat_lit 0 < 64 := by norm_num
  have hr : vrow (rowOf (mulW [x, gi, x, gi, x, gi, x, gi, x, g4] (nat_lit 1)) (nat_lit 0)) =
      vrow (rowOf (nat_lit 1) (nat_lit 0)) ᵥ* MX ᵥ* stripMat gi ᵥ* MX ᵥ* stripMat gi ᵥ* MX ᵥ*
        stripMat gi ᵥ* MX ᵥ* stripMat gi ᵥ* MX ᵥ* stripMat g4 := by
    have hn : ∀ X, mulW [] X = X := fun _ => rfl
    simp only [mulW_cons, hn, mulS_rows wf_g4 _ h64, mulS_rows wf_gi _ h64,
      mulS_rows wf_x _ h64]
  have hp : MX * stripMat gi * MX * stripMat gi * MX * stripMat gi * MX * stripMat gi * MX *
      stripMat g4 = 1 := by
    rw [gi_eq, g4_eq, ← e]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  simp only [Matrix.vecMul_vecMul] at hr
  rw [hp, Matrix.vecMul_one] at hr
  have hc := CFSG.KC.BM.E35.ne_P
  rw [rowOf_inj hr, Nat.beq_refl] at hc
  exact absurd hc (by decide)

theorem fact431004_of :
    stripMat x ∈ Submonoid.closure {stripMat Fi23.U, stripMat Fi23.V} ∧
      stripMat g ∈ Submonoid.closure {stripMat Fi23.U, stripMat Fi23.V} ∧
      CycFacts (stripMat x) (stripMat g) := by
  obtain ⟨hx, hg⟩ := x_g_mem
  unfold CycFacts
  refine ⟨hx, hg, x_cube, g_ten, z_eq ▸ notId_sound wf_z CFSG.KC.BM.E35.ne_z, ?_, ?_, ?_, ?_,
    P_ne⟩
  · rw [← z_eq]
    exact eqA wf_z wf_x wf_x wf_z (by bm_strips2_4 CFSG.KC.BM.E35.cm_zx 69)
  · rw [← x1_eq]
    exact eqA wf_x wf_x1 wf_x1 wf_x (by bm_strips2_4 CFSG.KC.BM.E35.cm_x1 69)
  · rw [← y2_eq]
    exact eqA wf_x wf_y2 wf_y2 wf_x (by bm_strips2_4 CFSG.KC.BM.E35.cm_y2 69)
  · rw [← x1_eq]
    exact eqMat_sound wf_x1 wf_x CFSG.KC.BM.E35.ne_x1

end CertificateChecks.KernelBM.E35

end
