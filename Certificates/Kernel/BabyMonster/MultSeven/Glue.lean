module

public import CFSG.Certificates.Kernel.BabyMonster.PairSound
public import CFSG.Certificates.Kernel.BabyMonster.WfProd
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.All
public import CFSG.Certificates.Kernel.BabyMonster.Max5.All
public import CFSG.Certificates.Kernel.BabyMonster.MultSeven.All
public import CFSG.Certificates.Kernel.BabyMonster.MultSeven.Vecs
public import Certificates.Kernel.BabyMonster.Chain
public import Certificates.Kernel.BabyMonster.Chain2
public import Certificates.Kernel.BabyMonster.MemChain
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenCensusRot
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Check4
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Check5
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Check6
public import CFSG.Certificates.Kernel.BabyMonster.Max5.Check7
public import CFSG.Certificates.Kernel.BabyMonster.MultSeven.Check0
public import CFSG.Certificates.Kernel.BabyMonster.MultSeven.Check1
public import CFSG.Certificates.Kernel.BabyMonster.MultSeven.Check2
public import CFSG.Certificates.Kernel.BabyMonster.MultSeven.Check3
public import CFSG.Certificates.Kernel.BabyMonster.MultSeven.Check4
public import CFSG.Certificates.Kernel.BabyMonster.MultSeven.Check5
public import CFSG.Certificates.Kernel.BabyMonster.MultSeven.Check6
public import CFSG.Certificates.Kernel.BabyMonster.MultSeven.Rot0
public import CFSG.Certificates.Kernel.BabyMonster.MultSeven.Rot1
public import CFSG.Certificates.Kernel.BabyMonster.MultSeven.Square0
public import CFSG.Certificates.Kernel.BabyMonster.MultSeven.Square1
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check4
public import CFSG.Open.Defs

public section

namespace CFSG.KC.BM.MultSevenGlue

open CFSG.KC.BM CFSG.KC.BM.SL CFSG.SectionRank.LocalWitness CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open scoped Matrix

abbrev Mt := Matrix (Fin 4370) (Fin 4370) (ZMod 2)

local notation "sm" => stripMat

section Chain

variable {S : Submonoid Mt}

abbrev Good (S : Submonoid Mt) (A : List Nat) : Prop := wfMat A = true ∧ sm A ∈ S

theorem gm {A B C : List Nat} (hA : Good S A) (hB : Good S B) (h : AllStrips [B] A C) :
    Good S C :=
  ⟨wfMat_of_allStrips hA.1 h, by rw [← stripMat_mul1 hA.1 hB.1 h]; exact S.mul_mem hA.2 hB.2⟩

theorem gi {A B : List Nat} (hA : Good S A) (wB : wfMat B = true)
    (h : AllStrips [B] A idStrips) : Good S B :=
  ⟨wB, MemChain.mem_of_mul_eq_one hA.2 (stripMat_mul1_one hA.1 wB h)⟩

theorem chain (hA1 : sm Seeds.A1 ∈ S) (hA2 : sm Seeds.A2 ∈ S) :
    Good S MultSeven.x ∧ Good S MultSeven.h3 ∧ Good S MultSeven.h4 ∧ Good S MultSeven.x2 ∧
      Good S MultSeven.x4 ∧ Good S MultSeven.hx ∧ Good S MultSeven.y ∧ Good S MultSeven.y2 ∧
      Good S MultSeven.b43q1 ∧ Good S MultSeven.b45q1 := by
  have g1 : Good S Seeds.A1 := ⟨Seeds.wf_A1, hA1⟩
  have g2 : Good S Seeds.A2 := ⟨Seeds.wf_A2, hA2⟩
  have m0 : Good S Max5.m0 := gm g1 g2 (by bm_strips CFSG.KC.BM.Max5.cm0 69)
  have m1 : Good S Max5.m1 := gm m0 g2 (by bm_strips CFSG.KC.BM.Max5.cm1 69)
  have m2 : Good S Max5.m2 := gm m0 m1 (by bm_strips CFSG.KC.BM.Max5.cm2 69)
  have m3 : Good S Max5.m3 := gm m0 m2 (by bm_strips CFSG.KC.BM.Max5.cm3 69)
  have m4 : Good S Max5.m4 := gm m3 m3 (by bm_strips CFSG.KC.BM.Max5.cm4 69)
  have m5 : Good S Max5.m5 := gm m4 m4 (by bm_strips CFSG.KC.BM.Max5.cm5 69)
  have m6 : Good S Max5.m6 := gm m4 m5 (by bm_strips CFSG.KC.BM.Max5.cm6 69)
  have m7 : Good S Max5.m7 := gm m5 m6 (by bm_strips CFSG.KC.BM.Max5.cm7 69)
  have m8 : Good S Max5.m8 := gm m1 m1 (by bm_strips CFSG.KC.BM.Max5.cm8 69)
  have m9 : Good S Max5.m9 := gm m8 m8 (by bm_strips CFSG.KC.BM.Max5.cm9 69)
  have m10 : Good S Max5.m10 := gm m9 m9 (by bm_strips CFSG.KC.BM.Max5.cm10 69)
  have m11 : Good S Max5.m11 := gm m10 m10 (by bm_strips CFSG.KC.BM.Max5.cm11 69)
  have m12 : Good S Max5.m12 := gm m1 m11 (by bm_strips CFSG.KC.BM.Max5.cm12 69)
  have m13 : Good S Max5.m13 := gi m12 Max5.wf_m13 (by bm_strips CFSG.KC.BM.Max5.cm13 69)
  have m14 : Good S Max5.m14 := gm m13 g2 (by bm_strips CFSG.KC.BM.Max5.cm14 69)
  have m15 : Good S Max5.m15 := gm m14 m12 (by bm_strips CFSG.KC.BM.Max5.cm15 69)
  have m16 : Good S Max5.m16 := gm m0 m0 (by bm_strips CFSG.KC.BM.Max5.cm16 69)
  have m17 : Good S Max5.m17 := gm m0 m16 (by bm_strips CFSG.KC.BM.Max5.cm17 69)
  have m18 : Good S Max5.m18 := gm m17 m17 (by bm_strips CFSG.KC.BM.Max5.cm18 69)
  have m19 : Good S Max5.m19 := gm m18 m18 (by bm_strips CFSG.KC.BM.Max5.cm19 69)
  have m20 : Good S Max5.m20 := gm m0 m19 (by bm_strips CFSG.KC.BM.Max5.cm20 69)
  have m21 : Good S Max5.m21 := gi m20 Max5.wf_m21 (by bm_strips CFSG.KC.BM.Max5.cm21 69)
  have m22 : Good S Max5.m22 := gm m21 m7 (by bm_strips CFSG.KC.BM.Max5.cm22 69)
  have m23 : Good S Max5.m23 := gm m22 m20 (by bm_strips CFSG.KC.BM.Max5.cm23 69)
  have b24 : Good S MultSeven.b24 := gm m23 m15 (by bm_strips CFSG.KC.BM.MultSeven.c_b24 69)
  have b25 : Good S MultSeven.b25 := gm b24 m15 (by bm_strips CFSG.KC.BM.MultSeven.c_b25 69)
  have b26q1 : Good S MultSeven.b26q1 :=
    gm b24 b24 (by bm_strips CFSG.KC.BM.MultSeven.c_b26q1 69)
  have b26q2 : Good S MultSeven.b26q2 :=
    gm b26q1 b26q1 (by bm_strips CFSG.KC.BM.MultSeven.c_b26q2 69)
  have b27 : Good S MultSeven.b27 := gm b26q2 b25 (by bm_strips CFSG.KC.BM.MultSeven.c_b27 69)
  have b28q1 : Good S MultSeven.b28q1 :=
    gm b25 b25 (by bm_strips CFSG.KC.BM.MultSeven.c_b28q1 69)
  have b28q2 : Good S MultSeven.b28q2 :=
    gm b28q1 b28q1 (by bm_strips CFSG.KC.BM.MultSeven.c_b28q2 69)
  have b28q3 : Good S MultSeven.b28q3 :=
    gm b28q2 b28q2 (by bm_strips CFSG.KC.BM.MultSeven.c_b28q3 69)
  have b29 : Good S MultSeven.b29 := gm b28q3 b25 (by bm_strips CFSG.KC.BM.MultSeven.c_b29 69)
  have b31 : Good S MultSeven.b31 :=
    gm b28q3 b26q1 (by bm_strips CFSG.KC.BM.MultSeven.c_b31 69)
  have b32 : Good S MultSeven.b32 := gm b24 b26q2 (by bm_strips CFSG.KC.BM.MultSeven.c_b32 69)
  have b33 : Good S MultSeven.b33 := gm b32 b32 (by bm_strips CFSG.KC.BM.MultSeven.c_b33 69)
  have b34 : Good S MultSeven.b34 := gm b32 b31 (by bm_strips CFSG.KC.BM.MultSeven.c_b34 69)
  have b35 : Good S MultSeven.b35 := gm b33 b29 (by bm_strips CFSG.KC.BM.MultSeven.c_b35 69)
  have b36q1 : Good S MultSeven.b36q1 :=
    gm b27 b27 (by bm_strips CFSG.KC.BM.MultSeven.c_b36q1 69)
  have b36q2 : Good S MultSeven.b36q2 :=
    gm b36q1 b36q1 (by bm_strips CFSG.KC.BM.MultSeven.c_b36q2 69)
  have b36 : Good S MultSeven.b36 := gm b27 b36q2 (by bm_strips CFSG.KC.BM.MultSeven.c_b36 69)
  have b37q1 : Good S MultSeven.b37q1 :=
    gm b34 b34 (by bm_strips CFSG.KC.BM.MultSeven.c_b37q1 69)
  have b37q2 : Good S MultSeven.b37q2 :=
    gm b37q1 b37q1 (by bm_strips CFSG.KC.BM.MultSeven.c_b37q2 69)
  have b37q3 : Good S MultSeven.b37q3 :=
    gm b37q2 b37q2 (by bm_strips CFSG.KC.BM.MultSeven.c_b37q3 69)
  have b37q4 : Good S MultSeven.b37q4 :=
    gm b37q3 b37q3 (by bm_strips CFSG.KC.BM.MultSeven.c_b37q4 69)
  have b37 : Good S MultSeven.b37 := gm b34 b37q4 (by bm_strips CFSG.KC.BM.MultSeven.c_b37 69)
  have b38 : Good S MultSeven.b38 := gm m15 b34 (by bm_strips CFSG.KC.BM.MultSeven.c_b38 69)
  have h3 : Good S MultSeven.h3 := gm b37 b38 (by bm_strips CFSG.KC.BM.MultSeven.c_h3 69)
  have b40q1 : Good S MultSeven.b40q1 :=
    gm b35 b35 (by bm_strips CFSG.KC.BM.MultSeven.c_b40q1 69)
  have b40 : Good S MultSeven.b40 := gm b35 b40q1 (by bm_strips CFSG.KC.BM.MultSeven.c_b40 69)
  have b41 : Good S MultSeven.b41 := gm b36 b35 (by bm_strips CFSG.KC.BM.MultSeven.c_b41 69)
  have h4 : Good S MultSeven.h4 := gm b40 b41 (by bm_strips CFSG.KC.BM.MultSeven.c_h4 69)
  have b43q1 : Good S MultSeven.b43q1 :=
    gm h3 h3 (by bm_strips CFSG.KC.BM.MultSeven.c_b43q1 69)
  have b44 : Good S MultSeven.b44 := gm h4 b43q1 (by bm_strips CFSG.KC.BM.MultSeven.c_b44 69)
  have b45q1 : Good S MultSeven.b45q1 :=
    gm h4 h4 (by bm_strips CFSG.KC.BM.MultSeven.c_b45q1 69)
  have b46 : Good S MultSeven.b46 := gm b44 b45q1 (by bm_strips CFSG.KC.BM.MultSeven.c_b46 69)
  have b47 : Good S MultSeven.b47 := gm b46 h3 (by bm_strips CFSG.KC.BM.MultSeven.c_b47 69)
  have x : Good S MultSeven.x := gm b47 h4 (by bm_strips CFSG.KC.BM.MultSeven.c_x 69)
  have x2 : Good S MultSeven.x2 := gm x x (by bm_strips CFSG.KC.BM.MultSeven.c_x2 69)
  have x4 : Good S MultSeven.x4 := gm x2 x2 (by bm_strips CFSG.KC.BM.MultSeven.c_x4 69)
  have hx : Good S MultSeven.hx := gm h3 x (by bm_strips CFSG.KC.BM.MultSeven.c_hx 69)
  have y : Good S MultSeven.y := gm hx b43q1 (by bm_strips CFSG.KC.BM.MultSeven.c_y 69)
  have y2 : Good S MultSeven.y2 := gm y y (by bm_strips CFSG.KC.BM.MultSeven.c_y2 69)
  exact ⟨x, h3, h4, x2, x4, hx, y, y2, b43q1, b45q1⟩

end Chain

local notation "chainTop" => chain (S := ⊤) (Submonoid.mem_top _) (Submonoid.mem_top _)

theorem wf_x : wfMat MultSeven.x = true := chainTop.1.1
theorem wf_h3 : wfMat MultSeven.h3 = true := chainTop.2.1.1
theorem wf_h4 : wfMat MultSeven.h4 = true := chainTop.2.2.1.1
theorem wf_x2 : wfMat MultSeven.x2 = true := chainTop.2.2.2.1.1
theorem wf_x4 : wfMat MultSeven.x4 = true := chainTop.2.2.2.2.1.1
theorem wf_hx : wfMat MultSeven.hx = true := chainTop.2.2.2.2.2.1.1
theorem wf_y : wfMat MultSeven.y = true := chainTop.2.2.2.2.2.2.1.1
theorem wf_y2 : wfMat MultSeven.y2 = true := chainTop.2.2.2.2.2.2.2.1.1
theorem wf_b43q1 : wfMat MultSeven.b43q1 = true := chainTop.2.2.2.2.2.2.2.2.1.1
theorem wf_b45q1 : wfMat MultSeven.b45q1 = true := chainTop.2.2.2.2.2.2.2.2.2.1

theorem e_x2 : sm MultSeven.x * sm MultSeven.x = sm MultSeven.x2 :=
  stripMat_mul1 wf_x wf_x (by bm_strips CFSG.KC.BM.MultSeven.c_x2 69)
theorem e_x4 : sm MultSeven.x2 * sm MultSeven.x2 = sm MultSeven.x4 :=
  stripMat_mul1 wf_x2 wf_x2 (by bm_strips CFSG.KC.BM.MultSeven.c_x4 69)
theorem e_hx : sm MultSeven.h3 * sm MultSeven.x = sm MultSeven.hx :=
  stripMat_mul1 wf_h3 wf_x (by bm_strips CFSG.KC.BM.MultSeven.c_hx 69)
theorem e_y : sm MultSeven.hx * sm MultSeven.b43q1 = sm MultSeven.y :=
  stripMat_mul1 wf_hx wf_b43q1 (by bm_strips CFSG.KC.BM.MultSeven.c_y 69)
theorem e_y2 : sm MultSeven.y * sm MultSeven.y = sm MultSeven.y2 :=
  stripMat_mul1 wf_y wf_y (by bm_strips CFSG.KC.BM.MultSeven.c_y2 69)
theorem e_b43 : sm MultSeven.h3 * sm MultSeven.h3 = sm MultSeven.b43q1 :=
  stripMat_mul1 wf_h3 wf_h3 (by bm_strips CFSG.KC.BM.MultSeven.c_b43q1 69)
theorem e_b45 : sm MultSeven.h4 * sm MultSeven.h4 = sm MultSeven.b45q1 :=
  stripMat_mul1 wf_h4 wf_h4 (by bm_strips CFSG.KC.BM.MultSeven.c_b45q1 69)

theorem e_x7 : sm MultSeven.x4 * sm MultSeven.x2 * sm MultSeven.x = 1 := by
  have h := stripMat_mul_eq_one (Ws := [MultSeven.x2, MultSeven.x]) (A := MultSeven.x4)
    (by simp [wf_x2, wf_x]) wf_x4 (by bm_strips CFSG.KC.BM.MultSeven.sq_x7 69)
  simpa using h

theorem e_h3 : sm MultSeven.b43q1 * sm MultSeven.h3 = 1 :=
  stripMat_mul1_one wf_b43q1 wf_h3 (by bm_strips CFSG.KC.BM.MultSeven.sq_h3 69)

theorem e_h4 : sm MultSeven.b45q1 * sm MultSeven.b45q1 = 1 :=
  stripMat_mul1_one wf_b45q1 wf_b45q1 (by bm_strips CFSG.KC.BM.MultSeven.rot_h4 69)

theorem e_xy : sm MultSeven.x * sm MultSeven.y = sm MultSeven.y * sm MultSeven.x := by
  have h := stripMat_mul_eq_of_allStrips2 (Ws := [MultSeven.y]) (Ds := [MultSeven.x])
    (by simp [wf_y]) (by simp [wf_x]) wf_x wf_y (by bm_strips2 CFSG.KC.BM.MultSeven.sq_xy 69)
  simpa using h

theorem e_act : sm MultSeven.x4 * sm MultSeven.y2 * sm MultSeven.h3 * sm MultSeven.y =
    sm MultSeven.h3 := by
  have h := stripMat_mul_of_allStrips (Ws := [MultSeven.y2, MultSeven.h3, MultSeven.y])
    (A := MultSeven.x4) (C := MultSeven.h3) (by simp [wf_y2, wf_h3, wf_y]) wf_x4
    (by bm_strips CFSG.KC.BM.MultSeven.sq_act 69)
  simpa using h

theorem e_rotx : sm MultSeven.x * sm MultSeven.h4 * sm MultSeven.x =
    sm MultSeven.y * sm MultSeven.h4 := by
  have h := stripMat_mul_eq_of_allStrips2 (Ws := [MultSeven.h4, MultSeven.x])
    (Ds := [MultSeven.h4]) (by simp [wf_h4, wf_x]) (by simp [wf_h4]) wf_x wf_y
    (by bm_strips2 CFSG.KC.BM.MultSeven.rot_x 69)
  simpa using h

theorem e_roty : sm MultSeven.x2 * sm MultSeven.h4 * sm MultSeven.y =
    sm MultSeven.y * sm MultSeven.h4 := by
  have h := stripMat_mul_eq_of_allStrips2 (Ws := [MultSeven.h4, MultSeven.y])
    (Ds := [MultSeven.h4]) (by simp [wf_h4, wf_y]) (by simp [wf_h4]) wf_x2 wf_y
    (by bm_strips2 CFSG.KC.BM.MultSeven.rot_y 69)
  simpa using h

theorem x_pow7 : sm MultSeven.x ^ 7 = 1 := by
  calc sm MultSeven.x ^ 7 = sm MultSeven.x * sm MultSeven.x * (sm MultSeven.x * sm MultSeven.x) *
        (sm MultSeven.x * sm MultSeven.x) * sm MultSeven.x := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = sm MultSeven.x4 * sm MultSeven.x2 * sm MultSeven.x := by rw [e_x2, e_x4]
    _ = 1 := e_x7

theorem h3_pow3 : sm MultSeven.h3 ^ 3 = 1 := by
  rw [pow_succ, pow_two, e_b43, e_h3]

theorem h4_pow4 : sm MultSeven.h4 ^ 4 = 1 := by
  calc sm MultSeven.h4 ^ 4 = sm MultSeven.h4 * sm MultSeven.h4 * (sm MultSeven.h4 * sm MultSeven.h4) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := by rw [e_b45, e_h4]

theorem rowList_cons (X : Nat) (Xs : List Nat) (m : Nat) :
    rowList (X :: Xs) m = (List.range' 0 m).reverse.map (rowOf X) ++ rowList Xs m := by
  have h := rowRec_eq X m m (rowList Xs m) le_rfl
  rw [Nat.sub_self] at h
  exact h

theorem mem_rowList : ∀ (Xs : List Nat) (m k t : Nat), k < Xs.length → t < m →
    rowOf (Xs.getD k 0) t ∈ rowList Xs m
  | [], _, _, _, hk, _ => absurd hk (by simp)
  | X :: Xs, m, 0, t, _, ht => by
    rw [rowList_cons, List.getD_cons_zero]
    refine List.mem_append_left _ (List.mem_map.2 ⟨t, ?_, rfl⟩)
    rw [List.mem_reverse, List.mem_range'_1]
    omega
  | X :: Xs, m, k + 1, t, hk, ht => by
    rw [rowList_cons, List.getD_cons_succ]
    exact List.mem_append_right _ (mem_rowList Xs m k t (by simpa using hk) ht)

theorem rowList_inj : ∀ (Xs : List Nat) (m : Nat), (rowList Xs m).Nodup →
    ∀ (k k' t t' : Nat), k < Xs.length → k' < Xs.length → t < m → t' < m →
      rowOf (Xs.getD k 0) t = rowOf (Xs.getD k' 0) t' → k = k' ∧ t = t'
  | [], _, _, _, _, _, _, hk, _, _, _, _ => absurd hk (by simp)
  | X :: Xs, m, hnd, k, k', t, t', hk, hk', ht, ht', he => by
    rw [rowList_cons, List.nodup_append] at hnd
    obtain ⟨h1, h2, h3⟩ := hnd
    have memA : ∀ s, s < m → rowOf X s ∈ (List.range' 0 m).reverse.map (rowOf X) := by
      intro s hs
      refine List.mem_map.2 ⟨s, ?_, rfl⟩
      rw [List.mem_reverse, List.mem_range'_1]
      omega
    match k, k' with
    | 0, 0 =>
      rw [List.getD_cons_zero] at he
      refine ⟨rfl, List.inj_on_of_nodup_map h1 ?_ ?_ he⟩ <;>
        rw [List.mem_reverse, List.mem_range'_1] <;> omega
    | 0, k' + 1 =>
      rw [List.getD_cons_zero, List.getD_cons_succ] at he
      exact absurd he (h3 _ (memA t ht) _ (mem_rowList Xs m k' t' (by simpa using hk') ht'))
    | k + 1, 0 =>
      rw [List.getD_cons_zero, List.getD_cons_succ] at he
      exact absurd he.symm (h3 _ (memA t' ht') _ (mem_rowList Xs m k t (by simpa using hk) ht))
    | k + 1, k' + 1 =>
      rw [List.getD_cons_succ, List.getD_cons_succ] at he
      obtain ⟨e1, e2⟩ := rowList_inj Xs m h2 k k' t t' (by simpa using hk) (by simpa using hk')
        ht ht' he
      exact ⟨by rw [e1], e2⟩

theorem orb_rows {V : Nat} {A : List Nat} {m₁ : Nat} (hm1 : m₁ < 64) (hA : wfMat A = true)
    (h0 : Nat.beq (rowsBlk V 0 1) 1 = true)
    (h1 : Nat.beq (rowsBlk V 1 m₁) (rowsBlk (mulS A V) 0 m₁) = true) :
    ∀ t, t ≤ m₁ → vrow (rowOf V t) = e0 ᵥ* stripMat A ^ t := by
  have h0' := Nat.eq_of_beq_eq_true h0
  have h1' := Nat.eq_of_beq_eq_true h1
  have hv0 : vrow (rowOf V 0) = e0 := by
    funext j
    rw [vrow_rowOf]
    have this : (rowsBlk V 0 1).testBit (64 * j.val + 0) = (1 : Nat).testBit (64 * j.val + 0) :=
      congrArg (fun x => Nat.testBit x (64 * j.val + 0)) h0'
    rw [testBit_rowsBlk V 0 (by norm_num) j.val 0 (by norm_num), testBit_one'] at this
    simp only [Nat.add_zero, decide_eq_true (by norm_num : 0 < 1), decide_eq_true j.isLt,
      Bool.and_true] at this
    rw [Nat.add_zero, this]
    unfold e0
    rw [Pi.single_apply, bz_decide]
    by_cases hj : j = 0
    · subst hj
      simp
    · have hj' : ¬ 64 * j.val = 0 := by
        intro e
        have hj0 : j.val = 0 := by omega
        exact hj (Fin.ext hj0)
      rw [ite_eq_right hj', ite_eq_right hj]
  have hstep : ∀ t, t < m₁ → vrow (rowOf V (t + 1)) = vrow (rowOf V t) ᵥ* stripMat A := by
    intro t ht
    rw [← mulS_rows hA V (t := t) (by omega)]
    funext j
    rw [vrow_rowOf, vrow_rowOf]
    have this : (rowsBlk V 1 m₁).testBit (64 * j.val + t) =
        (rowsBlk (mulS A V) 0 m₁).testBit (64 * j.val + t) :=
      congrArg (fun x => Nat.testBit x (64 * j.val + t)) h1'
    rw [testBit_rowsBlk V 1 hm1.le j.val t (by omega),
      testBit_rowsBlk _ 0 hm1.le j.val t (by omega)] at this
    simp only [decide_eq_true ht, decide_eq_true j.isLt, Bool.and_true, Nat.add_zero] at this
    rw [← Nat.add_assoc, this]
  intro t
  induction t with
  | zero => intro _; rw [pow_zero, Matrix.vecMul_one, hv0]
  | succ t ih =>
    intro ht
    rw [hstep t (by omega), ih (by omega), Matrix.vecMul_vecMul, pow_succ]

noncomputable abbrev Vs : List Nat := [MultSeven.V0, MultSeven.V1, MultSeven.V2, MultSeven.V3, MultSeven.V4,
  MultSeven.V5, MultSeven.V6]

theorem orb_parts : Nat.beq (rowsBlk MultSeven.V0 0 1) 1 = true ∧
    Nat.beq (rowsBlk MultSeven.V0 1 6) (rowsBlk (mulS MultSeven.x MultSeven.V0) 0 6) = true ∧
    (∀ j, j < 6 → Vs.getD (j + 1) 0 = mulS MultSeven.y (Vs.getD j 0)) ∧
    (rowList Vs 7).Nodup := by
  have h := CFSG.KC.BM.MultSeven.sq_orb
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, h0⟩, h1⟩, -⟩, e1⟩, -⟩, e2⟩, -⟩, e3⟩, -⟩, e4⟩, -⟩, e5⟩, -⟩, e6⟩,
    hd⟩ := h
  refine ⟨h0, h1, ?_, allDistinct_nodup _ hd⟩
  intro j hj
  interval_cases j
  · exact Nat.eq_of_beq_eq_true e1
  · exact Nat.eq_of_beq_eq_true e2
  · exact Nat.eq_of_beq_eq_true e3
  · exact Nat.eq_of_beq_eq_true e4
  · exact Nat.eq_of_beq_eq_true e5
  · exact Nat.eq_of_beq_eq_true e6

theorem rows : ∀ j, j < 7 → ∀ t, t < 7 →
    vrow (rowOf (Vs.getD j 0) t) = e0 ᵥ* (sm MultSeven.x ^ t * sm MultSeven.y ^ j)
  | 0, _, t, ht => by
    rw [pow_zero, mul_one]
    exact orb_rows (by norm_num) wf_x orb_parts.1 orb_parts.2.1 t (by omega)
  | j + 1, hj, t, ht => by
    rw [orb_parts.2.2.1 j (by omega), mulS_rows wf_y _ (by omega), rows j (by omega) t ht,
      Matrix.vecMul_vecMul, pow_succ, mul_assoc]

section Words

variable {G : Type*} [Group G] {X Y H K : G}

theorem hY_abs (hX : X ^ 7 = 1) (hY : Y ^ 7 = 1) (hc : X * Y = Y * X)
    (hA : X ^ 4 * Y ^ 2 * H * Y = H) : H * Y * H⁻¹ = X ^ 3 * Y ^ 5 := by
  have e1 : H * Y * H⁻¹ = (X ^ 4 * Y ^ 2)⁻¹ := by
    calc H * Y * H⁻¹ = (X ^ 4 * Y ^ 2)⁻¹ * (X ^ 4 * Y ^ 2 * H * Y) * H⁻¹ := by group
      _ = (X ^ 4 * Y ^ 2)⁻¹ := by rw [hA]; group
  rw [e1]
  refine inv_eq_of_mul_eq_one_right ?_
  have c : X ^ 3 * Y ^ 2 = Y ^ 2 * X ^ 3 := (Commute.pow_pow (hc : Commute X Y) 3 2).eq
  calc X ^ 4 * Y ^ 2 * (X ^ 3 * Y ^ 5) = X ^ 4 * (Y ^ 2 * X ^ 3) * Y ^ 5 := by
        simp only [mul_assoc]
    _ = X ^ 4 * X ^ 3 * (Y ^ 2 * Y ^ 5) := by rw [← c]; simp only [mul_assoc]
    _ = 1 := by rw [← pow_add, ← pow_add, hX, hY, one_mul]

theorem kX_abs (hX : X ^ 7 = 1) (hR : X * K * X = Y * K) : K * X * K⁻¹ = X ^ 6 * Y := by
  have e6 : X⁻¹ = X ^ 6 := (inv_eq_of_mul_eq_one_left (by rw [← pow_succ, hX]))
  calc K * X * K⁻¹ = X⁻¹ * (X * K * X) * K⁻¹ := by group
    _ = X ^ 6 * Y := by rw [hR, e6]; group

theorem kY_abs (hX : X ^ 7 = 1) (hR : X ^ 2 * K * Y = Y * K) : K * Y * K⁻¹ = X ^ 5 * Y := by
  have e5 : (X ^ 2)⁻¹ = X ^ 5 := (inv_eq_of_mul_eq_one_left (by rw [← pow_add, hX]))
  calc K * Y * K⁻¹ = (X ^ 2)⁻¹ * (X ^ 2 * K * Y) * K⁻¹ := by group
    _ = X ^ 5 * Y := by rw [hR, e5]; group

end Words

section Units

variable (S : Submonoid Mt)

theorem valInv_of_left {u : Sˣ} {A : Mt} (h : A * valHom S u = 1) : valHom S u⁻¹ = A := by
  calc valHom S u⁻¹ = A * valHom S u * valHom S u⁻¹ := by rw [h, one_mul]
    _ = A := by rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

variable {S} (hx : sm MultSeven.x ∈ S) (hh : sm MultSeven.h3 ∈ S) (hk : sm MultSeven.h4 ∈ S)

@[expose] noncomputable def uX : Sˣ := unitOf S hx (by norm_num) x_pow7

@[expose] noncomputable def uH : Sˣ := unitOf S hh (by norm_num) h3_pow3

@[expose] noncomputable def uK : Sˣ := unitOf S hk (by norm_num) h4_pow4

@[expose] noncomputable def uY : Sˣ := uH hh * uX hx * (uH hh)⁻¹

theorem vX : valHom S (uX hx) = sm MultSeven.x := valHom_unitOf S _ _ _

theorem vH : valHom S (uH hh) = sm MultSeven.h3 := valHom_unitOf S _ _ _

theorem vK : valHom S (uK hk) = sm MultSeven.h4 := valHom_unitOf S _ _ _

theorem vHi : valHom S (uH hh)⁻¹ = sm MultSeven.b43q1 :=
  valInv_of_left S (by rw [vH]; exact e_h3)

theorem vY : valHom S (uY hx hh) = sm MultSeven.y := by
  rw [uY, map_mul, map_mul, vH, vX, vHi, e_hx, e_y]

theorem X7 : uX hx ^ 7 = 1 := unitOf_pow S _ _ _

theorem Y7 : uY hx hh ^ 7 = 1 := by
  rw [uY, conj_pow, X7, mul_one, mul_inv_cancel]

theorem XY : uX hx * uY hx hh = uY hx hh * uX hx :=
  valHom_injective S (by rw [map_mul, map_mul, vX, vY, e_xy])

theorem hY : uH hh * uY hx hh * (uH hh)⁻¹ = uX hx ^ 3 * uY hx hh ^ 5 := by
  refine hY_abs (G := Sˣ) (X7 hx) (Y7 hx hh) (XY hx hh) (valHom_injective S ?_)
  have p4 : valHom S (uX hx) ^ 4 = sm MultSeven.x4 := by
    rw [vX, show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, e_x2, e_x4]
  have p2 : valHom S (uY hx hh) ^ 2 = sm MultSeven.y2 := by rw [vY, sq, e_y2]
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, p4, p2, vH, vY, e_act]

theorem kX : uK hk * uX hx * (uK hk)⁻¹ = uX hx ^ 6 * uY hx hh :=
  kX_abs (G := Sˣ) (X7 hx) (valHom_injective S (by rw [map_mul, map_mul, map_mul, vX, vK, vY, e_rotx]))

theorem kY : uK hk * uY hx hh * (uK hk)⁻¹ = uX hx ^ 5 * uY hx hh := by
  refine kY_abs (G := Sˣ) (X7 hx) (valHom_injective S ?_)
  have p2 : valHom S (uX hx) ^ 2 = sm MultSeven.x2 := by rw [vX, sq, e_x2]
  rw [map_mul, map_mul, map_mul, map_pow, p2, vK, vY, e_roty]

theorem card49 : Nat.card (Subgroup.closure ({uX hx, uY hx hh} : Set Sˣ)) = 7 ^ 2 := by
  refine card_closure_eq_sq (by norm_num) (X7 hx) (Y7 hx hh) (XY hx hh) ?_
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have h' := congrArg (fun u => e0 ᵥ* valHom S u) h
  simp only [map_mul, map_pow, vX, vY] at h'
  rw [← rows j j.isLt i i.isLt, ← rows j' j'.isLt i' i'.isLt] at h'
  obtain ⟨hj, hi⟩ := rowList_inj Vs 7 orb_parts.2.2.2 j j' i i' (by simp) (by simp) i.isLt
    i'.isLt (rowOf_inj h')
  exact Prod.ext (Fin.ext hi) (Fin.ext hj)

end Units

local notation "SB" => NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1
  NativeSporadic.BSeed2

theorem rotSevenData_of_seeds (hA1 : sm Seeds.A1 ∈ SB) (hA2 : sm Seeds.A2 ∈ SB) :
    ∃ x y h k : NativeSporadic.B, RotSevenData x y h k := by
  obtain ⟨hx, hh, hk, -⟩ := chain hA1 hA2
  exact ⟨uX hx.2, uY hx.2 hh.2, uH hh.2, uK hk.2,
    { pow_x := X7 hx.2
      comm := XY hx.2 hh.2
      card := card49 hx.2 hh.2
      hx := rfl
      hy := hY hx.2 hh.2
      kx := kX hx.2 hh.2 hk.2
      ky := kY hx.2 hh.2 hk.2 }⟩

theorem square_of_seeds (hA1 : sm Seeds.A1 ∈ SB) (hA2 : sm Seeds.A2 ∈ SB) :
    ∃ x y h : NativeSporadic.B,
      x ^ 7 = 1 ∧ y ^ 7 = 1 ∧ x * y = y * x ∧
        Nat.card (Subgroup.closure ({x, y} : Set NativeSporadic.B)) = 7 ^ 2 ∧
        h * x * h⁻¹ = x ^ 0 * y ^ 1 ∧ h * y * h⁻¹ = x ^ 3 * y ^ 5 := by
  obtain ⟨hx, hh, -⟩ := chain hA1 hA2
  exact ⟨uX hx.2, uY hx.2 hh.2, uH hh.2, X7 hx.2, Y7 hx.2 hh.2, XY hx.2 hh.2, card49 hx.2 hh.2,
    by rw [pow_zero, one_mul, pow_one]; try rfl, hY hx.2 hh.2⟩

end CFSG.KC.BM.MultSevenGlue

end
