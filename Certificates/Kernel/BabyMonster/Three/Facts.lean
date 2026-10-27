module

public import Certificates.Kernel.BabyMonster.Three.Glue
public import Certificates.Kernel.BabyMonster.Three.Mem
public import Certificates.Kernel.BabyMonster.Three.Regs
public import Certificates.Kernel.BabyMonster.Seeds
public import CFSG.Certificates.Kernel.BabyMonster.PairSound
public import CFSG.Monster.B.Pinned.Primes.ThreeWords
public import CFSG.Monster.B.Pinned.Primes.Data
public import CFSG.Monster.B.Cbar.SimpleBase

public section

namespace CertificateChecks.KernelBM.Three

open CFSG.KC.BM CFSG.KC.BM.Reg CFSG.KC.BM.ThreeGlue CFSG.KC.ClassTwo CFSG.SectionRank.LocalWitness
  CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Monster.B.Primes.Native CFSG.Blueprint

local notation "sm" => stripMat

local notation "SB" => NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1
  NativeSporadic.BSeed2

set_option maxRecDepth 100000

theorem seeds_mem : sm Seeds.A1 ∈ SB ∧ sm Seeds.A2 ∈ SB :=
  ⟨by rw [← KernelBM.genA₁_eq_stripMat]; exact Submonoid.subset_closure (Set.mem_insert _ _),
    by rw [← KernelBM.genA₂_eq_stripMat]; exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem gens_mem : sm Three.t79 ∈ SB ∧ sm Three.t58 ∈ SB :=
  ThreeMem.three_mem seeds_mem.1 seeds_mem.2

theorem three_bridge :
    bMat xThree = sm Three.t79 ∧ bMat hThree = sm Three.t58 := by
  have hw := pinned_B_three_primary_word_data.2.2.2.2.1 (CFSG.Monster.B.progInit bA₁ bA₂)
    (by simp [CFSG.Monster.B.progInit]) (by simp [CFSG.Monster.B.progInit])
  have hρ := three_regs bMat (CFSG.Monster.B.progInit bA₁ bA₂) ?_ ?_
  · have h0 := hρ 0 (by decide)
    have h1 := hρ 1 (by decide)
    change bMat ((threeProg ()).foldl insStepG (CFSG.Monster.B.progInit bA₁ bA₂) 1) =
      sm CFSG.KC.BM.Three.t79 at h0
    change bMat ((threeProg ()).foldl insStepG (CFSG.Monster.B.progInit bA₁ bA₂) 2) =
      sm CFSG.KC.BM.Three.t58 at h1
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

theorem xThree_eq : xThree = uT gens_mem.1 :=
  bMat_injective (three_bridge.1.trans (vT gens_mem.1).symm)

theorem hThree_eq : hThree = uH gens_mem.2 :=
  bMat_injective (three_bridge.2.trans (vH gens_mem.2).symm)

theorem qThree_eq (i : Fin 8) :
    qThree i = qq gens_mem.1 gens_mem.2 i.val := by
  fin_cases i <;>
    simp [qThree, qBaseThree, xThree_eq, hThree_eq, qq, u1, u2, u3, u4, u5, u6, u7, u8,
      mul_assoc, mul_inv_rev]

theorem zThree_eq : zThree = qq gens_mem.1 gens_mem.2 8 := by
  have e0 := qThree_eq 0
  have e1 := qThree_eq 1
  simp only [Fin.val_zero, Fin.val_one] at e0 e1
  rw [zThree, bcomm, e0, e1]
  simp only [qq, uz, mul_inv_rev, mul_assoc]

theorem bcomm_of {G : Type*} [Group G] {a b z : G} {k : ℕ} (h : a * b = b * a * z ^ k) :
    bcomm a b = z ^ k := by
  rw [bcomm, mul_assoc (a⁻¹ * b⁻¹), h]
  group

theorem conj_ne_one {G : Type*} [Group G] {a b : G} (h : b ≠ 1) : a⁻¹ * b * a ≠ 1 := by
  intro e
  apply h
  calc b = a * (a⁻¹ * b * a) * a⁻¹ := by group
    _ = 1 := by rw [e]; group

theorem x20_ne_one (t : ℕ) (h0 : 0 < t) (h40 : t < 40) :
    xThree ^ t ≠ 1 := by
  intro e
  have h := orbOK_sound (V := CFSG.KC.BM.Three.Vox) (A := CFSG.KC.BM.Three.t79) (m := 40)
    (m₁ := 39) rfl (by norm_num) CFSG.KC.BM.Three.wf_t79 CFSG.KC.BM.Three.ox_orb t h0 h40
  rw [← three_bridge.1, ← map_pow, e, map_one] at h
  exact h rfl

theorem h4_ne_one : hThree ^ 4 ≠ 1 := by
  intro e
  have h := orbOK_sound (V := CFSG.KC.BM.Three.Voh) (A := CFSG.KC.BM.Three.t58) (m := 8)
    (m₁ := 7) rfl (by norm_num) CFSG.KC.BM.Three.wf_t58 CFSG.KC.BM.Three.oh_orb 4 (by norm_num)
    (by norm_num)
  rw [← three_bridge.2, ← map_pow, e, map_one] at h
  exact h rfl

theorem act_x (i : Fin 8) : xThree⁻¹ * qThree i * xThree =
    (List.ofFn fun j => qThree j ^ (threeXRows.getD i []).getD j 0).prod *
      zThree ^ threeCVec.getD i 0 := by
  simp only [qThree_eq, zThree_eq]
  rw [xThree_eq, conjT]
  fin_cases i <;> simp [TX, ev, List.ofFn_succ, threeXRows, threeCVec, sq, mul_assoc]

theorem act_h (i : Fin 8) : hThree⁻¹ * qThree i * hThree =
    (List.ofFn fun j => qThree j ^ (threeYRows.getD i []).getD j 0).prod *
      zThree ^ threeDVec.getD i 0 := by
  simp only [qThree_eq, zThree_eq]
  rw [hThree_eq, conjH]
  fin_cases i <;> simp [TH, ev, List.ofFn_succ, threeYRows, threeDVec, sq, mul_assoc]

theorem fact3161 :
    xThree ^ 40 = 1 ∧ xThree ^ 20 ≠ 1 ∧ xThree ^ 8 ≠ 1 ∧ hThree ^ 8 = 1 ∧ hThree ^ 4 ≠ 1 ∧
      (∀ i, qThree i ^ 3 = 1 ∧ qThree i ≠ 1) ∧ zThree ^ 3 = 1 ∧ zThree ≠ 1 ∧
      (∀ i, qThree i * zThree = zThree * qThree i) ∧
      (∀ i j : Fin 8, i < j →
        bcomm (qThree i) (qThree j) = zThree ^ ((threeCommRows.getD i []).getD j 0)) ∧
      xThree⁻¹ * zThree * xThree = zThree * zThree ∧
      hThree⁻¹ * zThree * hThree = zThree * zThree ∧
      (∀ i : Fin 8, xThree⁻¹ * qThree i * xThree =
        (List.ofFn fun j => qThree j ^ (threeXRows.getD i []).getD j 0).prod *
          zThree ^ threeCVec.getD i 0) ∧
      ∀ i : Fin 8, hThree⁻¹ * qThree i * hThree =
        (List.ofFn fun j => qThree j ^ (threeYRows.getD i []).getD j 0).prod *
          zThree ^ threeDVec.getD i 0 := by
  have C := cfg gens_mem.1 gens_mem.2
  have hz1 : zThree ≠ 1 := by rw [zThree_eq]; exact uz_ne gens_mem.1 gens_mem.2
  have hq0 : qThree 0 ≠ 1 := by
    intro e
    apply hz1
    rw [zThree, e, bcomm]
    group
  refine ⟨?_, x20_ne_one 20 (by norm_num) (by norm_num), x20_ne_one 8 (by norm_num) (by norm_num),
    ?_, h4_ne_one, fun i => ⟨?_, ?_⟩, ?_, hz1, fun i => ?_, fun i j hij => ?_, ?_, ?_, act_x,
    act_h⟩
  · rw [xThree_eq]; exact unitOf_pow _ _ _ _
  · rw [hThree_eq]; exact unitOf_pow _ _ _ _
  · rw [qThree_eq]; exact C.pow i.val (by omega)
  · fin_cases i
    · exact hq0
    · exact conj_ne_one (a := xThree) hq0
    · exact conj_ne_one (a := hThree) hq0
    · exact conj_ne_one (a := xThree * xThree) hq0
    · exact conj_ne_one (a := xThree * hThree) hq0
    · exact conj_ne_one (a := hThree * xThree) hq0
    · exact conj_ne_one (a := hThree * hThree) hq0
    · exact conj_ne_one (a := xThree * xThree * xThree) hq0
  · rw [zThree_eq]; exact C.pow 8 le_rfl
  · rw [qThree_eq, zThree_eq]; exact C.cen i.val i.isLt
  · rw [qThree_eq, qThree_eq, zThree_eq]
    exact bcomm_of (C.rel i.val j.val hij j.isLt)
  · rw [xThree_eq, zThree_eq, conjT]
    simp [TX, ev]
  · rw [hThree_eq, zThree_eq, conjH]
    simp [TH, ev]

end CertificateChecks.KernelBM.Three

end
