module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3

public section

namespace CFSG.Quasithin.H13.NQCat

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)
open scoped commutatorElement

section General

variable {K : Type} [Field K]

theorem exists_unit_ne_one (hK4 : ∃ s : Finset K, s.card = 4) : ∃ s : Kˣ, (s : K) ≠ 1 := by
  classical
  obtain ⟨S, hS⟩ := hK4
  have h : 0 < ((S.erase 0).erase 1).card := by
    have h1 := Finset.pred_card_le_card_erase (s := S) (a := 0)
    have h2 := Finset.pred_card_le_card_erase (s := S.erase 0) (a := 1)
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp h
  exact ⟨Units.mk0 x (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx)),
    Finset.ne_of_mem_erase hx⟩

theorem units_inv_ne_one {s : Kˣ} (hs : (s : K) ≠ 1) : ((s⁻¹ : Kˣ) : K) ≠ 1 := by
  intro h
  apply hs
  rw [← inv_inv s, Units.val_inv_eq_inv_val, h, inv_one]

theorem root_mem_commutator {G : Type*} [Group G] {H : Subgroup G} (x : K → G)
    (hmul : ∀ s t, x s * x t = x (s + t)) (d : G) (w : K) (hw : w ≠ 1)
    (hconj : ∀ t, d * x t * d⁻¹ = x (w * t)) (hdH : d ∈ H) (hxH : ∀ t, x t ∈ H) (t : K) :
    x t ∈ ⁅H, H⁆ := by
  have h0 : x 0 = 1 := by
    have h := hmul 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := x 0) (by rw [h, mul_one])
  have hinv : ∀ t, (x t)⁻¹ = x (-t) := fun t => by
    rw [inv_eq_iff_mul_eq_one, hmul, add_neg_cancel, h0]
  have h1w : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have key : ⁅x (t / (1 - w)), d⁆ = x t := by
    have e : ⁅x (t / (1 - w)), d⁆ = x (t / (1 - w)) * (d * (x (t / (1 - w)))⁻¹ * d⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e, hinv, hconj, hmul]
    congr 1
    field_simp
    ring
  rw [← key]
  exact Subgroup.commutator_mem_commutator (hxH _) hdH

theorem perfectCore_le_commutator {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    perfectCore H ≤ ⁅H, H⁆ := by
  rw [← CFSG.Quasithin.perfectCore_perfect H]
  exact Subgroup.commutator_mono (CFSG.Quasithin.perfectCore_le H)
    (CFSG.Quasithin.perfectCore_le H)

@[expose] def dg2 (s : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![(s : K), 0; 0, ((s⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

theorem dg2_inv (s : Kˣ) : (dg2 s)⁻¹ = dg2 s⁻¹ := by
  rw [inv_eq_iff_mul_eq_one]
  apply Subtype.ext
  show !![(s : K), 0; 0, ((s⁻¹ : Kˣ) : K)] * !![((s⁻¹ : Kˣ) : K), 0; 0, ((s⁻¹⁻¹ : Kˣ) : K)] = 1
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def up2 (t : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

end General

namespace SL3

variable {K : Type} [Field K]

@[expose] def tv {a b : Fin 3} (hab : a ≠ b) (t : K) : SpecialLinearGroup (Fin 3) K :=
  ⟨transvection a b t, det_transvection_of_ne a b hab t⟩

theorem coe_tv {a b : Fin 3} (hab : a ≠ b) (t : K) :
    ((tv hab t : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = transvection a b t :=
  rfl

theorem tv_mul {a b : Fin 3} (hab : a ≠ b) (s t : K) : tv hab s * tv hab t = tv hab (s + t) :=
  Subtype.ext (transvection_mul_transvection_same a b hab s t)

theorem diag_conj_transvection (v : Fin 3 → K) (hv : ∀ i, v i ≠ 0) (a b : Fin 3) (t : K) :
    diagonal v * transvection a b t * diagonal (fun i => (v i)⁻¹) =
      transvection a b (v a * t * (v b)⁻¹) := by
  ext i j
  rw [mul_diagonal, diagonal_mul, transvection, transvection, Matrix.add_apply, Matrix.add_apply,
    mul_add, add_mul]
  congr 1
  · by_cases hij : i = j
    · subst hij
      rw [one_apply_eq, mul_one, mul_inv_cancel₀ (hv i)]
    · rw [one_apply_ne hij, mul_zero, zero_mul]
  · rw [single_apply, single_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      rfl
    · rw [mul_zero, zero_mul]

@[expose] def dv (j : Fin 2) (s : Kˣ) : Fin 3 → K :=
  if j = 0 then ![1, (s : K), ((s⁻¹ : Kˣ) : K)] else ![(s : K), ((s⁻¹ : Kˣ) : K), 1]

theorem coe_embSL_dg2 (j : Fin 2) (s : Kˣ) :
    ((embSL j (dg2 s) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal (dv j s) := by
  rw [coe_embSL]
  ext a b
  fin_cases j <;> fin_cases a <;> fin_cases b <;> simp [embMat, dg2, dv]

theorem coe_embSL_dg2_inv (j : Fin 2) (s : Kˣ) :
    (((embSL j (dg2 s))⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal (fun i => (dv j s i)⁻¹) := by
  rw [← map_inv, dg2_inv, coe_embSL_dg2]
  congr 1
  funext i
  fin_cases j <;> fin_cases i <;> simp [dv]

theorem embSL_dg2_conj_tv (j : Fin 2) (s : Kˣ) {a b : Fin 3} (hab : a ≠ b) (t : K) :
    embSL j (dg2 s) * tv hab t * (embSL j (dg2 s))⁻¹ =
      tv hab (dv j s a * (dv j s b)⁻¹ * t) := by
  have hv : ∀ i, dv j s i ≠ 0 := fun i => by
    fin_cases j <;> fin_cases i <;> simp [dv]
  apply Subtype.ext
  change ((embSL j (dg2 s) : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      transvection a b t *
      (((embSL j (dg2 s))⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    transvection a b _
  rw [coe_embSL_dg2, coe_embSL_dg2_inv, diag_conj_transvection _ hv]
  ring_nf

theorem tv_mem_unitriangular {a b : Fin 3} (hab : a < b) (t : K) :
    tv hab.ne t ∈ unitriangular 3 K := by
  refine ⟨fun i k hki => ?_, fun i => ?_⟩
  · rw [coe_tv, transvection, Matrix.add_apply, one_apply_ne (ne_of_gt hki), single_apply,
      zero_add, ite_eq_right]
    rintro ⟨rfl, rfl⟩
    exact absurd (hki.trans hab) (lt_irrefl _)
  · rw [coe_tv, transvection, Matrix.add_apply, one_apply_eq, single_apply, ite_eq_right,
      add_zero]
    rintro ⟨rfl, rfl⟩
    exact absurd hab (lt_irrefl _)

theorem eq_tv_mul_of_mem_unitriangular {u : SpecialLinearGroup (Fin 3) K}
    (hu : u ∈ unitriangular 3 K) :
    u = tv (show (0 : Fin 3) ≠ 1 by decide) ((u : Matrix (Fin 3) (Fin 3) K) 0 1) *
      tv (show (0 : Fin 3) ≠ 2 by decide) ((u : Matrix (Fin 3) (Fin 3) K) 0 2 -
        (u : Matrix (Fin 3) (Fin 3) K) 0 1 * (u : Matrix (Fin 3) (Fin 3) K) 1 2) *
      tv (show (1 : Fin 3) ≠ 2 by decide) ((u : Matrix (Fin 3) (Fin 3) K) 1 2) := by
  obtain ⟨h1, h2⟩ := hu
  have e10 := h1 1 0 (by decide)
  have e20 := h1 2 0 (by decide)
  have e21 := h1 2 1 (by decide)
  have e00 := h2 0
  have e11 := h2 1
  have e22 := h2 2
  apply Subtype.ext
  change (u : Matrix (Fin 3) (Fin 3) K) = transvection 0 1 _ * transvection 0 2 _ *
    transvection 1 2 _
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [transvection, Matrix.mul_apply, Fin.sum_univ_three, single_apply, e10, e20, e21, e00,
      e11, e22]

theorem embSL_up2_zero (t : K) :
    embSL 0 (up2 t) = tv (show (1 : Fin 3) ≠ 2 by decide) t := by
  apply Subtype.ext
  change embMat 0 !![1, t; 0, 1] = transvection 1 2 t
  ext i k
  fin_cases i <;> fin_cases k <;> simp [embMat, transvection]

theorem embSL_up2_one (t : K) :
    embSL 1 (up2 t) = tv (show (0 : Fin 3) ≠ 1 by decide) t := by
  apply Subtype.ext
  change embMat 1 !![1, t; 0, 1] = transvection 0 1 t
  ext i k
  fin_cases i <;> fin_cases k <;> simp [embMat, transvection]

theorem unitriangular_le_perfectCore (hK4 : ∃ s : Finset K, s.card = 4) (j : Fin 2) :
    unitriangular 3 K ≤ perfectCore (Q3 K j) := by
  obtain ⟨s, hs1⟩ := exists_unit_ne_one hK4
  have hsi1 := units_inv_ne_one hs1
  set H := unitriangular 3 K ⊔ (embSL (K := K) j).range with hH
  have hUH : unitriangular 3 K ≤ H := le_sup_left
  have hLH : (embSL (K := K) j).range ≤ H := le_sup_right
  have hL : (embSL (K := K) j).range ≤ ⁅H, H⁆ := by
    rw [← embSL_range_perfect hK4 j]
    exact Subgroup.commutator_mono hLH hLH
  have hdH : embSL j (dg2 s) ∈ H := hLH ⟨_, rfl⟩
  have hroot : ∀ {a b : Fin 3} (hab : a < b), dv j s a * (dv j s b)⁻¹ ≠ 1 →
      ∀ t, tv hab.ne t ∈ ⁅H, H⁆ := fun hab hw =>
    root_mem_commutator (tv hab.ne) (tv_mul hab.ne) _ _ hw (embSL_dg2_conj_tv j s hab.ne) hdH
      (fun t => hUH (tv_mem_unitriangular hab t))
  have hU : unitriangular 3 K ≤ ⁅H, H⁆ := by
    intro u hu
    rw [eq_tv_mul_of_mem_unitriangular hu]
    fin_cases j
    · refine mul_mem (mul_mem (hroot (by decide) (by simpa [dv] using hsi1) _)
        (hroot (by decide) (by simpa [dv] using hs1) _)) ?_
      rw [← embSL_up2_zero]
      exact hL ⟨_, rfl⟩
    · refine mul_mem (mul_mem ?_ (hroot (by decide) (by simpa [dv] using hs1) _))
        (hroot (by decide) (by simpa [dv] using hsi1) _)
      rw [← embSL_up2_one]
      exact hL ⟨_, rfl⟩
  have hperf : ⁅H, H⁆ = H :=
    le_antisymm (CFSG.Quasithin.A3.commutator_self_le H) (sup_le hU hL)
  have hHQ : H ≤ Q3 K j := sup_le
    (fun u hu => upperTriangular_le_Q3 j (unitriangular_le_upperTriangular 3 K hu))
    (by rintro _ ⟨A, rfl⟩; exact embSL_mem_Q3 j A)
  exact hUH.trans (le_perfectCore_of_perfect hHQ hperf)

@[expose] def w2 : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

theorem reflElt_eq_embSL (j : Fin 2) : reflElt 3 K (2 - (j : ℕ)) = embSL j w2 := by
  have hj := j.isLt
  rw [reflElt_of_lt (by omega) (by omega)]
  apply Subtype.ext
  rw [coe_reflection, coe_embSL]
  ext a b
  fin_cases j <;> fin_cases a <;> fin_cases b <;> simp [reflectionMatrix, embMat, w2]

theorem perfectCore_sup_eq_top [Finite K] (hK4 : ∃ s : Finset K, s.card = 4) :
    perfectCore (Q3 K 0) ⊔ perfectCore (Q3 K 1) = ⊤ := by
  have hU : unitriangular 3 K ≤ perfectCore (Q3 K 0) ⊔ perfectCore (Q3 K 1) :=
    (unitriangular_le_perfectCore hK4 0).trans le_sup_left
  have hr : ∀ j : Fin 2, reflElt 3 K (2 - (j : ℕ)) ∈ perfectCore (Q3 K j) := fun j => by
    rw [reflElt_eq_embSL]
    exact embSL_mem_perfectCore hK4 j w2
  refine ((linear_unitriangular_overgroup_subflag_containment (n := 3) (K := K)).1 _ hU).2.mp ?_
  refine Set.eq_empty_of_forall_notMem fun i hi => ?_
  obtain ⟨hi1, hi3, hnot⟩ := hi
  apply hnot
  rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl
  · have h := hr 1
    rw [show 2 - ((1 : Fin 2) : ℕ) = 1 from rfl, reflElt_of_lt hi1 hi3] at h
    exact le_sup_right (α := Subgroup (SpecialLinearGroup (Fin 3) K)) h
  · have h := hr 0
    rw [show 2 - ((0 : Fin 2) : ℕ) = 2 from rfl, reflElt_of_lt hi1 hi3] at h
    exact le_sup_left (α := Subgroup (SpecialLinearGroup (Fin 3) K)) h

theorem not_isSolvable_perfectCore [Finite K] [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4)
    (j : Fin 2) : ¬ Group.IsSolvable (perfectCore (Q3 K j)) := by
  intro h
  have := sl2_isSimple hK4
  obtain ⟨a, b, hab⟩ := sl2_nonabelian hK4
  have hs : Group.IsSolvable (SpecialLinearGroup (Fin 2) K) :=
    Group.isSolvable_of_surjective (blk3_surjective hK4 j)
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hs a b)

theorem le_upperTriangular_of_isSolvable [Finite K] [CharP K 2]
    (hK4 : ∃ s : Finset K, s.card = 4) {A : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hU : unitriangular 3 K ≤ A) (hA : Group.IsSolvable A) : A ≤ upperTriangular 3 K := by
  have hle := ((linear_unitriangular_overgroup_subflag_containment (n := 3) (K := K)).1 A hU).1
  have hr : ∀ (j : Fin 2), reflElt 3 K (2 - (j : ℕ)) ∉ A := by
    intro j hmem
    have hH : H3 K j ≤ A :=
      sup_le hU ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.mpr hmem))
    have hpc : perfectCore (Q3 K j) ≤ A :=
      ((perfectCore_le_commutator _).trans (commutator_Q3_le j)).trans hH
    exact not_isSolvable_perfectCore hK4 j
      (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hpc)
        (Subgroup.inclusion_injective hpc))
  have hcuts : borelOvergroupCuts A = {1, 2} := by
    ext i
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hi1, hi3, -⟩
      omega
    · intro hi
      rcases hi with rfl | rfl
      · refine ⟨le_rfl, by norm_num, ?_⟩
        have := hr 1
        rwa [show 2 - ((1 : Fin 2) : ℕ) = 1 from rfl, reflElt_of_lt le_rfl (by norm_num)] at this
      · refine ⟨by norm_num, by norm_num, ?_⟩
        have := hr 0
        rwa [show 2 - ((0 : Fin 2) : ℕ) = 2 from rfl,
          reflElt_of_lt (by norm_num) (by norm_num)] at this
  rw [upperTriangular_eq_flagStabilizer]
  rw [hcuts] at hle
  exact hle

end SL3

end CFSG.Quasithin.H13.NQCat
