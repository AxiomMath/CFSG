module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TypeOne

public noncomputable section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open Matrix CFSG.ComponentClassification.CatFactsSp4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial SymplecticHigher SymplecticFlag Subgroup
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K]

private abbrev a1413StrMat (x : StatedSp 2 K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

@[expose] def a1413StrSwapMat : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

private theorem a1413StrSwapMat_transpose : (a1413StrSwapMat (K := K))ᵀ = a1413StrSwapMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a1413StrSwapMat]

private theorem a1413StrSwapMat_mul_self :
    a1413StrSwapMat (K := K) * a1413StrSwapMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a1413StrSwapMat, Matrix.mul_apply, Fin.sum_univ_two]

private theorem a1413StrSwapMat_diag2 (a b : K) :
    a1413StrSwapMat * diag2 a b * a1413StrSwapMat = diag2 b a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a1413StrSwapMat, diag2, Matrix.mul_apply, Fin.sum_univ_two]

theorem a1413StrSwapMat_symplectic :
    (kron (1 : Matrix (Fin 2) (Fin 2) K) a1413StrSwapMat)ᵀ * formJ 2 K *
        kron (1 : Matrix (Fin 2) (Fin 2) K) a1413StrSwapMat = formJ 2 K := by
  rw [kron_symplectic_iff, det_one, one_smul, a1413StrSwapMat_transpose,
    a1413StrSwapMat_mul_self]

@[expose] def a1413StrSwapSp : StatedSp 2 K :=
  toSp (kron (1 : Matrix (Fin 2) (Fin 2) K) a1413StrSwapMat)
    a1413StrSwapMat_symplectic

@[simp] private theorem a1413StrCoeSwapSp :
    (((a1413StrSwapSp (K := K) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      kron (1 : Matrix (Fin 2) (Fin 2) K) a1413StrSwapMat := rfl

private theorem a1413StrSwapSp_mul_self :
    a1413StrSwapSp (K := K) * a1413StrSwapSp = 1 := by
  apply sp_ext
  rw [Subgroup.coe_mul, Units.val_mul, a1413StrCoeSwapSp, kron_mul, Matrix.one_mul,
    a1413StrSwapMat_mul_self, kron_one_one]
  rfl

private theorem a1413StrSwapSp_inv :
    (a1413StrSwapSp (K := K))⁻¹ = a1413StrSwapSp :=
  inv_eq_of_mul_eq_one_right a1413StrSwapSp_mul_self

@[expose] def a1413StrSwapProj : StatedProj (StatedSp 2 K) := proj 2 K (a1413StrSwapSp (K := K))

private theorem a1413StrProjSwap_inv :
    (a1413StrSwapProj (K := K))⁻¹ = a1413StrSwapProj := by
  rw [a1413StrSwapProj, ← map_inv, a1413StrSwapSp_inv]

private theorem a1413StrSwapMat_blk (g h : Matrix (Fin 2) (Fin 2) K) :
    kron (1 : Matrix (Fin 2) (Fin 2) K) a1413StrSwapMat * blk g h *
        kron (1 : Matrix (Fin 2) (Fin 2) K) a1413StrSwapMat = blk h g := by
  have hk : kron (1 : Matrix (Fin 2) (Fin 2) K) a1413StrSwapMat =
      fromBlocks a1413StrSwapMat 0 0 a1413StrSwapMat := by
    simp [kron]
  rw [hk, blk, blk, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, a1413StrSwapMat_diag2]

theorem a1413StrNegOne_symplectic :
    (-1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K * (-1) = formJ 2 K := by
  rw [transpose_neg, transpose_one, neg_mul, one_mul, mul_neg, mul_one, neg_neg]

@[expose] def a1413StrNegOneSp : StatedSp 2 K :=
  toSp (-1) a1413StrNegOne_symplectic

@[simp] private theorem a1413StrCoeNegOneSp :
    (((a1413StrNegOneSp (K := K) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1 := rfl

private theorem a1413StrProjNegOneSp :
    proj 2 K (a1413StrNegOneSp (K := K)) = 1 := by
  rw [← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff]
  exact Or.inr a1413StrCoeNegOneSp

private theorem a1413StrSwapSp_mul_T1 :
    a1413StrSwapSp (K := K) * T1 K * a1413StrSwapSp =
      a1413StrNegOneSp * T1 K := by
  apply sp_ext
  rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul,
    Units.val_mul, a1413StrCoeSwapSp, coe_T1, a1413StrCoeNegOneSp, a1413StrSwapMat_blk,
    Matrix.neg_mul, Matrix.one_mul, blk_neg (1 : Matrix (Fin 2) (Fin 2) K) (-1), neg_neg]

private theorem a1413StrSwapSp_mul_blkSL
    (g h : Matrix.SpecialLinearGroup (Fin 2) K) :
    a1413StrSwapSp (K := K) * blkSL K (g, h) * a1413StrSwapSp = blkSL K (h, g) := by
  apply sp_ext
  rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul, a1413StrCoeSwapSp,
    coe_blkSL, coe_blkSL, a1413StrSwapMat_blk]

private theorem a1413StrProjSwap_mul_self :
    proj 2 K (a1413StrSwapSp (K := K)) * proj 2 K a1413StrSwapSp = 1 := by
  rw [← map_mul, a1413StrSwapSp_mul_self, map_one]

private theorem a1413StrProjSwap_mem_centralizer :
    proj 2 K (a1413StrSwapSp (K := K)) ∈
      centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K))) := by
  rw [mem_centralizer_singleton_iff]
  have hT1 : proj 2 K (a1413StrSwapSp (K := K)) * proj 2 K (T1 K) *
      proj 2 K (a1413StrSwapSp (K := K)) = proj 2 K (T1 K) := by
    calc proj 2 K a1413StrSwapSp * proj 2 K (T1 K) * proj 2 K a1413StrSwapSp
        = proj 2 K (a1413StrSwapSp * T1 K * a1413StrSwapSp) := by
          rw [← map_mul, ← map_mul]
      _ = proj 2 K (a1413StrNegOneSp * T1 K) := by rw [a1413StrSwapSp_mul_T1]
      _ = proj 2 K a1413StrNegOneSp * proj 2 K (T1 K) := by rw [map_mul]
      _ = proj 2 K (T1 K) := by rw [a1413StrProjNegOneSp, one_mul]
  calc proj 2 K a1413StrSwapSp * u1 K
      = proj 2 K a1413StrSwapSp * u1 K * 1 := by rw [mul_one]
    _ = proj 2 K a1413StrSwapSp * u1 K *
          (proj 2 K a1413StrSwapSp * proj 2 K a1413StrSwapSp) := by
          rw [a1413StrProjSwap_mul_self]
    _ = (proj 2 K a1413StrSwapSp * u1 K * proj 2 K a1413StrSwapSp) *
          proj 2 K a1413StrSwapSp := by group
    _ = u1 K * proj 2 K a1413StrSwapSp := by
          rw [show u1 K = proj 2 K (T1 K) from rfl, hT1]

private theorem a1413Str_neg_one_ne_one (h2 : (2 : K) ≠ 0) : (-1 : K) ≠ 1 := by
  intro h
  exact h2 (by linear_combination -h)

private theorem a1413StrSwap_T1_entry :
    (a1413StrMat (a1413StrSwapSp (K := K)) * a1413StrMat (T1 K)) (Sum.inl 0) (Sum.inl 1) =
      -1 := by
  unfold a1413StrMat
  rw [a1413StrCoeSwapSp, coe_T1, kron, blk, fromBlocks_multiply]
  simp [diag2, a1413StrSwapMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
    Matrix.one_apply]

private theorem a1413StrT1_swap_entry :
    (a1413StrMat (T1 K) * a1413StrMat (a1413StrSwapSp (K := K))) (Sum.inl 0) (Sum.inl 1) =
      1 := by
  unfold a1413StrMat
  rw [coe_T1, a1413StrCoeSwapSp, blk, kron, fromBlocks_multiply]
  simp [diag2, a1413StrSwapMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
    Matrix.one_apply]

private theorem a1413StrSwapSp_not_commute_T1 (h2 : (2 : K) ≠ 0) :
    a1413StrSwapSp (K := K) * T1 K ≠ T1 K * a1413StrSwapSp := by
  intro hEq
  have hmat : a1413StrMat (a1413StrSwapSp (K := K)) * a1413StrMat (T1 K) =
      a1413StrMat (T1 K) * a1413StrMat a1413StrSwapSp :=
    congrArg a1413StrMat hEq
  have hentry := congrFun (congrFun hmat (Sum.inl 0)) (Sum.inl 1)
  rw [a1413StrSwap_T1_entry, a1413StrT1_swap_entry] at hentry
  exact a1413Str_neg_one_ne_one h2 hentry

private theorem a1413StrProjSwap_notMem_X0 (h2 : (2 : K) ≠ 0) :
    proj 2 K (a1413StrSwapSp (K := K)) ∉ X0 K := by
  intro hmem
  rw [X0, Subgroup.mem_map] at hmem
  obtain ⟨A, hA, hproj⟩ := hmem
  have hcommMat : a1413StrMat A * a1413StrMat (T1 K) =
      a1413StrMat (T1 K) * a1413StrMat A :=
    congrArg a1413StrMat (mem_centralizer_singleton_iff.mp hA)
  rcases eq_or_eq_neg_of_proj_eq hproj with h | h
  · have hmat : a1413StrMat (a1413StrSwapSp (K := K)) * a1413StrMat (T1 K) =
        a1413StrMat (T1 K) * a1413StrMat a1413StrSwapSp := by
      unfold a1413StrMat at hcommMat ⊢
      rw [h, hcommMat]
    exact a1413StrSwapSp_not_commute_T1 h2 (sp_ext hmat)
  · have hmat : a1413StrMat (a1413StrSwapSp (K := K)) * a1413StrMat (T1 K) =
        a1413StrMat (T1 K) * a1413StrMat a1413StrSwapSp := by
      unfold a1413StrMat at hcommMat ⊢
      rw [h, Matrix.neg_mul, Matrix.mul_neg, hcommMat]
    exact a1413StrSwapSp_not_commute_T1 h2 (sp_ext hmat)

private theorem a1413StrSwapProj_mem_centralizer :
    a1413StrSwapProj (K := K) ∈
      centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K))) :=
  (a1413StrProjSwap_mem_centralizer (K := K))

private theorem a1413StrSwapProj_notMem_X0 (h2 : (2 : K) ≠ 0) :
    a1413StrSwapProj (K := K) ∉ X0 K :=
  (a1413StrProjSwap_notMem_X0 (K := K) h2)

private theorem a1413StrSwapProj_mul_self :
    a1413StrSwapProj (K := K) * a1413StrSwapProj = 1 :=
  (a1413StrProjSwap_mul_self (K := K))

theorem a1413StrX0_eq_sup (h2 : (2 : K) ≠ 0) : X0 K = E1 K ⊔ E2 K := by
  refine le_antisymm ?_ (sup_le (E1_le_X0 h2) (E2_le_X0 h2))
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_X0 h2 hx
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)

theorem a1413Str_eq_one_or_u1_of_central_E1 (h2 : (2 : K) ≠ 0)
    {x : StatedProj (StatedSp 2 K)} (hx : x ∈ E1 K)
    (hc : ∀ y ∈ E1 K, x * y = y * x) : x = 1 ∨ x = u1 K := by
  obtain ⟨g, rfl⟩ := mem_E1.mp hx
  have hg : g ∈ center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply injective_E1 h2
    have h1 := hc (proj 2 K (blkSL K (h, 1))) (mem_E1.mpr ⟨h, rfl⟩)
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
      mul_one] at h1
    simp only [MonoidHom.comp_apply, MonoidHom.inl_apply]
    exact h1.symm
  rcases eq_one_or_neg_of_mem_center hg with h | h
  · left
    have hg1 : g = 1 := Subtype.ext h
    rw [hg1, show ((1 : Matrix.SpecialLinearGroup (Fin 2) K),
      (1 : Matrix.SpecialLinearGroup (Fin 2) K)) = 1 from rfl, map_one, map_one]
  · right
    rw [show g = negOneSL from Subtype.ext h, u1_eq_proj_blkSL']

theorem a1413Str_eq_one_or_u1_of_central_E2 (h2 : (2 : K) ≠ 0)
    {x : StatedProj (StatedSp 2 K)} (hx : x ∈ E2 K)
    (hc : ∀ y ∈ E2 K, x * y = y * x) : x = 1 ∨ x = u1 K := by
  obtain ⟨g, rfl⟩ := mem_E2.mp hx
  have hg : g ∈ center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply injective_E2 h2
    have h1 := hc (proj 2 K (blkSL K (1, h))) (mem_E2.mpr ⟨h, rfl⟩)
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
      mul_one] at h1
    simp only [MonoidHom.comp_apply, MonoidHom.inr_apply]
    exact h1.symm
  rcases eq_one_or_neg_of_mem_center hg with h | h
  · left
    have hg1 : g = 1 := Subtype.ext h
    rw [hg1, show ((1 : Matrix.SpecialLinearGroup (Fin 2) K),
      (1 : Matrix.SpecialLinearGroup (Fin 2) K)) = 1 from rfl, map_one, map_one]
  · right
    rw [show g = negOneSL from Subtype.ext h, u1_eq_proj_blkSL]

theorem a1413Str_inter_E1_E2 (h2 : (2 : K) ≠ 0) :
    E1 K ⊓ E2 K = zpowers (u1 K) := by
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
    rcases a1413Str_eq_one_or_u1_of_central_E1 h2 hz1
      (fun y hy => (commute_E1_E2 hy hz2).symm) with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.mpr ⟨u1_mem_E1, u1_mem_E2⟩

theorem a1413StrPerfect_X0 (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    ⁅X0 K, X0 K⁆ = X0 K := by
  refine le_antisymm ?_ ?_
  · exact (Subgroup.commutator_le_sup (X0 K) (X0 K)).trans (le_of_eq (sup_idem _))
  · nth_rw 1 [a1413StrX0_eq_sup h2]
    refine sup_le ?_ ?_
    · have hperf : Group.IsPerfect (E1 K) := (isQuasisimple_E1 h2 h4).1
      have hle : ⁅E1 K, E1 K⁆ ≤ ⁅X0 K, X0 K⁆ :=
        Subgroup.commutator_mono (E1_le_X0 h2) (E1_le_X0 h2)
      rwa [Subgroup.isPerfect_iff.mp hperf] at hle
    · have hperf : Group.IsPerfect (E2 K) := (isQuasisimple_E2 h2 h4).1
      have hle : ⁅E2 K, E2 K⁆ ≤ ⁅X0 K, X0 K⁆ :=
        Subgroup.commutator_mono (E2_le_X0 h2) (E2_le_X0 h2)
      rwa [Subgroup.isPerfect_iff.mp hperf] at hle

theorem a1413StrConjSwap_E1 :
    (E1 K).map (MulAut.conj (a1413StrSwapProj (K := K))).toMonoidHom = E2 K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨g, rfl⟩ := mem_E1.mp hy
    change MulAut.conj (a1413StrSwapProj (K := K)) (proj 2 K (blkSL K (g, 1))) ∈ E2 K
    rw [MulAut.conj_apply, a1413StrProjSwap_inv]
    unfold a1413StrSwapProj
    rw [← map_mul, ← map_mul, a1413StrSwapSp_mul_blkSL]
    exact mem_E2.mpr ⟨g, rfl⟩
  · intro hx
    obtain ⟨h, rfl⟩ := mem_E2.mp hx
    refine ⟨proj 2 K (blkSL K (h, 1)), mem_E1.mpr ⟨h, rfl⟩, ?_⟩
    change MulAut.conj (a1413StrSwapProj (K := K)) (proj 2 K (blkSL K (h, 1))) =
      proj 2 K (blkSL K (1, h))
    rw [MulAut.conj_apply, a1413StrProjSwap_inv]
    unfold a1413StrSwapProj
    rw [← map_mul, ← map_mul, a1413StrSwapSp_mul_blkSL]

theorem a1413StrConjSwap_E2 :
    (E2 K).map (MulAut.conj (a1413StrSwapProj (K := K))).toMonoidHom = E1 K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨h, rfl⟩ := mem_E2.mp hy
    change MulAut.conj (a1413StrSwapProj (K := K)) (proj 2 K (blkSL K (1, h))) ∈ E1 K
    rw [MulAut.conj_apply, a1413StrProjSwap_inv]
    unfold a1413StrSwapProj
    rw [← map_mul, ← map_mul, a1413StrSwapSp_mul_blkSL]
    exact mem_E1.mpr ⟨h, rfl⟩
  · intro hx
    obtain ⟨g, rfl⟩ := mem_E1.mp hx
    refine ⟨proj 2 K (blkSL K (1, g)), mem_E2.mpr ⟨g, rfl⟩, ?_⟩
    change MulAut.conj (a1413StrSwapProj (K := K)) (proj 2 K (blkSL K (1, g))) =
      proj 2 K (blkSL K (g, 1))
    rw [MulAut.conj_apply, a1413StrProjSwap_inv]
    unfold a1413StrSwapProj
    rw [← map_mul, ← map_mul, a1413StrSwapSp_mul_blkSL]

theorem a1413StrMem_C_or (h2 : (2 : K) ≠ 0) {g : StatedProj (StatedSp 2 K)}
    (hg : g ∈ centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))) :
    g ∈ X0 K ∨ g * a1413StrSwapProj ∈ X0 K := by
  obtain ⟨A, rfl⟩ := proj_surjective g
  have hcomm : proj 2 K A * proj 2 K (T1 K) = proj 2 K (T1 K) * proj 2 K A :=
    mem_centralizer_singleton_iff.mp hg
  rw [← map_mul, ← map_mul] at hcomm
  rcases eq_or_eq_neg_of_proj_eq hcomm with h | h
  · left
    refine Subgroup.mem_map.mpr ⟨A, ?_, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (sp_ext h.symm)
  · right
    have hanti_group : a1413StrSwapSp (K := K) * T1 K =
        a1413StrNegOneSp * T1 K * a1413StrSwapSp := by
      calc a1413StrSwapSp * T1 K =
            (a1413StrSwapSp * T1 K * a1413StrSwapSp) * a1413StrSwapSp := by
              rw [mul_assoc, a1413StrSwapSp_mul_self, mul_one]
        _ = (a1413StrNegOneSp * T1 K) * a1413StrSwapSp := by rw [a1413StrSwapSp_mul_T1]
    have hanti : a1413StrMat (a1413StrSwapSp (K := K)) * a1413StrMat (T1 K) =
        -(a1413StrMat (T1 K) * a1413StrMat a1413StrSwapSp) := by
      have hg' := congrArg (fun x : StatedSp 2 K =>
        (((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)))
        hanti_group
      simp only [Subgroup.coe_mul, Units.val_mul, a1413StrCoeNegOneSp, Matrix.neg_mul,
        Matrix.one_mul] at hg'
      exact hg'
    have hAanti : a1413StrMat A * a1413StrMat (T1 K) =
        -(a1413StrMat (T1 K) * a1413StrMat A) := by
      have h' := h
      simp only [Subgroup.coe_mul, Units.val_mul, Matrix.neg_mul] at h'
      rw [h', neg_neg]
    refine Subgroup.mem_map.mpr ⟨A * a1413StrSwapSp, ?_, ?_⟩
    · refine mem_centralizer_singleton_iff.mpr (sp_ext ?_)
      change (a1413StrMat A * a1413StrMat (a1413StrSwapSp (K := K))) *
          a1413StrMat (T1 K) =
        a1413StrMat (T1 K) * (a1413StrMat A * a1413StrMat a1413StrSwapSp)
      calc (a1413StrMat A * a1413StrMat a1413StrSwapSp) * a1413StrMat (T1 K)
          = a1413StrMat A * (a1413StrMat a1413StrSwapSp * a1413StrMat (T1 K)) := by
            rw [Matrix.mul_assoc]
        _ = a1413StrMat A * (-(a1413StrMat (T1 K) * a1413StrMat a1413StrSwapSp)) := by
            rw [hanti]
        _ = -(a1413StrMat A * (a1413StrMat (T1 K) * a1413StrMat a1413StrSwapSp)) := by
            rw [Matrix.mul_neg]
        _ = -((a1413StrMat A * a1413StrMat (T1 K)) * a1413StrMat a1413StrSwapSp) := by
            rw [Matrix.mul_assoc]
        _ = -((-(a1413StrMat (T1 K) * a1413StrMat A)) * a1413StrMat a1413StrSwapSp) := by
            rw [hAanti]
        _ = a1413StrMat (T1 K) * (a1413StrMat A * a1413StrMat a1413StrSwapSp) := by
            rw [Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    · rw [map_mul, a1413StrSwapProj]

private theorem a1413StrComm_X0_left (h2 : (2 : K) ≠ 0)
    {x y : StatedProj (StatedSp 2 K)} (hx : x ∈ X0 K)
    (hy : y ∈ centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))) :
    ⁅x, y⁆ ∈ X0 K := by
  have hconj : y * x * y⁻¹ ∈ X0 K := conj_mem_map_centralizer (T1 K) hy hx
  have hconj' : y * x⁻¹ * y⁻¹ ∈ X0 K := by
    convert Subgroup.inv_mem _ hconj using 1
    group
  rw [commutatorElement_def]
  simpa only [mul_assoc] using Subgroup.mul_mem _ hx hconj'

private theorem a1413StrComm_swap_left (h2 : (2 : K) ≠ 0)
    {y : StatedProj (StatedSp 2 K)}
    (hy : y ∈ centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))) :
    ⁅(a1413StrSwapProj (K := K)), y⁆ ∈ X0 K := by
  rcases a1413StrMem_C_or h2 hy with hyX | hyX
  · have h := a1413StrComm_X0_left h2 hyX a1413StrSwapProj_mem_centralizer
    simpa only [commutatorElement_inv] using Subgroup.inv_mem _ h
  · have h_eq : y = (y * a1413StrSwapProj) * a1413StrSwapProj := by
      rw [mul_assoc, a1413StrSwapProj_mul_self, mul_one]
    rw [h_eq, commutatorElement_mul_right_eq_mul_conj]
    have h1 : ⁅(a1413StrSwapProj (K := K)), (a1413StrSwapProj (K := K))⁆ =
        (1 : StatedProj (StatedSp 2 K)) := by
      rw [commutatorElement_def]; group
    have h2' : ⁅(a1413StrSwapProj (K := K)), y * a1413StrSwapProj⁆ ∈ X0 K := by
      have h := a1413StrComm_X0_left h2 hyX a1413StrSwapProj_mem_centralizer
      simpa only [commutatorElement_inv] using Subgroup.inv_mem _ h
    rw [h1, mul_one]
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using h2'

theorem a1413StrCommutator_C_eq_X0 (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    ⁅centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K))),
      centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))⁆ = X0 K := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    rcases a1413StrMem_C_or h2 hx with hxX | hxX
    · exact a1413StrComm_X0_left h2 hxX hy
    · have h_eq : x = (x * a1413StrSwapProj) * a1413StrSwapProj := by
        rw [mul_assoc, a1413StrSwapProj_mul_self, mul_one]
      rw [h_eq, commutatorElement_mul_left_eq_conj_mul]
      have h1 : ⁅a1413StrSwapProj, y⁆ ∈ X0 K := a1413StrComm_swap_left h2 hy
      have h2' : ⁅x * a1413StrSwapProj, y⁆ ∈ X0 K :=
        a1413StrComm_X0_left h2 hxX hy
      have hconj : (x * a1413StrSwapProj) * ⁅a1413StrSwapProj, y⁆ *
          (x * a1413StrSwapProj)⁻¹ ∈ X0 K :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hxX h1) (Subgroup.inv_mem _ hxX)
      exact Subgroup.mul_mem _ hconj h2'
  · nth_rw 1 [a1413StrX0_eq_sup h2]
    refine sup_le ?_ ?_
    · have hperf : Group.IsPerfect (E1 K) := (isQuasisimple_E1 h2 h4).1
      have hle : ⁅E1 K, E1 K⁆ ≤
          ⁅centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K))),
            centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))⁆ :=
        Subgroup.commutator_mono ((E1_le_X0 h2).trans X0_le_centralizer)
          ((E1_le_X0 h2).trans X0_le_centralizer)
      rwa [Subgroup.isPerfect_iff.mp hperf] at hle
    · have hperf : Group.IsPerfect (E2 K) := (isQuasisimple_E2 h2 h4).1
      have hle : ⁅E2 K, E2 K⁆ ≤
          ⁅centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K))),
            centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))⁆ :=
        Subgroup.commutator_mono ((E2_le_X0 h2).trans X0_le_centralizer)
          ((E2_le_X0 h2).trans X0_le_centralizer)
      rwa [Subgroup.isPerfect_iff.mp hperf] at hle

theorem a1413StrRelIndex_X0_C (h2 : (2 : K) ≠ 0) :
    (X0 K).relIndex (centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and']
  refine ⟨a1413StrSwapProj, a1413StrSwapProj_mem_centralizer,
    a1413StrSwapProj_notMem_X0 h2, ?_⟩
  intro b hb
  rcases a1413StrMem_C_or h2 hb with hbX | hbX
  · exact Or.inr hbX
  · left
    have hconj : a1413StrSwapProj * (b * a1413StrSwapProj) * a1413StrSwapProj⁻¹ ∈ X0 K :=
      conj_mem_map_centralizer (T1 K) a1413StrSwapProj_mem_centralizer hbX
    have h_eq : a1413StrSwapProj * b =
        a1413StrSwapProj * (b * a1413StrSwapProj) * a1413StrSwapProj := by
      rw [mul_assoc, mul_assoc, a1413StrSwapProj_mul_self, mul_one]
    rw [h_eq]
    rwa [a1413StrProjSwap_inv] at hconj

private theorem a1413StrExistsE1NotMemE2 (h2 : (2 : K) ≠ 0) :
    ∃ e ∈ E1 K, e ∉ E2 K := by
  let g : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hg_ne_one : (g : Matrix (Fin 2) (Fin 2) K) ≠ 1 := by
    intro h
    have := congrFun (congrFun h 0) 1
    simp [g] at this
  have hg_ne_neg_one : (g : Matrix (Fin 2) (Fin 2) K) ≠ -1 := by
    intro h
    have := congrFun (congrFun h 0) 1
    simp [g] at this
  refine ⟨proj 2 K (blkSL K (g, 1)), mem_E1.mpr ⟨g, rfl⟩, ?_⟩
  intro hmem
  have hx1 : proj 2 K (blkSL K (g, 1)) ∈ E1 K := mem_E1.mpr ⟨g, rfl⟩
  have hcomm : ∀ y ∈ E1 K, proj 2 K (blkSL K (g, 1)) * y =
      y * proj 2 K (blkSL K (g, 1)) :=
    fun y hy => (commute_E1_E2 hy hmem).symm
  rcases a1413Str_eq_one_or_u1_of_central_E1 h2 hx1 hcomm with h1 | h1
  · rcases (proj_blkSL_eq_one_iff (g, 1)).mp h1 with ⟨hg, -⟩ | ⟨-, h1'⟩
    · exact hg_ne_one hg
    · exact one_ne_neg_one_mat h2 h1'
  · rw [u1_eq_proj_blkSL'] at h1
    rcases eq_or_eq_neg_of_proj_eq h1 with e | e
    · exact hg_ne_neg_one ((blk_injective _ _ _ _ e).1.symm)
    · rw [coe_blkSL, coe_blkSL] at e
      rw [blk_neg] at e
      exact one_ne_neg_one_mat h2 (blk_injective _ _ _ _ e).2

theorem a1413StrCentralizer_X0 (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    centralizer (X0 K : Set (StatedProj (StatedSp 2 K))) = zpowers (u1 K) := by
  refine le_antisymm ?_ ?_
  · intro g hg
    have hgC : g ∈ centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K))) := by
      rw [mem_centralizer_singleton_iff]
      have hu1X : u1 K ∈ X0 K := (E1_le_X0 h2) u1_mem_E1
      exact ((Subgroup.mem_centralizer_iff.mp hg) (u1 K) hu1X).symm
    rcases a1413StrMem_C_or h2 hgC with hgX | hgX
    · obtain ⟨e1, he1, e2, he2, rfl⟩ := exists_mul_of_mem_X0 h2 hgX
      have he1c : ∀ y ∈ E1 K, e1 * y = y * e1 := by
        intro y hy
        have h1 : (e1 * e2) * y = y * (e1 * e2) :=
          ((Subgroup.mem_centralizer_iff.mp hg) y (E1_le_X0 h2 hy)).symm
        have h2' : e2 * y = y * e2 := (commute_E1_E2 hy he2).symm
        have h3 : (e1 * y) * e2 = (y * e1) * e2 := by
          calc (e1 * y) * e2 = e1 * (y * e2) := by rw [mul_assoc]
            _ = e1 * (e2 * y) := by rw [h2']
            _ = (e1 * e2) * y := by rw [mul_assoc]
            _ = y * (e1 * e2) := h1
            _ = (y * e1) * e2 := by rw [mul_assoc]
        exact mul_right_cancel h3
      have he2c : ∀ y ∈ E2 K, e2 * y = y * e2 := by
        intro y hy
        have h1 : (e1 * e2) * y = y * (e1 * e2) :=
          ((Subgroup.mem_centralizer_iff.mp hg) y (E2_le_X0 h2 hy)).symm
        have h2' : e1 * y = y * e1 := commute_E1_E2 he1 hy
        have h3 : e1 * (e2 * y) = e1 * (y * e2) := by
          calc e1 * (e2 * y) = (e1 * e2) * y := by rw [mul_assoc]
            _ = y * (e1 * e2) := h1
            _ = (y * e1) * e2 := by rw [mul_assoc]
            _ = (e1 * y) * e2 := by rw [← h2']
            _ = e1 * (y * e2) := by rw [mul_assoc]
        exact mul_left_cancel h3
      have hz1 : e1 ∈ zpowers (u1 K) := by
        rcases a1413Str_eq_one_or_u1_of_central_E1 h2 he1 he1c with h | h <;> rw [h]
        · exact Subgroup.one_mem _
        · exact Subgroup.mem_zpowers _
      have hz2 : e2 ∈ zpowers (u1 K) := by
        rcases a1413Str_eq_one_or_u1_of_central_E2 h2 he2 he2c with h | h <;> rw [h]
        · exact Subgroup.one_mem _
        · exact Subgroup.mem_zpowers _
      exact Subgroup.mul_mem _ hz1 hz2
    · have hle : E1 K ≤ E2 K := by
        intro e he
        have heq : g * e * g⁻¹ = e := by
          have hcomm : e * g = g * e :=
            (Subgroup.mem_centralizer_iff.mp hg) e (E1_le_X0 h2 he)
          rw [← hcomm]; group
        have hg_eq : g = (g * a1413StrSwapProj) * a1413StrSwapProj := by
          rw [mul_assoc, a1413StrSwapProj_mul_self, mul_one]
        have haea : a1413StrSwapProj * e * a1413StrSwapProj ∈ E2 K := by
          have h : MulAut.conj (a1413StrSwapProj (K := K)) e ∈
              (E1 K).map (MulAut.conj (a1413StrSwapProj (K := K))).toMonoidHom :=
            Subgroup.mem_map.mpr ⟨e, he, rfl⟩
          rw [a1413StrConjSwap_E1] at h
          rw [MulAut.conj_apply, a1413StrProjSwap_inv] at h
          exact h
        have hxnorm : (g * a1413StrSwapProj) * (a1413StrSwapProj * e * a1413StrSwapProj) *
            (g * a1413StrSwapProj)⁻¹ ∈ E2 K :=
          conj_mem_E2 h2 hgX haea
        have heq2 : e = (g * a1413StrSwapProj) *
            (a1413StrSwapProj * e * a1413StrSwapProj) * (g * a1413StrSwapProj)⁻¹ := by
          have h1 : (g * a1413StrSwapProj) *
              (a1413StrSwapProj * e * a1413StrSwapProj) * (g * a1413StrSwapProj)⁻¹ =
              g * e * g⁻¹ := by
            rw [_root_.mul_inv_rev, a1413StrProjSwap_inv]
            rw [show (g * a1413StrSwapProj) * (a1413StrSwapProj * e * a1413StrSwapProj) *
                (a1413StrSwapProj * g⁻¹) =
                g * (a1413StrSwapProj * a1413StrSwapProj) * e *
                  (a1413StrSwapProj * a1413StrSwapProj) * g⁻¹ by group]
            rw [a1413StrSwapProj_mul_self, mul_one, mul_one]
          rw [h1]
          exact heq.symm
        rwa [heq2]
      obtain ⟨e, he1, he2⟩ := a1413StrExistsE1NotMemE2 h2
      exact absurd (hle he1) he2
  · rw [Subgroup.zpowers_le]
    refine (Subgroup.mem_centralizer_iff).mpr fun x hx => ?_
    exact mem_centralizer_singleton_iff.mp (X0_le_centralizer hx)

section Generic

variable {G : Type} [Group G]

theorem a1413StrMapCentralizerSingleton (φ : MulAut G) (b : G) :
    (centralizer ({b} : Set G)).map φ.toMonoidHom = centralizer ({φ b} : Set G) := by
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' : g * b = b * g := mem_centralizer_singleton_iff.mp hg
    exact mem_centralizer_singleton_iff.mpr (by
      show (MulEquiv.toMonoidHom φ) g * (MulEquiv.toMonoidHom φ) b =
        (MulEquiv.toMonoidHom φ) b * (MulEquiv.toMonoidHom φ) g
      rw [← MonoidHom.map_mul, ← MonoidHom.map_mul, hg'])
  · intro hh
    have hh' : h * φ b = φ b * h := mem_centralizer_singleton_iff.mp hh
    refine ⟨φ.symm h, ?_, by simp⟩
    exact mem_centralizer_singleton_iff.mpr (by
      apply φ.injective
      simpa only [map_mul, MulEquiv.apply_symm_apply] using hh')

end Generic

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
