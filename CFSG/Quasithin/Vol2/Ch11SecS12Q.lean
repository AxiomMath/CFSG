module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3F

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.SteinbergBR.BlockPar
open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

abbrev tr3 {i j : Fin 3} (hij : i ≠ j) (b : F) : SpecialLinearGroup (Fin 3) F :=
  SpecialLinearGroup.transvection hij b

theorem tr3_apply {i j : Fin 3} (hij : i ≠ j) (b : F) (k l : Fin 3) :
    ((tr3 hij b : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) k l =
      (if k = l then 1 else 0) + (if i = k ∧ j = l then b else 0) := by
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]

theorem tr3_mulVec {i j : Fin 3} (hij : i ≠ j) (b : F) (v : Fin 3 → F) :
    ((tr3 hij b : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      v + Pi.single i (b * v j) := by
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec]
  rfl

theorem single_eq_smul (i : Fin 3) (c : F) :
    (Pi.single i c : Fin 3 → F) = c • (Pi.single i 1 : Fin 3 → F) := by
  ext k
  simp [Pi.single_apply]

theorem tr3_mem_radU {W : Submodule F (Fin 3 → F)} {i j : Fin 3} (hij : i ≠ j) (b : F)
    (hi : (Pi.single i 1 : Fin 3 → F) ∈ W) (hj : ∀ w ∈ W, w j = 0) :
    tr3 hij b ∈ radU F W := by
  refine ⟨fun v => ?_, fun w hw => ?_⟩
  · show ((tr3 hij b : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ W
    rw [tr3_mulVec, add_sub_cancel_left, single_eq_smul]
    exact W.smul_mem _ hi
  · show ((tr3 hij b : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w
    rw [tr3_mulVec, hj w hw, mul_zero, Pi.single_zero, add_zero]

theorem tr3_mem_radU_zero {j : Fin 3} (hj : (0 : Fin 3) ≠ j) (b : F) :
    tr3 hj b ∈ radU F (flagSpace 3 F (((0 : Fin 2) : ℕ) + 1)) := by
  refine tr3_mem_radU hj b ?_ fun w hw => ?_
  · rw [mem_flagSpace]
    intro k hk
    have : k ≠ 0 := fun h => by subst h; simp at hk
    simp [this]
  · rw [mem_flagSpace] at hw
    refine hw j ?_
    have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h).symm
    simp only [Fin.val_zero, zero_add]
    omega

theorem tr3_mem_radU_one {i : Fin 3} (hi : i ≠ 2) (b : F) :
    tr3 hi b ∈ radU F (flagSpace 3 F (((1 : Fin 2) : ℕ) + 1)) := by
  refine tr3_mem_radU hi b ?_ fun w hw => ?_
  · rw [mem_flagSpace]
    intro k hk
    have hk2 : k = 2 := by
      have : (k : ℕ) < 3 := k.2
      ext
      simp only [Fin.val_one, Fin.isValue] at hk
      simp
      omega
    subst hk2
    simp [Ne.symm hi]
  · rw [mem_flagSpace] at hw
    exact hw 2 (by simp)

theorem radU_diag {d : ℕ} {r : SpecialLinearGroup (Fin 3) F} (hr : r ∈ radU F (flagSpace 3 F d))
    (k : Fin 3) : (r : Matrix (Fin 3) (Fin 3) F) k k = 1 := by
  obtain ⟨h1, h2⟩ := hr
  by_cases hk : (k : ℕ) < d
  · have hmem : (Pi.single k 1 : Fin 3 → F) ∈ flagSpace 3 F d := by
      rw [mem_flagSpace]
      intro l hl
      have : l ≠ k := fun h => by subst h; omega
      simp [this]
    have := congrFun (h2 _ hmem) k
    simpa [Matrix.mulVec_single_one] using this
  · have := h1 (Pi.single k 1)
    rw [mem_flagSpace] at this
    have h3 := this k (not_lt.mp hk)
    simp only [Matrix.mulVec_single_one, Pi.sub_apply, Pi.single_eq_same] at h3
    simpa [sub_eq_zero] using h3

theorem radU_row {d : ℕ} {r : SpecialLinearGroup (Fin 3) F} (hr : r ∈ radU F (flagSpace 3 F d))
    {i : Fin 3} (hi : d ≤ (i : ℕ)) (k : Fin 3) :
    (r : Matrix (Fin 3) (Fin 3) F) i k = if i = k then 1 else 0 := by
  have := hr.1 (Pi.single k 1)
  rw [mem_flagSpace] at this
  have h3 := this i hi
  simp only [Matrix.mulVec_single_one, Pi.sub_apply] at h3
  by_cases hik : i = k
  · subst hik
    simp only [↓reduceIte]
    exact radU_diag hr i
  · have h4 : (r : Matrix (Fin 3) (Fin 3) F) i k = 0 := by
      simpa [Pi.single_apply, hik] using h3
    simp [hik, h4]

theorem radU_col {d : ℕ} {r : SpecialLinearGroup (Fin 3) F} (hr : r ∈ radU F (flagSpace 3 F d))
    {k : Fin 3} (hk : (k : ℕ) < d) (i : Fin 3) :
    (r : Matrix (Fin 3) (Fin 3) F) i k = if i = k then 1 else 0 := by
  have hmem : (Pi.single k 1 : Fin 3 → F) ∈ flagSpace 3 F d := by
    rw [mem_flagSpace]
    intro l hl
    have : l ≠ k := fun h => by subst h; omega
    simp [this]
  have h5 := congrFun (hr.2 _ hmem) i
  have h6 : (r : Matrix (Fin 3) (Fin 3) F) i k = (Pi.single k 1 : Fin 3 → F) i := by
    rw [← h5, Matrix.mulVec_single_one]
    rfl
  rw [h6]
  simp [Pi.single_apply]

theorem trace_radU [CharP F 2] {d : ℕ} {r : SpecialLinearGroup (Fin 3) F}
    (hr : r ∈ radU F (flagSpace 3 F d)) : Matrix.trace (r : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [Matrix.trace_fin_three, radU_diag hr, radU_diag hr, radU_diag hr]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination h2

variable [Finite F] [CharP F 2]

theorem mem_pCoreOf_Ptheta (hF : Nat.card F = 4) {j : Fin 2} {y : PGL3 F} :
    y ∈ pCoreOf 2 (Ptheta F j) ↔ ∃ r ∈ radU F (flagSpace 3 F ((j : ℕ) + 1)),
      ProjGenLinGroup.mk (SpecialLinearGroup.toGL r) = y := by
  rw [pCoreOf_map_of_injective (thetaP F) thetaP_injective, pCoreOf_parab34 hF j]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r, hr, (thetaP_proj r).symm⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨proj 3 F r, ⟨r, hr, rfl⟩, thetaP_proj r⟩

theorem conj_radU (hF : Nat.card F = 4) {j : Fin 2} {g : GL (Fin 3) F}
    (hg : ProjGenLinGroup.mk g ∈
      Subgroup.normalizer ((pCoreOf 2 (Ptheta F j) : Subgroup (PGL3 F)) : Set (PGL3 F)))
    {u : SpecialLinearGroup (Fin 3) F} (hu : u ∈ radU F (flagSpace 3 F ((j : ℕ) + 1))) :
    ∃ r ∈ radU F (flagSpace 3 F ((j : ℕ) + 1)),
      g * SpecialLinearGroup.toGL u * g⁻¹ = SpecialLinearGroup.toGL r := by
  have hu' : ProjGenLinGroup.mk (SpecialLinearGroup.toGL u) ∈ pCoreOf 2 (Ptheta F j) :=
    (mem_pCoreOf_Ptheta hF).mpr ⟨u, hu, rfl⟩
  have h1 := (Subgroup.mem_normalizer_iff.mp hg _).mp hu'
  rw [← map_inv, ← map_mul, ← map_mul] at h1
  obtain ⟨r, hr, hre⟩ := (mem_pCoreOf_Ptheta hF).mp h1
  rw [ProjGenLinGroup.mk_eq_mk_iff] at hre
  obtain ⟨c, hc⟩ := hre
  have hc' : (r : Matrix (Fin 3) (Fin 3) F) * Matrix.scalar (Fin 3) (c : F) =
      (g : Matrix (Fin 3) (Fin 3) F) * (u : Matrix (Fin 3) (Fin 3) F) *
        ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) hc
    simpa only [Units.val_mul, GeneralLinearGroup.coe_scalar,
      SpecialLinearGroup.coe_GL_coe_matrix] using this
  have htr := congrArg Matrix.trace hc'
  have e1 : Matrix.trace ((r : Matrix (Fin 3) (Fin 3) F) * Matrix.scalar (Fin 3) (c : F)) =
      (c : F) * Matrix.trace (r : Matrix (Fin 3) (Fin 3) F) := by
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal, Matrix.trace_smul, smul_eq_mul]
  have e2 : Matrix.trace ((g : Matrix (Fin 3) (Fin 3) F) * (u : Matrix (Fin 3) (Fin 3) F) *
      ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) =
      Matrix.trace (u : Matrix (Fin 3) (Fin 3) F) := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  rw [e1, e2, trace_radU hu, trace_radU hr, mul_one] at htr
  have hc1 : c = 1 := Units.ext htr
  subst hc1
  rw [map_one, mul_one] at hc
  exact ⟨r, hr, hc.symm⟩

omit [Finite F] [CharP F 2] in
theorem mul_eq_of_conj {g : GL (Fin 3) F} {u r : SpecialLinearGroup (Fin 3) F}
    (h : g * SpecialLinearGroup.toGL u * g⁻¹ = SpecialLinearGroup.toGL r) :
    (g : Matrix (Fin 3) (Fin 3) F) * (u : Matrix (Fin 3) (Fin 3) F) =
      (r : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) := by
  have h1 := mul_inv_eq_iff_eq_mul.mp h
  have h2 := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) h1
  simpa only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix] using h2

omit [Finite F] [CharP F 2] in
theorem mulVec_single_mem {W : Submodule F (Fin 3 → F)} {g : GL (Fin 3) F}
    {r : SpecialLinearGroup (Fin 3) F} (hr : r ∈ radU F W) {i k : Fin 3} (hik : i ≠ k)
    (h : (g : Matrix (Fin 3) (Fin 3) F) *
      ((tr3 hik (1 : F) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (r : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F)) :
    (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single i 1 ∈ W := by
  have h1 := congrArg (· *ᵥ (Pi.single k 1 : Fin 3 → F)) h
  simp only [← Matrix.mulVec_mulVec] at h1
  rw [tr3_mulVec, Pi.single_eq_same, mul_one, Matrix.mulVec_add] at h1
  have h2 := hr.1 ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single k 1)
  rw [← h1, add_sub_cancel_left] at h2
  exact h2

theorem entries_of_normalizer_zero (hF : Nat.card F = 4) {g : GL (Fin 3) F}
    (hg : ProjGenLinGroup.mk g ∈
      Subgroup.normalizer ((pCoreOf 2 (Ptheta F 0) : Subgroup (PGL3 F)) : Set (PGL3 F))) :
    (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := by
  obtain ⟨r, hr, hgr⟩ := conj_radU hF hg (tr3_mem_radU_zero (by decide : (0 : Fin 3) ≠ 1) 1)
  have h1 := mulVec_single_mem hr _ (mul_eq_of_conj hgr)
  rw [mem_flagSpace] at h1
  have a1 := h1 1 (by simp)
  have a2 := h1 2 (by simp)
  simp only [Matrix.mulVec_single_one] at a1 a2
  exact ⟨a1, a2⟩

theorem entries_of_normalizer_one (hF : Nat.card F = 4) {g : GL (Fin 3) F}
    (hg : ProjGenLinGroup.mk g ∈
      Subgroup.normalizer ((pCoreOf 2 (Ptheta F 1) : Subgroup (PGL3 F)) : Set (PGL3 F))) :
    (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  obtain ⟨r, hr, hgr⟩ := conj_radU hF hg (tr3_mem_radU_one (by decide : (0 : Fin 3) ≠ 2) 1)
  obtain ⟨r', hr', hgr'⟩ := conj_radU hF hg (tr3_mem_radU_one (by decide : (1 : Fin 3) ≠ 2) 1)
  have h1 := mulVec_single_mem hr _ (mul_eq_of_conj hgr)
  have h2 := mulVec_single_mem hr' _ (mul_eq_of_conj hgr')
  rw [mem_flagSpace] at h1 h2
  have a1 := h1 2 (by simp)
  have a2 := h2 2 (by simp)
  simp only [Matrix.mulVec_single_one] at a1 a2
  exact ⟨a1, a2⟩

omit [Finite F] [CharP F 2] in
theorem tr3_mem_stabilizer {W : Submodule F (Fin 3 → F)} {i j : Fin 3} (hij : i ≠ j) (b : F)
    (h : (Pi.single i 1 : Fin 3 → F) ∈ W ∨ ∀ w ∈ W, w j = 0) : tr3 hij b ∈ stabilizer W := by
  refine mem_stabilizer_of_map_le ?_
  rintro _ ⟨w, hw, rfl⟩
  show ((tr3 hij b : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W
  rw [tr3_mulVec]
  rcases h with h | h
  · rw [single_eq_smul]
    exact W.add_mem hw (W.smul_mem _ h)
  · rw [h w hw, mul_zero, Pi.single_zero, add_zero]
    exact hw

omit [Finite F] [CharP F 2] in
theorem mk_mem_Ptheta {j : Fin 2} {T : SpecialLinearGroup (Fin 3) F}
    (hT : T ∈ stabilizer (flagSpace 3 F ((j : ℕ) + 1))) :
    ProjGenLinGroup.mk (SpecialLinearGroup.toGL T) ∈ Ptheta F j :=
  ⟨proj 3 F T, ⟨T, hT, rfl⟩, thetaP_proj T⟩

theorem comm_eq_of_mem_sc (hF : Nat.card F = 4) {j : Fin 2} {g : GL (Fin 3) F}
    (hg : ProjGenLinGroup.mk g ∈ sectionCentralizer (Ptheta F j) (pCoreOf 2 (Ptheta F j)))
    {T : SpecialLinearGroup (Fin 3) F} (hT : T ∈ stabilizer (flagSpace 3 F ((j : ℕ) + 1))) :
    ∃ r ∈ radU F (flagSpace 3 F ((j : ℕ) + 1)), ∃ c : F,
      (g : Matrix (Fin 3) (Fin 3) F) * (T : Matrix (Fin 3) (Fin 3) F) =
        c • ((r : Matrix (Fin 3) (Fin 3) F) * (T : Matrix (Fin 3) (Fin 3) F) *
          (g : Matrix (Fin 3) (Fin 3) F)) := by
  have h := hg.2.2 _ (mk_mem_Ptheta hT)
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at h
  obtain ⟨r, hr, hre⟩ := (mem_pCoreOf_Ptheta hF).mp h
  rw [ProjGenLinGroup.mk_eq_mk_iff] at hre
  obtain ⟨c, hc⟩ := hre
  have h1 : g * SpecialLinearGroup.toGL T =
      SpecialLinearGroup.toGL r * GeneralLinearGroup.scalar (Fin 3) c *
        (SpecialLinearGroup.toGL T * g) := by
    rw [hc]
    group
  have h2 := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) h1
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar,
    SpecialLinearGroup.coe_GL_coe_matrix] at h2
  refine ⟨r, hr, c, ?_⟩
  rw [h2, Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal, Matrix.smul_mul, Matrix.mul_assoc]

omit [Finite F] [CharP F 2] in
theorem g00_ne_zero {g : GL (Fin 3) F} (h10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0)
    (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) : (g : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := by
  intro h0
  have hdet : (g : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  apply hdet
  rw [Matrix.det_fin_three, h0, h10, h20]
  ring

omit [Finite F] [CharP F 2] in
theorem g22_ne_zero {g : GL (Fin 3) F} (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) : (g : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := by
  intro h2
  have hdet : (g : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  apply hdet
  rw [Matrix.det_fin_three, h2, h20, h21]
  ring

theorem block_of_mem_sc_zero (hF : Nat.card F = 4) {g : GL (Fin 3) F}
    (hg : ProjGenLinGroup.mk g ∈ sectionCentralizer (Ptheta F 0) (pCoreOf 2 (Ptheta F 0)))
    (h10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0) (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) :
    (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 1 1 = (g : Matrix (Fin 3) (Fin 3) F) 2 2 := by
  have h0 := g00_ne_zero h10 h20
  have hW : ∀ w ∈ flagSpace 3 F (((0 : Fin 2) : ℕ) + 1), ∀ k : Fin 3, k ≠ 0 → w k = 0 := by
    intro w hw k hk
    rw [mem_flagSpace] at hw
    refine hw k ?_
    have : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
    simp only [Fin.val_zero, zero_add]
    omega
  have h1r : ((0 : Fin 2) : ℕ) + 1 ≤ ((1 : Fin 3) : ℕ) := by simp
  obtain ⟨r, hr, c, hc⟩ := comm_eq_of_mem_sc hF hg
    (tr3_mem_stabilizer (by decide : (1 : Fin 3) ≠ 2) (1 : F)
      (Or.inr fun w hw => hW w hw 2 (by decide)))
  have e00 := congrFun (congrFun hc 0) 0
  have e11 := congrFun (congrFun hc 1) 1
  have e12 := congrFun (congrFun hc 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, tr3_apply, radU_row hr h1r, radU_diag hr, h10,
    h20] at e00 e11 e12
  have hc1 : c = 1 := by
    have : (c - 1) * (g : Matrix (Fin 3) (Fin 3) F) 0 0 = 0 := by linear_combination -e00
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h0)
  subst hc1
  obtain ⟨r', hr', c', hc'⟩ := comm_eq_of_mem_sc hF hg
    (tr3_mem_stabilizer (by decide : (2 : Fin 3) ≠ 1) (1 : F)
      (Or.inr fun w hw => hW w hw 1 (by decide)))
  have f00 := congrFun (congrFun hc' 0) 0
  have f11 := congrFun (congrFun hc' 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, tr3_apply, radU_row hr' h1r, radU_diag hr', h10,
    h20] at f00 f11
  have hc1' : c' = 1 := by
    have : (c' - 1) * (g : Matrix (Fin 3) (Fin 3) F) 0 0 = 0 := by linear_combination -f00
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h0)
  subst hc1'
  refine ⟨?_, ?_, ?_⟩
  · linear_combination f11
  · linear_combination -e11
  · linear_combination e12

theorem block_of_mem_sc_one (hF : Nat.card F = 4) {g : GL (Fin 3) F}
    (hg : ProjGenLinGroup.mk g ∈ sectionCentralizer (Ptheta F 1) (pCoreOf 2 (Ptheta F 1)))
    (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) (h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) :
    (g : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 0 0 = (g : Matrix (Fin 3) (Fin 3) F) 1 1 := by
  have h2 := g22_ne_zero h20 h21
  have hmem : ∀ i : Fin 3, i ≠ 2 →
      (Pi.single i 1 : Fin 3 → F) ∈ flagSpace 3 F (((1 : Fin 2) : ℕ) + 1) := by
    intro i hi
    rw [mem_flagSpace]
    intro k hk
    have hk2 : k = 2 := by
      have : (k : ℕ) < 3 := k.2
      ext
      simp only [Fin.val_one, Fin.isValue] at hk
      simp
      omega
    subst hk2
    simp [Ne.symm hi]
  have h0c : ((0 : Fin 3) : ℕ) < ((1 : Fin 2) : ℕ) + 1 := by simp
  have h1c : ((1 : Fin 3) : ℕ) < ((1 : Fin 2) : ℕ) + 1 := by simp
  have h2r : ((1 : Fin 2) : ℕ) + 1 ≤ ((2 : Fin 3) : ℕ) := by simp
  obtain ⟨r, hr, c, hc⟩ := comm_eq_of_mem_sc hF hg
    (tr3_mem_stabilizer (by decide : (0 : Fin 3) ≠ 1) (1 : F) (Or.inl (hmem 0 (by decide))))
  have e22 := congrFun (congrFun hc 2) 2
  have e11 := congrFun (congrFun hc 1) 1
  have e01 := congrFun (congrFun hc 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, tr3_apply, radU_col hr h0c, radU_col hr h1c,
    radU_row hr h2r, h21] at e22 e11 e01
  have hc1 : c = 1 := by
    have : (c - 1) * (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 0 := by linear_combination -e22
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h2)
  subst hc1
  obtain ⟨r', hr', c', hc'⟩ := comm_eq_of_mem_sc hF hg
    (tr3_mem_stabilizer (by decide : (1 : Fin 3) ≠ 0) (1 : F) (Or.inl (hmem 1 (by decide))))
  have f22 := congrFun (congrFun hc' 2) 2
  have f00 := congrFun (congrFun hc' 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three, tr3_apply, radU_col hr' h0c, radU_col hr' h1c,
    radU_row hr' h2r, h20] at f22 f00
  have hc1' : c' = 1 := by
    have : (c' - 1) * (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 0 := by linear_combination -f22
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h2)
  subst hc1'
  refine ⟨?_, ?_, ?_⟩
  · linear_combination f00
  · linear_combination e11
  · linear_combination e01

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
