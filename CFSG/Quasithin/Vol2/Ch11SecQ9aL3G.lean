module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3F

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.SteinbergBR.BlockPar
  CFSG.ClassicalInvolution.ModelFacts.OddCover

variable {F : Type} [Field F] [Finite F]

theorem classify_pgl [CharP F 2] (hF : Nat.card F = 4) {P : Subgroup (PGL3 F)} (h1 : P ≠ ⊥)
    (hp : ⁅P, P⁆ = P) (hc : P ≠ ⁅(⊤ : Subgroup (PGL3 F)), (⊤ : Subgroup (PGL3 F))⁆)
    (hS : S0P F ≤ Subgroup.normalizer (P : Set (PGL3 F))) :
    P = Ptheta F 0 ∨ P = Ptheta F 1 := by
  have hle : P ≤ (thetaP F).range := by
    rw [range_thetaP_eq hF, ← hp]
    exact Subgroup.commutator_mono le_top le_top
  have hPm : (P.comap (thetaP F)).map (thetaP F) = P := Subgroup.map_comap_eq_self hle
  have hinj := Subgroup.map_injective (f := thetaP F) thetaP_injective
  have h1' : P.comap (thetaP F) ≠ ⊥ := by
    intro h
    apply h1
    rw [← hPm, h, Subgroup.map_bot]
  have hp' : ⁅P.comap (thetaP F), P.comap (thetaP F)⁆ = P.comap (thetaP F) := by
    apply hinj
    rw [Subgroup.map_commutator, hPm, hp]
  have hS' : projUnitriangular 3 F ≤
      Subgroup.normalizer ((P.comap (thetaP F)) : Set (projectiveSL 3 F)) := by
    intro u hu
    have h2 := hS ⟨u, hu, rfl⟩
    rw [← hPm] at h2
    exact (map_mem_normalizer_iff (thetaP F) thetaP_injective).mp h2
  rcases classify_std hF _ h1' hp' hS' with h | h | h
  · left
    rw [← hPm, h]
  · right
    rw [← hPm, h]
  · exfalso
    apply hc
    rw [← hPm, h, ← MonoidHom.range_eq_map, range_thetaP_eq hF]

omit [Finite F] in
theorem diag_ne_zero {g : GL (Fin 3) F} (hg : (g : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular)
    (i : Fin 3) : (g : Matrix (Fin 3) (Fin 3) F) i i ≠ 0 := by
  have hdet : (g : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  rw [Matrix.det_of_isUpperTriangular hg] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)

omit [Finite F] in
theorem mk_mem_S0P {g : GL (Fin 3) F} (hg : (g : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular)
    (h01 : (g : Matrix (Fin 3) (Fin 3) F) 0 0 = (g : Matrix (Fin 3) (Fin 3) F) 1 1)
    (h12 : (g : Matrix (Fin 3) (Fin 3) F) 1 1 = (g : Matrix (Fin 3) (Fin 3) F) 2 2) :
    ProjGenLinGroup.mk g ∈ S0P F := by
  obtain ⟨a, e0⟩ : ∃ a, (g : Matrix (Fin 3) (Fin 3) F) 0 0 = a := ⟨_, rfl⟩
  have e1 : (g : Matrix (Fin 3) (Fin 3) F) 1 1 = a := h01.symm.trans e0
  have e2 : (g : Matrix (Fin 3) (Fin 3) F) 2 2 = a := h12.symm.trans e1
  have ha0 : a ≠ 0 := e0 ▸ diag_ne_zero hg 0
  have hdet : (a⁻¹ • (g : Matrix (Fin 3) (Fin 3) F)).det = 1 := by
    rw [Matrix.det_smul, Matrix.det_of_isUpperTriangular hg, Fin.prod_univ_three,
      Fintype.card_fin, e0, e1, e2]
    field_simp
  let u : SpecialLinearGroup (Fin 3) F := ⟨a⁻¹ • (g : Matrix (Fin 3) (Fin 3) F), hdet⟩
  have hu : u ∈ unitriangular 3 F := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · change (a⁻¹ • (g : Matrix (Fin 3) (Fin 3) F)) i j = 0
      rw [Matrix.smul_apply, hg hij, smul_zero]
    · change (a⁻¹ • (g : Matrix (Fin 3) (Fin 3) F)) i i = 1
      rw [Matrix.smul_apply, smul_eq_mul]
      fin_cases i <;> simp [e0, e1, e2, ha0]
  refine ⟨proj 3 F u, ⟨u, hu, rfl⟩, ?_⟩
  rw [thetaP_proj, ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨Units.mk0 a ha0, Units.ext ?_⟩
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, SpecialLinearGroup.coe_GL_coe_matrix]
  change a⁻¹ • (g : Matrix (Fin 3) (Fin 3) F) * Matrix.scalar (Fin 3) a = g
  rw [Matrix.smul_mul, ← Matrix.scalar_commute a (fun _ => Commute.all _ _), Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul, smul_smul, inv_mul_cancel₀ ha0, one_smul]

omit [Finite F] in
theorem uSL_mem_Ptheta (j : Fin 2) (a b c : F) :
    ProjGenLinGroup.mk (SpecialLinearGroup.toGL (uSL a b c)) ∈ Ptheta F j :=
  ⟨proj 3 F (uSL a b c), ⟨_, upperTriangular_le_stabilizer_flagSpace _
    (unitriangular_le_upperTriangular 3 F (uSL_mem_unitriangular a b c)), rfl⟩, rfl⟩

omit [Finite F] in
theorem radU_zero_entries {r : SpecialLinearGroup (Fin 3) F}
    (hr : r ∈ radU F (flagSpace 3 F (((0 : Fin 2) : ℕ) + 1))) :
    (r : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 ∧ (r : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
      (r : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (r : Matrix (Fin 3) (Fin 3) F) 1 1 = 1 ∧
      (r : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 := by
  obtain ⟨h1, h2⟩ := hr
  have a := h2 (Pi.single 0 1) (by
    rw [mem_flagSpace]
    intro k hk
    fin_cases k <;> simp_all)
  have b := h1 (Pi.single 1 1)
  have c := h1 (Pi.single 2 1)
  rw [mem_flagSpace] at b c
  have b1 := b 1 (by simp)
  have c1 := c 1 (by simp)
  have a0 := congrFun a 0
  have a1 := congrFun a 1
  have a2 := congrFun a 2
  simp at a0 a1 a2 b1 c1
  exact ⟨a0, a1, a2, by linear_combination b1, c1⟩

omit [Finite F] in
theorem radU_one_entries {r : SpecialLinearGroup (Fin 3) F}
    (hr : r ∈ radU F (flagSpace 3 F (((1 : Fin 2) : ℕ) + 1))) :
    (r : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 ∧ (r : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
      (r : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (r : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 ∧
      (r : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  obtain ⟨-, h2⟩ := hr
  have a := h2 (Pi.single 0 1) (by
    rw [mem_flagSpace]
    intro k hk
    fin_cases k <;> simp_all)
  have b := h2 (Pi.single 1 1) (by
    rw [mem_flagSpace]
    intro k hk
    fin_cases k <;> simp_all)
  have a0 := congrFun a 0
  have a1 := congrFun a 1
  have a2 := congrFun a 2
  have b0 := congrFun b 0
  have b2 := congrFun b 2
  simp at a0 a1 a2 b0 b2
  exact ⟨a0, a1, a2, b0, b2⟩

theorem eq_of_mem_sc_zero [CharP F 2] (hF : Nat.card F = 4) {g : GL (Fin 3) F}
    (hg : (g : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular)
    (h : ProjGenLinGroup.mk g ∈ sectionCentralizer (Ptheta F 0) (pCoreOf 2 (Ptheta F 0))) :
    (g : Matrix (Fin 3) (Fin 3) F) 1 1 = (g : Matrix (Fin 3) (Fin 3) F) 2 2 := by
  have h2 := h.2.2 _ (uSL_mem_Ptheta 0 (0 : F) 0 1)
  rw [pCoreOf_map_of_injective (thetaP F) thetaP_injective, pCoreOf_parab34 hF 0] at h2
  obtain ⟨_, ⟨r, hr, rfl⟩, hre⟩ := h2
  rw [thetaP_proj, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
    ProjGenLinGroup.mk_eq_mk_iff] at hre
  obtain ⟨c, hc⟩ := hre
  have hc' : SpecialLinearGroup.toGL r * GeneralLinearGroup.scalar (Fin 3) c *
      SpecialLinearGroup.toGL (uSL 0 0 1) * g = g * SpecialLinearGroup.toGL (uSL 0 0 1) := by
    rw [hc]
    group
  have e := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) hc'
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, SpecialLinearGroup.coe_GL_coe_matrix,
    coe_uSL] at e
  obtain ⟨r00, r10, -, r11, r12⟩ := radU_zero_entries hr
  have g10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 := hg (by decide)
  have g20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := hg (by decide)
  have g21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := hg (by decide)
  have e00 := congrFun (congrFun e 0) 0
  have e12 := congrFun (congrFun e 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, uMat, r00, r10, r11, r12, g10, g20] at e00 e12
  have hg0 := diag_ne_zero hg 0
  have hc1 : (c : F) = 1 := by
    have : ((c : F) - 1) * (g : Matrix (Fin 3) (Fin 3) F) 0 0 = 0 := by linear_combination e00
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hg0)
  rw [hc1] at e12
  linear_combination -e12

theorem eq_of_mem_sc_one [CharP F 2] (hF : Nat.card F = 4) {g : GL (Fin 3) F}
    (hg : (g : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular)
    (h : ProjGenLinGroup.mk g ∈ sectionCentralizer (Ptheta F 1) (pCoreOf 2 (Ptheta F 1))) :
    (g : Matrix (Fin 3) (Fin 3) F) 0 0 = (g : Matrix (Fin 3) (Fin 3) F) 1 1 := by
  have h2 := h.2.2 _ (uSL_mem_Ptheta 1 (1 : F) 0 0)
  rw [pCoreOf_map_of_injective (thetaP F) thetaP_injective, pCoreOf_parab34 hF 1] at h2
  obtain ⟨_, ⟨r, hr, rfl⟩, hre⟩ := h2
  rw [thetaP_proj, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
    ProjGenLinGroup.mk_eq_mk_iff] at hre
  obtain ⟨c, hc⟩ := hre
  have hc' : SpecialLinearGroup.toGL r * GeneralLinearGroup.scalar (Fin 3) c *
      SpecialLinearGroup.toGL (uSL 1 0 0) * g = g * SpecialLinearGroup.toGL (uSL 1 0 0) := by
    rw [hc]
    group
  have e := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) hc'
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, SpecialLinearGroup.coe_GL_coe_matrix,
    coe_uSL] at e
  obtain ⟨r00, -, -, r01, -⟩ := radU_one_entries hr
  have g10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 := hg (by decide)
  have g20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 := hg (by decide)
  have g21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := hg (by decide)
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, uMat, r00, r01, g10, g20, g21] at e00 e01
  have hg0 := diag_ne_zero hg 0
  have hc1 : (c : F) = 1 := by
    have : ((c : F) - 1) * (g : Matrix (Fin 3) (Fin 3) F) 0 0 = 0 := by linear_combination e00
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hg0)
  rw [hc1] at e01
  linear_combination -e01

theorem false_of_mem_sc_both [CharP F 2] (hF : Nat.card F = 4) {x : PGL3 F}
    (hx : x ∈ Subgroup.normalizer (S0P F : Set (PGL3 F))) (hx3 : orderOf x = 3)
    (h0 : x ∈ sectionCentralizer (Ptheta F 0) (pCoreOf 2 (Ptheta F 0)))
    (h1 : x ∈ sectionCentralizer (Ptheta F 1) (pCoreOf 2 (Ptheta F 1))) : False := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective x
  have hg := isUpperTriangular_of_mem_normalizer hx
  have hS := mk_mem_S0P hg (eq_of_mem_sc_one hF hg h1) (eq_of_mem_sc_zero hF hg h0)
  have hp : IsPGroup 2 (S0P F) := (isSylowTwoOf_projU (K := F)).2.1.map (thetaP F)
  obtain ⟨k, hk⟩ := hp ⟨_, hS⟩
  have hk' : (ProjGenLinGroup.mk g) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h3 := orderOf_dvd_of_pow_eq_one hk'
  rw [hx3] at h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
