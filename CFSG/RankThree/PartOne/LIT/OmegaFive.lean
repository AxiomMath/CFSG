module

public import CFSG.RankThree.PartOne.LIT.FiveClosure
public import CFSG.RankThree.PartOne.LIT.OrthogonalTransport

public section

namespace CFSG.RankThree.PartOne.LIT

open Matrix CFSG.RankThree.SubgroupLists
open scoped commutatorElement

theorem orthGL_mem_soGL {A : M3} (h : Aᵀ * A = 1) (hd : A.det = 1) :
    orthGL A h ∈ soGL (1 : M3) := by
  rw [mem_soGL]
  exact ⟨by simpa using h, hd⟩

theorem commutator_mem_of_index_two {G : Type*} [Group G] {K : Subgroup G} (hK : K.index = 2)
    (a b : G) : a * b * a⁻¹ * b⁻¹ ∈ K := by
  have h := fun x y : G => Subgroup.mul_mem_iff_of_index_two hK (a := x) (b := y)
  rw [h, h, h, inv_mem_iff, inv_mem_iff]
  tauto

@[expose] def x1M : M3 := !![0, 0, 1; 0, 1, 0; 4, 0, 0]

@[expose] def y1M : M3 := !![0, 0, 1; 4, 0, 0; 0, 4, 0]

@[expose] def y2M : M3 := !![1, 3, 4; 4, 1, 2; 2, 4, 4]

theorem x1M_orth : x1Mᵀ * x1M = 1 := by decide

theorem y1M_orth : y1Mᵀ * y1M = 1 := by decide

theorem y2M_orth : y2Mᵀ * y2M = 1 := by decide

theorem aM_det : aM.det = 1 := by decide

theorem x1M_det : x1M.det = 1 := by decide

theorem y1M_det : y1M.det = 1 := by decide

theorem y2M_det : y2M.det = 1 := by decide

theorem aGL_mem_soGL : aGL ∈ soGL (1 : M3) := orthGL_mem_soGL aM_orth aM_det

theorem aGL_comm :
    ⁅orthGL x1M x1M_orth, orthGL y1M y1M_orth⁆ = aGL := by
  apply Units.ext
  rw [commutatorElement_def]
  simp only [Units.val_mul, val_orthGL, val_inv_orthGL]
  show x1M * y1M * x1Mᵀ * y1Mᵀ = aM
  decide

theorem bGL_comm : ⁅aGL, orthGL y2M y2M_orth⁆ = bGL := by
  apply Units.ext
  rw [commutatorElement_def]
  simp only [Units.val_mul, val_orthGL, val_inv_orthGL]
  show aM * y2M * aMᵀ * y2Mᵀ = bM
  decide

theorem aGL_mem_omega : aGL ∈ omegaGL (1 : M3) := by
  rw [← aGL_comm]
  exact Subgroup.commutator_mem_commutator (orthGL_mem_soGL x1M_orth x1M_det)
    (orthGL_mem_soGL y1M_orth y1M_det)

theorem bGL_mem_omega : bGL ∈ omegaGL (1 : M3) := by
  rw [← bGL_comm]
  exact Subgroup.commutator_mem_commutator aGL_mem_soGL (orthGL_mem_soGL y2M_orth y2M_det)

theorem Kfive_le_omega : Kfive ≤ omegaGL (1 : M3) := by
  rw [Kfive, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact aGL_mem_omega
  · exact bGL_mem_omega

theorem omega_eq_Kfive (hcard : Nat.card (soGL (1 : M3)) = 120) : omegaGL (1 : M3) = Kfive := by
  have hKle : Kfive ≤ soGL (1 : M3) := Kfive_le_omega.trans (omegaGL_le_soGL _)
  have hidx : (Kfive.subgroupOf (soGL (1 : M3))).index = 2 := by
    have h := Subgroup.card_mul_index (Kfive.subgroupOf (soGL (1 : M3)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv, natCard_Kfive, hcard] at h
    omega
  refine le_antisymm ?_ Kfive_le_omega
  rw [omegaGL, Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  have h := commutator_mem_of_index_two hidx ⟨g₁, h₁⟩ ⟨g₂, h₂⟩
  rw [Subgroup.mem_subgroupOf] at h
  rw [commutatorElement_def]
  simpa using h

theorem natCard_omegaGL_one (hcard : Nat.card (soGL (1 : M3)) = 120) :
    Nat.card (omegaGL (1 : M3)) = 60 := by
  rw [omega_eq_Kfive hcard, natCard_Kfive]

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem scalar_records : ∀ x00 < 5, ∀ x01 < 5, ∀ x02 < 5, ∀ x11 < 5, ∀ x12 < 5, ∀ x22 < 5,
    R3.mul (R3.mul aR.transpose ⟨x00, x01, x02, x01, x11, x12, x02, x12, x22⟩) aR =
      ⟨x00, x01, x02, x01, x11, x12, x02, x12, x22⟩ →
    R3.mul (R3.mul bR.transpose ⟨x00, x01, x02, x01, x11, x12, x02, x12, x22⟩) bR =
      ⟨x00, x01, x02, x01, x11, x12, x02, x12, x22⟩ →
    x01 = 0 ∧ x02 = 0 ∧ x12 = 0 ∧ x11 = x00 ∧ x22 = x00 := by decide +kernel

theorem scalar_record (s : R3) (hn : s.Norm) (hsym : s.transpose = s)
    (ha : R3.mul (R3.mul aR.transpose s) aR = s) (hb : R3.mul (R3.mul bR.transpose s) bR = s) :
    s = ⟨s.a00, 0, 0, 0, s.a00, 0, 0, 0, s.a00⟩ := by
  obtain ⟨a00, a01, a02, a10, a11, a12, a20, a21, a22⟩ := s
  obtain ⟨n00, n01, n02, n10, n11, n12, n20, n21, n22⟩ := hn
  have h10 : a01 = a10 := congrArg R3.a10 hsym
  have h20 : a02 = a20 := congrArg R3.a20 hsym
  have h21 : a12 = a21 := congrArg R3.a21 hsym
  subst h10 h20 h21
  obtain ⟨e01, e02, e12, e11, e22⟩ := scalar_records a00 n00 a01 n01 a02 n02 a11 n11 a12 n12
    a22 n22 ha hb
  subst e01 e02 e12 e11 e22
  rfl

theorem scalar_of_invariant (S : M3) (hS : Sᵀ = S) (ha : aMᵀ * S * aM = S)
    (hb : bMᵀ * S * bM = S) : ∃ c : ZMod 5, S = c • (1 : M3) := by
  have hsym : (R3.ofM S).transpose = R3.ofM S := by
    rw [← R3.ofM_transpose, hS]
  have ha' : R3.mul (R3.mul aR.transpose (R3.ofM S)) aR = R3.ofM S := by
    have := congrArg R3.ofM ha
    rwa [R3.ofM_mul, R3.ofM_mul, R3.ofM_transpose, ofM_aM] at this
  have hb' : R3.mul (R3.mul bR.transpose (R3.ofM S)) bR = R3.ofM S := by
    have := congrArg R3.ofM hb
    rwa [R3.ofM_mul, R3.ofM_mul, R3.ofM_transpose, ofM_bM] at this
  have h := scalar_record _ (R3.norm_ofM S) hsym ha' hb'
  have hS' := congrArg R3.toM h
  rw [R3.toM_ofM] at hS'
  refine ⟨((R3.ofM S).a00 : ZMod 5), hS'.trans ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R3.toM]

@[expose] def sclGL (u : ZMod 5) (hu : u ≠ 0) : GL (Fin 3) (ZMod 5) :=
  GeneralLinearGroup.mkOfDetNeZero (u • (1 : M3)) (by simp [hu])

@[simp] theorem val_sclGL (u : ZMod 5) (hu : u ≠ 0) : (sclGL u hu : M3) = u • (1 : M3) := rfl

theorem sclGL_mem_center (u : ZMod 5) (hu : u ≠ 0) :
    sclGL u hu ∈ Subgroup.center (GL (Fin 3) (ZMod 5)) := by
  rw [Subgroup.mem_center_iff]
  intro h
  apply Units.ext
  simp [Units.val_mul]

theorem exists_unit_sq_cube : ∀ c d : ZMod 5, c ≠ 0 → d ^ 2 = c ^ 3 →
    ∃ u : ZMod 5, u ≠ 0 ∧ u ^ 2 = c ∧ u ^ 3 = d := by decide

theorem exists_center_mul_so {g : GL (Fin 3) (ZMod 5)}
    (hg : g ∈ Subgroup.normalizer (omegaGL (1 : M3) : Set (GL (Fin 3) (ZMod 5)))) :
    ∃ z ∈ Subgroup.center (GL (Fin 3) (ZMod 5)), ∃ s ∈ soGL (1 : M3), g = z * s := by
  have hnorm := Subgroup.mem_set_normalizer_iff.mp hg
  have haS : aGL ∈ soGL ((g : M3)ᵀ * 1 * (g : M3)) :=
    (mem_soGL_congr g 1 aGL).mpr (omegaGL_le_soGL _ ((hnorm aGL).mp aGL_mem_omega))
  have hbS : bGL ∈ soGL ((g : M3)ᵀ * 1 * (g : M3)) :=
    (mem_soGL_congr g 1 bGL).mpr (omegaGL_le_soGL _ ((hnorm bGL).mp bGL_mem_omega))
  set P : M3 := (g : M3) with hP
  have hSsym : (Pᵀ * 1 * P)ᵀ = Pᵀ * 1 * P := by
    simp [Matrix.transpose_mul]
  obtain ⟨c, hc⟩ := scalar_of_invariant (Pᵀ * 1 * P) hSsym (mem_soGL.mp haS).1
    (mem_soGL.mp hbS).1
  have hPP : Pᵀ * P = c • (1 : M3) := by simpa using hc
  have hdet := congrArg Matrix.det hPP
  rw [det_mul, det_transpose, Matrix.det_smul, det_one] at hdet
  have hP0 : P.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det P).mp g.isUnit).ne_zero
  have hdet' : P.det ^ 2 = c ^ 3 := by simpa [sq] using hdet
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hP0 (pow_eq_zero_iff (two_ne_zero) |>.mp (by simpa using hdet'))
  obtain ⟨u, hu0, hu2, hu3⟩ := exists_unit_sq_cube c P.det hc0 hdet'
  have hsdet : ((u⁻¹ • P : M3)).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hu0)) hP0
  refine ⟨sclGL u hu0, sclGL_mem_center u hu0, GeneralLinearGroup.mkOfDetNeZero (u⁻¹ • P) hsdet,
    ?_, ?_⟩
  · rw [mem_soGL]
    refine ⟨?_, ?_⟩
    · show (u⁻¹ • P)ᵀ * 1 * (u⁻¹ • P) = 1
      rw [Matrix.transpose_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hPP,
        smul_smul, ← hu2]
      have : u⁻¹ * u⁻¹ * u ^ 2 = 1 := by
        rw [sq, mul_assoc, ← mul_assoc u⁻¹ u u, inv_mul_cancel₀ hu0, one_mul, inv_mul_cancel₀ hu0]
      rw [this, one_smul]
    · show (u⁻¹ • P).det = 1
      rw [Matrix.det_smul, ← hu3]
      simp only [Fintype.card_fin]
      rw [← mul_pow, inv_mul_cancel₀ hu0, one_pow]
  · apply Units.ext
    show P = (u • (1 : M3)) * (u⁻¹ • P)
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hu0, one_smul]

theorem commutator_center_mul_left {G : Type*} [Group G] {z : G} (hz : z ∈ Subgroup.center G)
    (a b : G) : ⁅z * a, b⁆ = ⁅a, b⁆ := by
  have hz' : ∀ g : G, g * z = z * g := Subgroup.mem_center_iff.mp hz
  rw [commutatorElement_def, commutatorElement_def]
  calc z * a * b * (z * a)⁻¹ * b⁻¹ = (z * (a * b * a⁻¹) * z⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [← hz' (a * b * a⁻¹), mul_inv_cancel_right]

theorem commutator_center_mul_right {G : Type*} [Group G] {z : G} (hz : z ∈ Subgroup.center G)
    (a b : G) : ⁅a, z * b⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv, commutator_center_mul_left hz, commutatorElement_inv]

theorem perfect_normalizer_le (Λ : Subgroup (GL (Fin 3) (ZMod 5)))
    (hΛ : Λ ≤ Subgroup.normalizer (omegaGL (1 : M3) : Set (GL (Fin 3) (ZMod 5))))
    (hperf : Group.IsPerfect Λ) : Λ ≤ omegaGL (1 : M3) := by
  have := hperf
  calc Λ = ⁅Λ, Λ⁆ := (Subgroup.commutator_eq_self (H := Λ)).symm
    _ ≤ omegaGL (1 : M3) := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨z₁, hz₁, s₁, hs₁, rfl⟩ := exists_center_mul_so (hΛ hx)
      obtain ⟨z₂, hz₂, s₂, hs₂, rfl⟩ := exists_center_mul_so (hΛ hy)
      rw [commutator_center_mul_left hz₁, commutator_center_mul_right hz₂]
      exact Subgroup.commutator_mem_commutator hs₁ hs₂

end CFSG.RankThree.PartOne.LIT
