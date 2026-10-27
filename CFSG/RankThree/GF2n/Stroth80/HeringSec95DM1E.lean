module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DM1D

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix MatrixGroups

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section Lemmas

variable {hc : Ctx M Q Z B} {t : G} {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
  {Y₁ Y₂ : Type} [AddCommGroup Y₁] [Module K Y₁] [AddCommGroup Y₂] [Module K Y₂]

@[expose] noncomputable def Setup95.swap (S : Setup95 hc t M₀ φ Y₁ Y₂) :
    Setup95 hc t M₀ φ Y₂ Y₁ where
  glob := S.glob
  hφπ := S.hφπ
  hφQ := S.hφQ
  hφQf := S.hφQf
  hWV := S.hWV
  ht := S.ht
  desc := S.desc.swap

theorem rhoM_swap (D : ModDesc95 hc t M₀ φ Y₁ Y₂) {g : G} (hg : g ∈ Rt M (LB M Q B) t) :
    rhoM D.swap g = (rhoM D g).swap := by
  rw [rhoM_of_mem D hg, rhoM_of_mem D.swap hg]
  rfl

omit [Finite K] in
theorem mat_rowcase (g h : Matrix (Fin 2) (Fin 2) K) (hg10 : g 1 0 = 0) (hg00 : g 0 0 ≠ 0)
    (hh10 : h 1 0 ≠ 0) :
    ((g 0 0 * h 1 0)⁻¹ : K) • (g * Matrix.single 0 0 1 * hᵀ -
      (g 0 0 * h 0 0) • Matrix.single 0 0 1) = Matrix.single 0 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, hg10] <;> field_simp

omit [Finite K] in
theorem mat_colcase (g h : Matrix (Fin 2) (Fin 2) K) (hh10 : h 1 0 = 0) (hg10 : g 1 0 ≠ 0)
    (hh00 : h 0 0 ≠ 0) :
    ((g 1 0 * h 0 0)⁻¹ : K) • (g * Matrix.single 0 0 1 * hᵀ -
      (g 0 0 * h 0 0) • Matrix.single 0 0 1) = Matrix.single 1 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, hh10] <;> field_simp

omit [Finite K] in
theorem mat_entry (g h : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    (g * Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : K) * hᵀ) i j = g i 0 * h j 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]

namespace Setup95

variable (S : Setup95 hc t M₀ φ Y₁ Y₂)

include S

theorem core [CharP K 2] (hq4 : 4 ≤ Nat.card K) (h34 : Stroth34Statement) {n : ℕ}
    (hs : Sec9Hyp hc n t)
    (hKgrp : ∀ m ∈ hc.CN t, (∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅m, x⁆ ∈ Z) → m ∈ LB M Q B)
    {s₂ x₀ r : G} (hs₂ : s₂ ∈ N1 hc t) (hx₀ : x₀ ∈ N1 hc t) (hrR : r ∈ Rt M (LB M Q B) t)
    (hs₂r : s₂ ∈ LB M Q (conjSubgroup r B)) {p' : M₀.E} (hp'B : p' ∈ M₀.img B) (hp'0 : p' ≠ 0)
    (hb : ∃ e ∈ V2 φ s₂, actM φ x₀ e - e = p')
    (hc₀ : ∃ e ∈ V2 φ s₂, actM φ x₀ e - e = actM φ r p')
    (hne : ∀ κ : K, actM φ r p' ≠ κ • p') :
    ∃ d ∈ N1 hc t, d ∈ LB M Q (conjSubgroup r B) ∧ ∃ e ∈ V2 φ s₂, actM φ d e ≠ e := by
  classical
  have hs₂N : s₂ ∈ hc.CN t := (Subgroup.mem_inf.mp hs₂).2
  have hx₀N : x₀ ∈ hc.CN t := (Subgroup.mem_inf.mp hx₀).2
  have hx₀L : x₀ ∈ LB M Q B := (Subgroup.mem_inf.mp hx₀).1
  have hs₂H : s₂ ∈ H0 M Z := hc.Rt_le_H0 t (sec9_CN_le_Rt hc t hs₂N)
  have hss : s₂ * s₂ ∈ Q := by
    have := hc.sq_mem_Q_of_mem_LB (Subgroup.mem_inf.mp hs₂).1
    rwa [pow_two] at this
  have hrH := hc.Rt_le_H0 t hrR
  have hKS : ∀ m ∈ hc.CN t, S.theta m = 0 → m ∈ LB M Q B := fun m hm h0 =>
    hKgrp m hm ((S.theta_eq_zero_iff hm).mp h0)
  have hKS' : ∀ m ∈ hc.CN t, S.swap.theta m = 0 → m ∈ LB M Q B := fun m hm h0 =>
    hKgrp m hm ((S.swap.theta_eq_zero_iff hm).mp h0)
  obtain ⟨p, hp0, hBp, hcp⟩ := S.desc.point
  have hpB : p ∈ M₀.img B := (hBp p).mpr ⟨1, (one_smul K p).symm⟩
  have hpV : p ∈ M₀.img (Vt M (LB M Q B) B Z t) := M₀.img_mono (hc.B_le_Vt S.ht) hpB
  obtain ⟨lam, hlam⟩ := (hBp p').mp hp'B
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    exact hp'0 (by rw [hlam, zero_smul])
  obtain ⟨e_b', he_b', hEb'⟩ := hb
  obtain ⟨e_c', he_c', hEc'⟩ := hc₀
  have hEb : actM φ x₀ (lam⁻¹ • e_b') - lam⁻¹ • e_b' = p := by
    have : actM φ x₀ (lam⁻¹ • e_b') - lam⁻¹ • e_b' = lam⁻¹ • (actM φ x₀ e_b' - e_b') := by
      rw [map_smul, smul_sub]
    rw [this, hEb', hlam, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
  have hEc : actM φ x₀ (lam⁻¹ • e_c') - lam⁻¹ • e_c' = actM φ r p := by
    have : actM φ x₀ (lam⁻¹ • e_c') - lam⁻¹ • e_c' = lam⁻¹ • (actM φ x₀ e_c' - e_c') := by
      rw [map_smul, smul_sub]
    rw [this, hEc', hlam, map_smul, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
  have hV2 : ∀ e ∈ V2 φ s₂, lam⁻¹ • e ∈ V2 φ s₂ := fun e he => (V2 φ s₂).smul_mem _ he
  set e_b := lam⁻¹ • e_b' with he_bdef
  set e_c := lam⁻¹ • e_c' with he_cdef
  have he_bV := hV2 _ he_b'
  have he_cV := hV2 _ he_c'
  have hne' : ∀ κ : K, actM φ r p ≠ κ • p := by
    intro κ hκ
    apply hne (κ)
    rw [hlam, map_smul, hκ, smul_smul, smul_smul, mul_comm]
  have hcvr := S.desc.cV_act ⟨r, hrR⟩ p hpV
  have hrp : S.desc.cV (actM φ r p) = ((rhoM S.desc r).1 : Matrix (Fin 2) (Fin 2) K) *
      Matrix.single 0 0 1 * ((rhoM S.desc r).2 : Matrix (Fin 2) (Fin 2) K)ᵀ := by
    rw [actM_of_mem hrH]
    have h1 : S.desc.cV (φ ⟨r, hrH⟩ p) = ((S.desc.ρ ⟨r, hrR⟩).1 : Matrix (Fin 2) (Fin 2) K) *
        S.desc.cV p * ((S.desc.ρ ⟨r, hrR⟩).2 : Matrix (Fin 2) (Fin 2) K)ᵀ := hcvr
    rw [h1, hcp, rhoM_of_mem S.desc hrR]
  set g : Matrix (Fin 2) (Fin 2) K := ((rhoM S.desc r).1 : Matrix (Fin 2) (Fin 2) K) with hgdef
  set h : Matrix (Fin 2) (Fin 2) K := ((rhoM S.desc r).2 : Matrix (Fin 2) (Fin 2) K) with hhdef
  have hdg : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := (rhoM S.desc r).1.det_coe
    rwa [Matrix.det_fin_two] at this
  have hdh : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    have := (rhoM S.desc r).2.det_coe
    rwa [Matrix.det_fin_two] at this
  have hB : ∀ (s s' : K) (y : M1.Wd K Y₁ Y₂), S.theta x₀ (M1.actW (M1.uMat s) (M1.uMat s') y) =
      M1.uMat s * S.theta x₀ y * (M1.uMat s')ᵀ :=
    fun s s' y => S.theta_comm_LB h34 hs hx₀N hx₀L s s' y
  have h11 : g 1 0 * h 1 0 = 0 := by
    have h1 := M1.eqv_second_11 (S.theta x₀) hB (S.desc.cW e_c)
    rw [S.theta_apply hx₀N (S.V2_le_W hs₂N hss he_cV), hEc, hrp, mat_entry] at h1
    exact h1
  have hmem_cV : ∀ κ : K, κ • p ∈ M₀.img (Vt M (LB M Q B) B Z t) := fun κ =>
    hc.smul_mem_img_Vt S.glob t κ hpV
  by_cases hg10 : g 1 0 = 0
  ·
    have hg00 : g 0 0 ≠ 0 := by
      intro h0
      rw [h0, hg10] at hdg
      simp at hdg
    have hh10 : h 1 0 ≠ 0 := by
      intro h0
      apply hne' (g 0 0 * h 0 0)
      have hcvE : S.desc.cV (actM φ r p) = S.desc.cV ((g 0 0 * h 0 0) • p) := by
        rw [hrp, map_smul, hcp]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [mat_entry, Matrix.single_apply, hg10, h0]
      have hmem : actM φ r p - (g 0 0 * h 0 0) • p ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
        (M₀.img (Vt M (LB M Q B) B Z t)).sub_mem (S.actM_mem_V hrR hpV) (hmem_cV _)
      exact sub_eq_zero.mp (S.desc.cV_inj _ hmem (by rw [map_sub, hcvE, sub_self]))
    have hP : ∃ e ∈ V2 φ s₂, S.desc.cV (actM φ x₀ e - e) = Matrix.single 0 1 1 := by
      refine ⟨((g 0 0 * h 1 0)⁻¹ : K) • (e_c - (g 0 0 * h 0 0) • e_b),
        (V2 φ s₂).smul_mem _ ((V2 φ s₂).sub_mem he_cV ((V2 φ s₂).smul_mem _ he_bV)), ?_⟩
      have e1 : actM φ x₀ (((g 0 0 * h 1 0)⁻¹ : K) • (e_c - (g 0 0 * h 0 0) • e_b)) -
          ((g 0 0 * h 1 0)⁻¹ : K) • (e_c - (g 0 0 * h 0 0) • e_b) =
          ((g 0 0 * h 1 0)⁻¹ : K) • ((actM φ x₀ e_c - e_c) -
            (g 0 0 * h 0 0) • (actM φ x₀ e_b - e_b)) := by
        simp only [map_smul, map_sub, smul_sub]
        abel
      rw [e1, hEc, hEb, map_smul, map_sub, map_smul, hrp, hcp]
      exact mat_rowcase g h hg10 hg00 hh10
    exact S.core_A hq4 h34 hs hKS hs₂ hx₀ hrR hs₂r hg10 hh10 hP
  ·
    have hh10 : h 1 0 = 0 := (mul_eq_zero.mp h11).resolve_left hg10
    have hh00 : h 0 0 ≠ 0 := by
      intro h0
      rw [h0, hh10] at hdh
      simp at hdh
    have hrs : ∀ g' : G, g' ∈ Rt M (LB M Q B) t → rhoM S.swap.desc g' = (rhoM S.desc g').swap :=
      fun g' hg' => rhoM_swap S.desc hg'
    have hP : ∃ e ∈ V2 φ s₂, S.swap.desc.cV (actM φ x₀ e - e) = Matrix.single 0 1 1 := by
      refine ⟨((g 1 0 * h 0 0)⁻¹ : K) • (e_c - (g 0 0 * h 0 0) • e_b),
        (V2 φ s₂).smul_mem _ ((V2 φ s₂).sub_mem he_cV ((V2 φ s₂).smul_mem _ he_bV)), ?_⟩
      have e1 : actM φ x₀ (((g 1 0 * h 0 0)⁻¹ : K) • (e_c - (g 0 0 * h 0 0) • e_b)) -
          ((g 1 0 * h 0 0)⁻¹ : K) • (e_c - (g 0 0 * h 0 0) • e_b) =
          ((g 1 0 * h 0 0)⁻¹ : K) • ((actM φ x₀ e_c - e_c) -
            (g 0 0 * h 0 0) • (actM φ x₀ e_b - e_b)) := by
        simp only [map_smul, map_sub, smul_sub]
        abel
      have e2 : S.swap.desc.cV (actM φ x₀ (((g 1 0 * h 0 0)⁻¹ : K) • (e_c - (g 0 0 * h 0 0) • e_b))
          - ((g 1 0 * h 0 0)⁻¹ : K) • (e_c - (g 0 0 * h 0 0) • e_b)) =
          (S.desc.cV (actM φ x₀ (((g 1 0 * h 0 0)⁻¹ : K) • (e_c - (g 0 0 * h 0 0) • e_b))
          - ((g 1 0 * h 0 0)⁻¹ : K) • (e_c - (g 0 0 * h 0 0) • e_b)))ᵀ := rfl
      rw [e2, e1, hEc, hEb, map_smul, map_sub, map_smul, hrp, hcp, mat_colcase g h hh10 hg10 hh00]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]
    have hρs := hrs r hrR
    have hg10' : ((rhoM S.swap.desc r).1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
      rw [hρs]
      exact hh10
    have hh10' : ((rhoM S.swap.desc r).2 : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
      rw [hρs]
      exact hg10
    exact S.swap.core_A hq4 h34 hs hKS' hs₂ hx₀ hrR hs₂r hg10' hh10' hP

end Setup95

end Lemmas

end HS9

end CFSG.RankThree.GF2n.Stroth80
