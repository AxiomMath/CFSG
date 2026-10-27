module

public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieFrame
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieTorus
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieFix
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieQ3
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieAbs

public section

namespace CFSG.Quasithin.H13.F431.L3.P3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.QuasithinUnique.Fin257
  CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.LocalAnalysis.ComponentInitial.LinearCover CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem det_V2 {M : Matrix.SpecialLinearGroup (Fin 3) F}
    (h20 : M.1 2 0 = 0) (h21 : M.1 2 1 = 0) :
    M.1 2 2 * (M.1 0 0 *
      M.1 1 1 - M.1 0 1 *
      M.1 1 0) = 1 := by
  have := M.2
  rw [Matrix.det_fin_three] at this
  rw [h20, h21] at this
  linear_combination this

omit [CharP F 2] in
theorem mat_V2_w {M : Matrix.SpecialLinearGroup (Fin 3) F}
    (h20 : M.1 2 0 = 0) (h21 : M.1 2 1 = 0)
    (c : F) :
    M * wMat c = yMat ((M.1 0 0 * M.1 1 1 -
        M.1 0 1 * M.1 1 0) *
        M.1 1 0 * c) *
      wMat ((M.1 0 0 * M.1 1 1 -
        M.1 0 1 * M.1 1 0) *
        M.1 0 0 * c) * M := by
  have hd := det_V2 h20 h21
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  change M.1 * wM c = (yM _ * wM _) * M.1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wM, yM, Matrix.mul_apply, Fin.sum_univ_three, h20, h21]
  · linear_combination (-(M.1 0 0 * c)) * hd
  · linear_combination (-(M.1 1 0 * c)) * hd

omit [CharP F 2] in
theorem mat_V2_y {M : Matrix.SpecialLinearGroup (Fin 3) F}
    (h20 : M.1 2 0 = 0) (h21 : M.1 2 1 = 0)
    (b : F) :
    M * yMat b = yMat ((M.1 0 0 * M.1 1 1 -
        M.1 0 1 * M.1 1 0) *
        M.1 1 1 * b) *
      wMat ((M.1 0 0 * M.1 1 1 -
        M.1 0 1 * M.1 1 0) *
        M.1 0 1 * b) * M := by
  have hd := det_V2 h20 h21
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  change M.1 * yM b = (yM _ * wM _) * M.1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wM, yM, Matrix.mul_apply, Fin.sum_univ_three, h20, h21]
  · linear_combination (-(M.1 0 1 * b)) * hd
  · linear_combination (-(M.1 1 1 * b)) * hd

omit [CharP F 2] in
theorem yP_wP_inj {b c b' c' : F} (h : yP b * wP c = yP b' * wP c') : b = b' ∧ c = c' := by
  have h1 : yP b * wP c = wP c * xP 0 * yP b := by rw [xP_zero, mul_one, wP_mul_yP]
  have h2 : yP b' * wP c' = wP c' * xP 0 * yP b' := by rw [xP_zero, mul_one, wP_mul_yP]
  rw [h1, h2] at h
  obtain ⟨hc, -, hb⟩ := U_ext h
  exact ⟨hb, hc⟩

omit [CharP F 2] in
theorem conj_yP_Q3 {M : Matrix.SpecialLinearGroup (Fin 3) F} (hM : M ∈ Q3 F 1) (b : F) :
    proj 3 F M * yP b * (proj 3 F M)⁻¹ =
      yP ((M.1 0 0 * M.1 1 1 -
        M.1 0 1 * M.1 1 0) *
        M.1 1 1 * b) *
      wP ((M.1 0 0 * M.1 1 1 -
        M.1 0 1 * M.1 1 0) *
        M.1 0 1 * b) := by
  obtain ⟨h20, h21⟩ := mem_Q3_one_iff.mp hM
  have hy := congrArg (proj 3 F) (mat_V2_y h20 h21 b)
  rw [map_mul, map_mul, map_mul] at hy
  have : proj 3 F M * yP b = (yP ((M.1 0 0 *
        M.1 1 1 - M.1 0 1 *
        M.1 1 0) * M.1 1 1 * b) *
      wP ((M.1 0 0 * M.1 1 1 -
        M.1 0 1 * M.1 1 0) *
        M.1 0 1 * b)) * proj 3 F M := hy
  rw [this]; group

omit [CharP F 2] in
theorem conj_wP_Q3' {M : Matrix.SpecialLinearGroup (Fin 3) F} (hM : M ∈ Q3 F 1) (c : F) :
    proj 3 F M * wP c * (proj 3 F M)⁻¹ =
      yP ((M.1 0 0 * M.1 1 1 -
        M.1 0 1 * M.1 1 0) *
        M.1 1 0 * c) *
      wP ((M.1 0 0 * M.1 1 1 -
        M.1 0 1 * M.1 1 0) *
        M.1 0 0 * c) := by
  obtain ⟨h20, h21⟩ := mem_Q3_one_iff.mp hM
  have hw := congrArg (proj 3 F) (mat_V2_w h20 h21 c)
  rw [map_mul, map_mul, map_mul] at hw
  have : proj 3 F M * wP c = (yP ((M.1 0 0 *
        M.1 1 1 - M.1 0 1 *
        M.1 1 0) * M.1 1 0 * c) *
      wP ((M.1 0 0 * M.1 1 1 -
        M.1 0 1 * M.1 1 0) *
        M.1 0 0 * c)) * proj 3 F M := hw
  rw [this]; group

theorem projQ3_conj_V2 [Finite F] {M : Matrix.SpecialLinearGroup (Fin 3) F} (hM : M ∈ Q3 F 1)
    {v : projectiveSL 3 F} (hv : v ∈ (V2 : Subgroup (projectiveSL 3 F))) :
    proj 3 F M * v * (proj 3 F M)⁻¹ ∈ (V2 : Subgroup (projectiveSL 3 F)) := by
  obtain ⟨b, c, rfl⟩ := mem_V2.mp hv
  have hconj : proj 3 F M * (yP b * wP c) * (proj 3 F M)⁻¹ =
      (proj 3 F M * yP b * (proj 3 F M)⁻¹) * (proj 3 F M * wP c * (proj 3 F M)⁻¹) := by group
  rw [hconj, conj_yP_Q3 hM, conj_wP_Q3' hM]
  exact mul_mem ⟨_, _, rfl⟩ ⟨_, _, rfl⟩

theorem projQ3_le_normalizer_V2 [Finite F] :
    (Q3 F 1).map (proj 3 F) ≤
      Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  rintro _ ⟨M, hM, rfl⟩
  refine CFSG.QuasithinUnique.Fin257.L3.mem_normalizer_of_conj _
    (fun v hv => projQ3_conj_V2 hM hv) (fun v hv => ?_)
  have := projQ3_conj_V2 ((Q3 F 1).inv_mem hM) hv
  simpa [map_inv] using this

theorem normalizer_V2_le_projQ3 [Finite F] :
    Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) ≤
      (Q3 F 1).map (proj 3 F) := by
  set A : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) :=
    (Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))).comap
      (proj 3 F) with hA
  have hVA : unitriangular 3 F ≤ A := by
    intro u hu
    exact U_le_normalizer_V2 ⟨u, hu, rfl⟩
  have hAt : A ≠ ⊤ := by
    intro h
    apply (normalizer_V2_lt_top (F := F)).ne
    rw [eq_top_iff]
    intro g _
    obtain ⟨M, rfl⟩ := proj_surjective 3 F g
    have : M ∈ A := by rw [h]; trivial
    exact this
  rcases contained_in_Q3 hVA hAt with h | h
  · exfalso
    have hs : (s₁₂Mat : Matrix.SpecialLinearGroup (Fin 3) F) ∈ A := s12P_mem_normalizer_V2
    have h10 := (mem_Q3_zero_iff.mp (h hs)).1
    have : (s₁₂Mat : Matrix.SpecialLinearGroup (Fin 3) F) 1 0 = 1 := by
      simp [s₁₂Mat, s₁₂M]
    rw [this] at h10
    exact one_ne_zero h10
  · intro g hg
    obtain ⟨M, rfl⟩ := proj_surjective 3 F g
    exact ⟨M, h hg, rfl⟩

theorem normalizer_V2_eq [Finite F] :
    Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) =
      (Q3 F 1).map (proj 3 F) :=
  le_antisymm normalizer_V2_le_projQ3 projQ3_le_normalizer_V2

theorem exists_params_V2 [Finite F] {m : projectiveSL 3 F}
    (hm : m ∈ Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))) :
    ∃ α β : F, (α ≠ 0 ∨ β ≠ 0) ∧ ∀ c, m * wP c * m⁻¹ = yP (α * c) * wP (β * c) := by
  rw [normalizer_V2_eq] at hm
  obtain ⟨M, hM, rfl⟩ := hm
  obtain ⟨h20, h21⟩ := mem_Q3_one_iff.mp hM
  have hd := det_V2 h20 h21
  set Δ : F := M.1 0 0 * M.1 1 1 -
    M.1 0 1 * M.1 1 0 with hΔ
  refine ⟨Δ * M.1 1 0, Δ * M.1 0 0, ?_,
    fun c => conj_wP_Q3' hM c⟩
  by_contra hcon
  have hα : Δ * M.1 1 0 = 0 := by_contra fun h => hcon (Or.inl h)
  have hβ : Δ * M.1 0 0 = 0 := by_contra fun h => hcon (Or.inr h)
  have hΔ0 : Δ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hd
    exact zero_ne_one hd
  have h10 := (mul_eq_zero.mp hα).resolve_left hΔ0
  have h00 := (mul_eq_zero.mp hβ).resolve_left hΔ0
  apply hΔ0
  rw [hΔ, h10, h00]
  ring

theorem fix_V2 [Finite F] (hq : 2 < Nat.card F) {m : projectiveSL 3 F}
    (hm : m ∈ Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)))
    (hstab : ∀ c ∈ torus3 F, ∀ z ∈ conjSub m (Wg : Subgroup (projectiveSL 3 F)),
      c * z * c⁻¹ ∈ conjSub m (Wg : Subgroup (projectiveSL 3 F))) :
    conjSub m (Wg : Subgroup (projectiveSL 3 F)) = Wg ∨
      conjSub m (Wg : Subgroup (projectiveSL 3 F)) =
        conjSub (s₁₂P : projectiveSL 3 F) (Wg : Subgroup (projectiveSL 3 F)) := by
  obtain ⟨α, β, hαβ, hmw⟩ := exists_params_V2 hm
  obtain ⟨ω, hω⟩ := exists_unit_ne_one hq
  have hω1 : (ω : F) ≠ 1 := fun h => hω (Units.ext h)
  have hω0 : (ω : F) ≠ 0 := ω.ne_zero
  refine fix_of_lines (B₀ := torus3 F) yP wP (fun x => mem_Wg)
    (fun a c a' c' h => yP_wP_inj h) yP_zero wP_zero (t := proj 3 F (dMat 1 ω))
    (dP_mem_torus3 1 ω) (χ := (ω : F) * ω) (ψ := (ω : F)) ?_ ?_ ?_
    (s := s₁₂P) (fun c => s12P_conj_wP' c) hαβ hmw hstab
  · intro h
    apply hω1
    have : (ω : F) * (ω - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hω0
    · linear_combination h1
  · intro b
    rw [dP_conj_yP]
    simp
  · intro c
    rw [dP_conj_wP]
    simp

theorem cov_V2 [Finite F] {x : projectiveSL 3 F} (hx : x ∈ (V2 : Subgroup (projectiveSL 3 F))) :
    ∃ m ∈ Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)),
      m * x * m⁻¹ ∈ (Wg : Subgroup (projectiveSL 3 F)) := by
  obtain ⟨b, c, rfl⟩ := mem_V2.mp hx
  by_cases hc : c = 0
  · subst hc
    refine ⟨s₁₂P, s12P_mem_normalizer_V2, ?_⟩
    rw [wP_zero, mul_one, s12P_conj_yP']
    exact mem_Wg.mpr ⟨b, rfl⟩
  · have hM : vMat (b * c⁻¹) ∈ Q3 F 1 := by
      rw [mem_Q3_one_iff]
      simp [coe_vMat]
    refine ⟨proj 3 F (vMat (b * c⁻¹)), ?_, ?_⟩
    · rw [normalizer_V2_eq]
      exact ⟨_, hM, rfl⟩
    · have e1 := conj_yP_Q3 hM b
      have e2 := conj_wP_Q3' hM c
      simp [coe_vMat] at e1 e2
      have hconj : proj 3 F (vMat (b * c⁻¹)) * (yP b * wP c) * (proj 3 F (vMat (b * c⁻¹)))⁻¹ =
          (proj 3 F (vMat (b * c⁻¹)) * yP b * (proj 3 F (vMat (b * c⁻¹)))⁻¹) *
          (proj 3 F (vMat (b * c⁻¹)) * wP c * (proj 3 F (vMat (b * c⁻¹)))⁻¹) := by group
      rw [hconj, e1, e2]
      have h1 : b * c⁻¹ * c = b := by field_simp
      rw [h1, wP_zero, mul_one, ← mul_assoc, ← yP_add, CharTwo.add_self_eq_zero, yP_zero, one_mul]
      exact mem_Wg.mpr ⟨c, rfl⟩

theorem nonsolv_V2 [Finite F] (hK : ∃ s : Finset F, s.card = 4) :
    ¬ Group.IsSolvable ↥(Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F))) :=
  not_solvable_of_projQ3_le hK 1 projQ3_le_normalizer_V2

theorem half_V2 [Finite F] (hK : ∃ s : Finset F, s.card = 4) (hq : 2 < Nat.card F) :
    L3Half (projUnitriangular 3 F) (V2 : Subgroup (projectiveSL 3 F)) V1 (torus3 F) s₁₂P where
  s_mem := s12P_mem_normalizer_V2
  s_not := s12P_not_mem_normalizer_V1
  s_sq := s12P_mul_self
  s_norm := by
    intro b hb
    obtain ⟨t₁, t₂, rfl⟩ := mem_torus3.mp hb
    rw [s₁₂P_conj_torus]
    exact dP_mem_torus3 _ _
  cov := fun x hx _ => by
    rw [centerOf_U]
    exact cov_V2 hx
  nonsolv := nonsolv_V2 hK
  fix := by
    intro m hm hstab
    rw [centerOf_U] at hstab ⊢
    exact fix_V2 hq hm hstab

end CFSG.Quasithin.H13.F431.L3.P3
