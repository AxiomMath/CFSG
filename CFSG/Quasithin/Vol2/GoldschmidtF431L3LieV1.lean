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
theorem det_V1 {M : Matrix.SpecialLinearGroup (Fin 3) F}
    (h10 : M.1 1 0 = 0) (h20 : M.1 2 0 = 0) :
    M.1 0 0 * (M.1 1 1 *
      M.1 2 2 - M.1 1 2 *
      M.1 2 1) = 1 := by
  have := M.2
  rw [Matrix.det_fin_three] at this
  rw [h10, h20] at this
  linear_combination this

theorem mat_V1_w {M : Matrix.SpecialLinearGroup (Fin 3) F}
    (h10 : M.1 1 0 = 0) (h20 : M.1 2 0 = 0)
    (c : F) :
    M * wMat c = xMat (M.1 0 0 ^ 2 * M.1 2 1 * c) *
      wMat (M.1 0 0 ^ 2 * M.1 1 1 * c) * M := by
  have hd := det_V1 h10 h20
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  change M.1 * wM c = (xM _ * wM _) * M.1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wM, xM, Matrix.mul_apply, Fin.sum_univ_three, h10, h20]
  · linear_combination (-(M.1 0 0 ^ 2 * M.1 1 1 *
      M.1 2 1 * c)) * h2
  · linear_combination (-(M.1 0 0 * c)) * hd +
      (-(M.1 0 0 ^ 2 * c * M.1 1 2 *
      M.1 2 1)) * h2

theorem mat_V1_x {M : Matrix.SpecialLinearGroup (Fin 3) F}
    (h10 : M.1 1 0 = 0) (h20 : M.1 2 0 = 0)
    (a : F) :
    M * xMat a = xMat (M.1 0 0 ^ 2 * M.1 2 2 * a) *
      wMat (M.1 0 0 ^ 2 * M.1 1 2 * a) * M := by
  have hd := det_V1 h10 h20
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  change M.1 * xM a = (xM _ * wM _) * M.1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wM, xM, Matrix.mul_apply, Fin.sum_univ_three, h10, h20]
  · linear_combination (-(M.1 0 0 * a)) * hd +
      (-(M.1 0 0 ^ 2 * a * M.1 1 2 *
      M.1 2 1)) * h2
  · linear_combination (-(M.1 0 0 ^ 2 * a *
      M.1 1 2 * M.1 2 2)) * h2

theorem projQ3_conj_V1 [Finite F] {M : Matrix.SpecialLinearGroup (Fin 3) F} (hM : M ∈ Q3 F 0)
    {v : projectiveSL 3 F} (hv : v ∈ (V1 : Subgroup (projectiveSL 3 F))) :
    proj 3 F M * v * (proj 3 F M)⁻¹ ∈ (V1 : Subgroup (projectiveSL 3 F)) := by
  obtain ⟨h10, h20⟩ := mem_Q3_zero_iff.mp hM
  obtain ⟨a, c, rfl⟩ := mem_V1.mp hv
  set m : projectiveSL 3 F := proj 3 F M with hm
  have hx := congrArg (proj 3 F) (mat_V1_x h10 h20 a)
  have hw := congrArg (proj 3 F) (mat_V1_w h10 h20 c)
  rw [map_mul, map_mul, map_mul] at hx hw
  have hx' : m * xP a * m⁻¹ = xP (M.1 0 0 ^ 2 *
      M.1 2 2 * a) * wP (M.1 0 0 ^ 2 *
      M.1 1 2 * a) := by
    have : m * xP a = (xP (M.1 0 0 ^ 2 *
      M.1 2 2 * a) * wP (M.1 0 0 ^ 2 *
      M.1 1 2 * a)) * m := hx
    rw [this]; group
  have hw' : m * wP c * m⁻¹ = xP (M.1 0 0 ^ 2 *
      M.1 2 1 * c) * wP (M.1 0 0 ^ 2 *
      M.1 1 1 * c) := by
    have : m * wP c = (xP (M.1 0 0 ^ 2 *
      M.1 2 1 * c) * wP (M.1 0 0 ^ 2 *
      M.1 1 1 * c)) * m := hw
    rw [this]; group
  have hconj : m * (xP a * wP c) * m⁻¹ = (m * xP a * m⁻¹) * (m * wP c * m⁻¹) := by group
  rw [hconj, hx', hw']
  exact mul_mem ⟨_, _, rfl⟩ ⟨_, _, rfl⟩

theorem projQ3_le_normalizer_V1 [Finite F] :
    (Q3 F 0).map (proj 3 F) ≤
      Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
  rintro _ ⟨M, hM, rfl⟩
  refine CFSG.QuasithinUnique.Fin257.L3.mem_normalizer_of_conj _
    (fun v hv => projQ3_conj_V1 hM hv) (fun v hv => ?_)
  have := projQ3_conj_V1 ((Q3 F 0).inv_mem hM) hv
  simpa [map_inv] using this

theorem normalizer_V1_le_projQ3 [Finite F] :
    Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) ≤
      (Q3 F 0).map (proj 3 F) := by
  set A : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) :=
    (Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))).comap
      (proj 3 F) with hA
  have hVA : unitriangular 3 F ≤ A := by
    intro u hu
    exact U_le_normalizer_V1 ⟨u, hu, rfl⟩
  have hAt : A ≠ ⊤ := by
    intro h
    apply (normalizer_V1_lt_top (F := F)).ne
    rw [eq_top_iff]
    intro g _
    obtain ⟨M, rfl⟩ := proj_surjective 3 F g
    have : M ∈ A := by rw [h]; trivial
    exact this
  rcases contained_in_Q3 hVA hAt with h | h
  · intro g hg
    obtain ⟨M, rfl⟩ := proj_surjective 3 F g
    exact ⟨M, h hg, rfl⟩
  · exfalso
    have hs : (s₂₃Mat : Matrix.SpecialLinearGroup (Fin 3) F) ∈ A := s23P_mem_normalizer_V1
    have h21 := (mem_Q3_one_iff.mp (h hs)).2
    have : (s₂₃Mat : Matrix.SpecialLinearGroup (Fin 3) F) 2 1 = 1 := by
      simp [s₂₃Mat, s₂₃M]
    rw [this] at h21
    exact one_ne_zero h21

theorem normalizer_V1_eq [Finite F] :
    Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) =
      (Q3 F 0).map (proj 3 F) :=
  le_antisymm normalizer_V1_le_projQ3 projQ3_le_normalizer_V1

theorem exists_params_V1 [Finite F] {m : projectiveSL 3 F}
    (hm : m ∈ Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))) :
    ∃ α β : F, (α ≠ 0 ∨ β ≠ 0) ∧ ∀ c, m * wP c * m⁻¹ = xP (α * c) * wP (β * c) := by
  rw [normalizer_V1_eq] at hm
  obtain ⟨M, hM, rfl⟩ := hm
  obtain ⟨h10, h20⟩ := mem_Q3_zero_iff.mp hM
  have hd := det_V1 h10 h20
  refine ⟨M.1 0 0 ^ 2 * M.1 2 1,
    M.1 0 0 ^ 2 * M.1 1 1, ?_, fun c => ?_⟩
  · by_contra hcon
    have hα : M.1 0 0 ^ 2 * M.1 2 1 = 0 :=
      by_contra fun h => hcon (Or.inl h)
    have hβ : M.1 0 0 ^ 2 * M.1 1 1 = 0 :=
      by_contra fun h => hcon (Or.inr h)
    have h00 : M.1 0 0 ≠ 0 := by
      intro h
      rw [h, zero_mul] at hd
      exact zero_ne_one hd
    have h21 := (mul_eq_zero.mp hα).resolve_left (pow_ne_zero 2 h00)
    have h11 := (mul_eq_zero.mp hβ).resolve_left (pow_ne_zero 2 h00)
    rw [h21, h11] at hd
    simp at hd
  · have hw := congrArg (proj 3 F) (mat_V1_w h10 h20 c)
    rw [map_mul, map_mul, map_mul] at hw
    have : proj 3 F M * wP c = (xP (M.1 0 0 ^ 2 *
      M.1 2 1 * c) * wP (M.1 0 0 ^ 2 *
      M.1 1 1 * c)) * proj 3 F M := hw
    rw [this]; group

theorem fix_V1 [Finite F] (hq : 2 < Nat.card F) {m : projectiveSL 3 F}
    (hm : m ∈ Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)))
    (hstab : ∀ c ∈ torus3 F, ∀ z ∈ conjSub m (Wg : Subgroup (projectiveSL 3 F)),
      c * z * c⁻¹ ∈ conjSub m (Wg : Subgroup (projectiveSL 3 F))) :
    conjSub m (Wg : Subgroup (projectiveSL 3 F)) = Wg ∨
      conjSub m (Wg : Subgroup (projectiveSL 3 F)) =
        conjSub (s₂₃P : projectiveSL 3 F) (Wg : Subgroup (projectiveSL 3 F)) := by
  obtain ⟨α, β, hαβ, hmw⟩ := exists_params_V1 hm
  obtain ⟨ω, hω⟩ := exists_unit_ne_one hq
  have hω1 : (ω : F) ≠ 1 := fun h => hω (Units.ext h)
  have hω0 : (ω : F) ≠ 0 := ω.ne_zero
  refine fix_of_lines (B₀ := torus3 F) xP wP (fun x => mem_Wg)
    (fun a c a' c' h => xP_wP_inj h) xP_zero wP_zero (t := proj 3 F (dMat ω 1))
    (dP_mem_torus3 ω 1) (χ := (ω : F)) (ψ := (ω : F) * ω) ?_ ?_ ?_
    (s := s₂₃P) (fun c => s23P_conj_wP' c) hαβ hmw hstab
  · intro h
    apply hω1
    have : (ω : F) * (1 - ω) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hω0
    · linear_combination -h1
  · intro a
    rw [dP_conj_xP]
    simp
  · intro c
    rw [dP_conj_wP]
    simp

theorem conj_xP_Q3 {M : Matrix.SpecialLinearGroup (Fin 3) F} (hM : M ∈ Q3 F 0) (a : F) :
    proj 3 F M * xP a * (proj 3 F M)⁻¹ =
      xP (M.1 0 0 ^ 2 * M.1 2 2 * a) *
      wP (M.1 0 0 ^ 2 * M.1 1 2 * a) := by
  obtain ⟨h10, h20⟩ := mem_Q3_zero_iff.mp hM
  have hx := congrArg (proj 3 F) (mat_V1_x h10 h20 a)
  rw [map_mul, map_mul, map_mul] at hx
  have : proj 3 F M * xP a = (xP (M.1 0 0 ^ 2 *
      M.1 2 2 * a) * wP (M.1 0 0 ^ 2 *
      M.1 1 2 * a)) * proj 3 F M := hx
  rw [this]; group

theorem conj_wP_Q3 {M : Matrix.SpecialLinearGroup (Fin 3) F} (hM : M ∈ Q3 F 0) (c : F) :
    proj 3 F M * wP c * (proj 3 F M)⁻¹ =
      xP (M.1 0 0 ^ 2 * M.1 2 1 * c) *
      wP (M.1 0 0 ^ 2 * M.1 1 1 * c) := by
  obtain ⟨h10, h20⟩ := mem_Q3_zero_iff.mp hM
  have hw := congrArg (proj 3 F) (mat_V1_w h10 h20 c)
  rw [map_mul, map_mul, map_mul] at hw
  have : proj 3 F M * wP c = (xP (M.1 0 0 ^ 2 *
      M.1 2 1 * c) * wP (M.1 0 0 ^ 2 *
      M.1 1 1 * c)) * proj 3 F M := hw
  rw [this]; group

theorem cov_V1 [Finite F] {x : projectiveSL 3 F} (hx : x ∈ (V1 : Subgroup (projectiveSL 3 F))) :
    ∃ m ∈ Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)),
      m * x * m⁻¹ ∈ (Wg : Subgroup (projectiveSL 3 F)) := by
  obtain ⟨a, c, rfl⟩ := mem_V1.mp hx
  by_cases hc : c = 0
  · subst hc
    refine ⟨s₂₃P, s23P_mem_normalizer_V1, ?_⟩
    rw [wP_zero, mul_one, s23P_conj_xP']
    exact mem_Wg.mpr ⟨a, rfl⟩
  · have hM : zMat (a * c⁻¹) ∈ Q3 F 0 := by
      rw [mem_Q3_zero_iff]
      simp [coe_zMat]
    refine ⟨proj 3 F (zMat (a * c⁻¹)), ?_, ?_⟩
    · rw [normalizer_V1_eq]
      exact ⟨_, hM, rfl⟩
    · have e1 := conj_xP_Q3 hM a
      have e2 := conj_wP_Q3 hM c
      simp [coe_zMat] at e1 e2
      have hconj : proj 3 F (zMat (a * c⁻¹)) * (xP a * wP c) * (proj 3 F (zMat (a * c⁻¹)))⁻¹ =
          (proj 3 F (zMat (a * c⁻¹)) * xP a * (proj 3 F (zMat (a * c⁻¹)))⁻¹) *
          (proj 3 F (zMat (a * c⁻¹)) * wP c * (proj 3 F (zMat (a * c⁻¹)))⁻¹) := by group
      rw [hconj, e1, e2]
      have h1 : a * c⁻¹ * c = a := by field_simp
      rw [h1, wP_zero, mul_one, ← mul_assoc, ← xP_add, CharTwo.add_self_eq_zero, xP_zero, one_mul]
      exact mem_Wg.mpr ⟨c, rfl⟩

theorem nonsolv_V1 [Finite F] (hK : ∃ s : Finset F, s.card = 4) :
    ¬ Group.IsSolvable ↥(Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F))) :=
  not_solvable_of_projQ3_le hK 0 projQ3_le_normalizer_V1

theorem half_V1 [Finite F] (hK : ∃ s : Finset F, s.card = 4) (hq : 2 < Nat.card F) :
    L3Half (projUnitriangular 3 F) (V1 : Subgroup (projectiveSL 3 F)) V2 (torus3 F) s₂₃P where
  s_mem := s23P_mem_normalizer_V1
  s_not := s23P_not_mem_normalizer_V2
  s_sq := s23P_mul_self
  s_norm := by
    intro b hb
    obtain ⟨t₁, t₂, rfl⟩ := mem_torus3.mp hb
    rw [s₂₃P_conj_torus]
    exact dP_mem_torus3 _ _
  cov := fun x hx _ => by
    rw [centerOf_U]
    exact cov_V1 hx
  nonsolv := nonsolv_V1 hK
  fix := by
    intro m hm hstab
    rw [centerOf_U] at hstab ⊢
    exact fix_V1 hq hm hstab


end CFSG.Quasithin.H13.F431.L3.P3
