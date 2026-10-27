module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinMaxL3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

namespace L3T

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.QuasithinUnique.Fin257.L3

variable {F : Type} [Field F] [CharP F 2]

theorem mul_eq_of_apply_G2 {A : GL (Fin 3) F} {σ : F ≃+* F} {b c a c' : F}
    (h : (LinearFlag.conjAut 3 F A * fieldAut 3 F σ) (yP b * wP c) = xP a * wP c') :
    (A : Matrix (Fin 3) (Fin 3) F) *
        ((G2 b c : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map σ =
      ((G1 a c' : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (A : Matrix (Fin 3) (Fin 3) F) := by
  have h1 := standard_apply_proj A σ 0 (G2 b c)
  rw [pow_zero, mul_one, proj_G2, h, ← proj_G1] at h1
  have h2 : Phi A σ 0 (G2 b c) = G1 a c' := by
    refine eq_of_proj_eq_of_sq ?_ (G1_mul_self _ _) h1.symm
    rw [← map_mul, G2_mul_self, map_one]
  have h3 := congrArg
    (fun x : Matrix.SpecialLinearGroup (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) h2
  simp only [coe_Phi_zero] at h3
  exact mul_eq_of_phi h3

theorem not_forall_V2_mem_V1 {θ : MulAut (projectiveSL 3 F)} (hθ : θ ∈ semilinearAutGroup 3 F) :
    ¬ ∀ g ∈ (V2 : Subgroup (projectiveSL 3 F)), θ g ∈ (V1 : Subgroup (projectiveSL 3 F)) := by
  intro hall
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp hθ
  obtain ⟨a₁, c₁, h₁⟩ := mem_V1.mp (hall (yP 1 * wP 0) ⟨1, 0, rfl⟩)
  obtain ⟨a₂, c₂, h₂⟩ := mem_V1.mp (hall (yP 0 * wP 1) ⟨0, 1, rfl⟩)
  have e1 := mul_eq_of_apply_G2 h₁
  have e2 := mul_eq_of_apply_G2 h₂
  rw [coe_G2, coe_G1] at e1 e2
  have f1 := congrFun (congrFun e1 1) 2
  have f2 := congrFun (congrFun e1 2) 2
  have f3 := congrFun (congrFun e2 1) 2
  have f4 := congrFun (congrFun e2 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply] at f1 f2 f3 f4
  apply det_ne_zero A
  rw [Matrix.det_fin_three, f1, f2, f3, f4]
  ring

omit [CharP F 2] in
theorem inverseTranspose_W0 :
    Matrix.GeneralLinearGroup.inverseTranspose (W0 : GL (Fin 3) F) = W0 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_inverseTranspose]
  show (((W0 : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).transpose = _
  rw [coe_W0_inv, coe_W0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [CharP F 2] in
theorem W0_mul_self : (W0 : GL (Fin 3) F) * W0 = 1 := by
  apply Units.ext
  show ((W0 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
    ((W0 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1
  rw [coe_W0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

omit [CharP F 2] in
theorem iota_mul_iota : (iota : MulAut (projectiveSL 3 F)) * iota = 1 := by
  have htrans := standard_automorphism_transport (K := F) (n := 3)
  unfold iota
  calc LinearFlag.conjAut 3 F W0 * dualAut 3 F * (LinearFlag.conjAut 3 F W0 * dualAut 3 F)
      = LinearFlag.conjAut 3 F W0 *
          (dualAut 3 F * LinearFlag.conjAut 3 F W0 * dualAut 3 F) := by group
    _ = LinearFlag.conjAut 3 F W0 *
          LinearFlag.conjAut 3 F (Matrix.GeneralLinearGroup.inverseTranspose W0) := by
        rw [htrans.2.2.2.2.1]
    _ = LinearFlag.conjAut 3 F (W0 * Matrix.GeneralLinearGroup.inverseTranspose W0) := by
        rw [htrans.1]
    _ = 1 := by rw [inverseTranspose_W0, W0_mul_self, map_one]

omit [CharP F 2] in
theorem iota_inv : (iota : MulAut (projectiveSL 3 F))⁻¹ = iota :=
  inv_eq_of_mul_eq_one_right iota_mul_iota

theorem iota_mem_V2 {g : projectiveSL 3 F} (hg : g ∈ (V1 : Subgroup (projectiveSL 3 F))) :
    iota g ∈ (V2 : Subgroup (projectiveSL 3 F)) := by
  obtain ⟨a, c, rfl⟩ := mem_V1.mp hg
  have h : iota (xP a * wP c) = yP a * wP c := by
    rw [← iota_yP_wP a c, ← MulAut.mul_apply, iota_mul_iota, MulAut.one_apply]
  rw [h]
  exact mem_V2.mpr ⟨a, c, rfl⟩

theorem mem_semilinear_of_map_V1 [Finite F] {θ : MulAut (projectiveSL 3 F)}
    (h : ∀ g ∈ (V1 : Subgroup (projectiveSL 3 F)), θ g ∈ (V1 : Subgroup (projectiveSL 3 F))) :
    θ ∈ semilinearAutGroup 3 F := by
  have htrans := standard_automorphism_transport (K := F) (n := 3)
  have hR : standardAutGroup 3 F = ⊤ := (automorphism_generation (K := F) le_rfl).1
  have hθ : θ ∈ standardAutGroup 3 F := by rw [hR]; exact Subgroup.mem_top θ
  rcases mem_or_mul_dualAut_mem hθ with h1 | h1
  · exact h1
  · exfalso
    have hδδ : dualAut 3 F * dualAut 3 F = 1 := htrans.2.2.2.1
    have he : θ * iota =
        (θ * dualAut 3 F) * (dualAut 3 F * LinearFlag.conjAut 3 F W0 * dualAut 3 F) := by
      rw [show (θ * dualAut 3 F) * (dualAut 3 F * LinearFlag.conjAut 3 F W0 * dualAut 3 F) =
        θ * (dualAut 3 F * dualAut 3 F) * LinearFlag.conjAut 3 F W0 * dualAut 3 F by group,
        hδδ, mul_one]
      unfold iota
      group
    have he' : θ * iota ∈ semilinearAutGroup 3 F := by
      rw [he, htrans.2.2.2.2.1]
      exact mul_mem h1 (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _))
    refine not_forall_V2_mem_V1 he' fun g hg => ?_
    rw [MulAut.mul_apply]
    exact h _ (iota_mem_V1 hg)

theorem mem_semilinear_of_map_V2 [Finite F] {θ : MulAut (projectiveSL 3 F)}
    (h : ∀ g ∈ (V2 : Subgroup (projectiveSL 3 F)), θ g ∈ (V2 : Subgroup (projectiveSL 3 F))) :
    θ ∈ semilinearAutGroup 3 F := by
  have h1 : iota * θ * iota ∈ semilinearAutGroup 3 F := by
    refine mem_semilinear_of_map_V1 fun g hg => ?_
    simp only [MulAut.mul_apply]
    exact iota_mem_V1 (h _ (iota_mem_V2 hg))
  have h2 := (conj_mem_iff_semilinear (iota : MulAut (projectiveSL 3 F))⁻¹ θ).mp
  rw [iota_inv] at h2
  exact h2 (by rw [iota_inv]; exact h1)

theorem map_V_eq [Finite F] {θ : MulAut (projectiveSL 3 F)}
    (hθ : ∀ u ∈ projUnitriangular 3 F, θ u ∈ projUnitriangular 3 F)
    {V : Subgroup (projectiveSL 3 F)} (hV : V = V1 ∨ V = V2) :
    V.map θ.toMonoidHom = V1 ∨ V.map θ.toMonoidHom = V2 := by
  have hVU : V ≤ projUnitriangular 3 F := by rcases hV with rfl | rfl; exacts [V1_le_U, V2_le_U]
  have hVe : IsElemAbelian 2 V := by
    rcases hV with rfl | rfl; exacts [isElemAbelian_V1, isElemAbelian_V2]
  have hle : V.map θ.toMonoidHom ≤ projUnitriangular 3 F := by
    rintro _ ⟨v, hv, rfl⟩
    exact hθ v (hVU hv)
  have hsq : ∀ x ∈ V.map θ.toMonoidHom, x * x = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    have h2 : v ^ 2 = 1 := hVe.2 v hv
    rw [← map_mul, ← pow_two, h2, map_one]
  have hc : Nat.card (V.map θ.toMonoidHom) = Nat.card V :=
    Subgroup.card_map_of_injective θ.injective
  have hcV : Nat.card V = Nat.card (V1 : Subgroup (projectiveSL 3 F)) := by
    rcases hV with rfl | rfl
    · rfl
    · exact card_V1_eq_card_V2.symm
  rcases elem_le_V1_or_V2 hle hsq with h | h
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (by rw [hc, hcV]))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (by rw [hc, hcV, card_V1_eq_card_V2]))

theorem map_V_of_mem_semilinear [Finite F] {θ : MulAut (projectiveSL 3 F)}
    (hθE : θ ∈ semilinearAutGroup 3 F)
    (hθ : ∀ u ∈ projUnitriangular 3 F, θ u ∈ projUnitriangular 3 F) :
    (V1 : Subgroup (projectiveSL 3 F)).map θ.toMonoidHom = V1 ∧
      (V2 : Subgroup (projectiveSL 3 F)).map θ.toMonoidHom = V2 := by
  have h2 : (V2 : Subgroup (projectiveSL 3 F)).map θ.toMonoidHom = V2 := by
    rcases map_V_eq hθ (Or.inr rfl) with h | h
    · exact absurd (fun g hg => h ▸ Subgroup.mem_map_of_mem _ hg) (not_forall_V2_mem_V1 hθE)
    · exact h
  refine ⟨?_, h2⟩
  rcases map_V_eq hθ (Or.inl rfl) with h | h
  · exact h
  · exact absurd (Subgroup.map_injective θ.injective (h.trans h2.symm)) V1_ne_V2

theorem map_V_of_not_mem_semilinear [Finite F] {θ : MulAut (projectiveSL 3 F)}
    (hθE : θ ∉ semilinearAutGroup 3 F)
    (hθ : ∀ u ∈ projUnitriangular 3 F, θ u ∈ projUnitriangular 3 F) :
    (V1 : Subgroup (projectiveSL 3 F)).map θ.toMonoidHom = V2 ∧
      (V2 : Subgroup (projectiveSL 3 F)).map θ.toMonoidHom = V1 := by
  refine ⟨?_, ?_⟩
  · rcases map_V_eq hθ (Or.inl rfl) with h | h
    · exact absurd (mem_semilinear_of_map_V1 fun g hg => h ▸ Subgroup.mem_map_of_mem _ hg) hθE
    · exact h
  · rcases map_V_eq hθ (Or.inr rfl) with h | h
    · exact h
    · exact absurd (mem_semilinear_of_map_V2 fun g hg => h ▸ Subgroup.mem_map_of_mem _ hg) hθE

theorem map_Wg [Finite F] {θ : MulAut (projectiveSL 3 F)}
    (hθ : ∀ u ∈ projUnitriangular 3 F, θ u ∈ projUnitriangular 3 F) :
    (Wg : Subgroup (projectiveSL 3 F)).map θ.toMonoidHom = Wg := by
  rw [← V1_inf_V2, Subgroup.map_inf _ _ _ θ.injective]
  by_cases hθE : θ ∈ semilinearAutGroup 3 F
  · obtain ⟨h1, h2⟩ := map_V_of_mem_semilinear hθE hθ
    rw [h1, h2]
  · obtain ⟨h1, h2⟩ := map_V_of_not_mem_semilinear hθE hθ
    rw [h1, h2, inf_comm]

end L3T

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
