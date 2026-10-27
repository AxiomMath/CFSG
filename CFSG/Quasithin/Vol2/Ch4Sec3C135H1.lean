module

public import CFSG.Quasithin.Vol2.Ch4Sec3C136Norm
public import CFSG.Quasithin.Vol2.Ch4Sec3L4311SL3

public section

namespace CFSG.Quasithin.H13.Ch4.C135

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.Ch4

variable {F : Type} [Field F]

@[expose] def dualHom : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) F where
  toFun γ := ⟨((γ⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ, by
    rw [det_transpose]
    exact (γ⁻¹).2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' γ δ := Subtype.ext (by
    change (((γ * δ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).adjugate)ᵀ =
      ((γ : Matrix (Fin 3) (Fin 3) F).adjugate)ᵀ * ((δ : Matrix (Fin 3) (Fin 3) F).adjugate)ᵀ
    rw [Matrix.SpecialLinearGroup.coe_mul, adjugate_mul_distrib, transpose_mul])

theorem coe_dualHom (γ : SpecialLinearGroup (Fin 3) F) :
    ((dualHom γ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((γ⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ := rfl

theorem dualHom_dualHom (γ : SpecialLinearGroup (Fin 3) F) : dualHom (dualHom γ) = γ := by
  apply Subtype.ext
  have e : (((dualHom γ)⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((dualHom γ⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
    congrArg Subtype.val (map_inv dualHom γ).symm
  change (((dualHom γ)⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ = γ
  rw [e, coe_dualHom, transpose_transpose, inv_inv]

theorem coe_hom_mul {K : Type*} [Group K] (ρ : K →* SpecialLinearGroup (Fin 3) F) (g h : K) :
    ((ρ (g * h) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (ρ g : Matrix (Fin 3) (Fin 3) F) * (ρ h : Matrix (Fin 3) (Fin 3) F) := by
  rw [map_mul]
  rfl

@[expose] noncomputable def slNat {K : Type*} [Group K] (α : K →* ↥(StatedSL 3 F)) :
    K →* SpecialLinearGroup (Fin 3) F :=
  (specialLinearGroupEquivStatedSL 3 F).symm.toMonoidHom.comp α

theorem coe_slNat {K : Type*} [Group K] (α : K →* ↥(StatedSL 3 F)) (g : K) :
    ((slNat α g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((α g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  conv_rhs => rw [← (specialLinearGroupEquivStatedSL 3 F).apply_symm_apply (α g)]
  rfl

theorem moduleAct_false_eq {K : Type*} [Group K] (α : K →* ↥(StatedSL 3 F)) (g : K) :
    moduleAct false (α g : GL (Fin 3) F) =
      ((slNat α g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  rw [coe_slNat]
  rfl

theorem moduleAct_true_eq {K : Type*} [Group K] (α : K →* ↥(StatedSL 3 F)) (g : K) :
    moduleAct true (α g : GL (Fin 3) F) =
      ((dualHom (slNat α g) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  rw [coe_dualHom]
  have e : α g = specialLinearGroupEquivStatedSL 3 F (slNat α g) := by
    rw [slNat, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  show ((((α g : GL (Fin 3) F))⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ = _
  rw [e]
  rfl

theorem dact_sub (X : Matrix (Fin 3) (Fin 3) F) {k : ℕ} (v w : Fin k → Fin 3 → F) :
    dact X (v - w) = dact X v - dact X w := by
  funext i
  simp [dact, mulVec_sub]

theorem dact_neg (X : Matrix (Fin 3) (Fin 3) F) {k : ℕ} (v : Fin k → Fin 3 → F) :
    dact X (-v) = -dact X v := by
  funext i
  simp [dact, mulVec_neg]

theorem dact_mul (X Y : Matrix (Fin 3) (Fin 3) F) {k : ℕ} (v : Fin k → Fin 3 → F) :
    dact (X * Y) v = dact X (dact Y v) := by
  funext i
  simp [dact, mulVec_mulVec]

theorem exists_coboundary {K : Type*} [Group K] {k : ℕ} {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (hcc : c * c ≠ 1) {ρ : K →* SpecialLinearGroup (Fin 3) F} (hρ : Function.Surjective ρ)
    {f : K → Fin k → Fin 3 → F}
    (hf : ∀ g h, f (g * h) = f g + dact (ρ g : Matrix (Fin 3) (Fin 3) F) (f h))
    (hker : ∀ a, ρ a = 1 → f a = 0) :
    ∃ m : Fin k → Fin 3 → F, ∀ g, f g = dact (ρ g : Matrix (Fin 3) (Fin 3) F) m - m := by
  classical
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  set d₀ := torusSL c hc0 0 1 h01 with hd₀
  obtain ⟨k₀, hk₀⟩ := hρ d₀
  set m : Fin k → Fin 3 → F := fun i l => f k₀ i l / (torusPair c 0 1 l - 1) with hm
  set f' : K → Fin k → Fin 3 → F :=
    fun g => f g - (dact (ρ g : Matrix (Fin 3) (Fin 3) F) m - m) with hf'
  have hf'mul : ∀ g h, f' (g * h) = f' g + dact (ρ g : Matrix (Fin 3) (Fin 3) F) (f' h) := by
    intro g h
    show f (g * h) - (dact (ρ (g * h) : Matrix (Fin 3) (Fin 3) F) m - m) =
      (f g - (dact (ρ g : Matrix (Fin 3) (Fin 3) F) m - m)) +
        dact (ρ g : Matrix (Fin 3) (Fin 3) F) (f h - (dact (ρ h : Matrix (Fin 3) (Fin 3) F) m - m))
    rw [hf, coe_hom_mul, dact_mul, dact_sub, dact_sub]
    abel
  have hf'ker : ∀ a, ρ a = 1 → f' a = 0 := by
    intro a ha
    simp only [hf', hker a ha, ha, Matrix.SpecialLinearGroup.coe_one]
    funext i l
    simp [dact]
  have hf'k₀ : f' k₀ = 0 := by
    funext i l
    simp only [hf', hk₀, hd₀, torusSL_coe, dact, Pi.sub_apply, mulVec_diagonal, hm,
      Pi.zero_apply]
    have hne : torusPair c 0 1 l - 1 ≠ 0 := sub_ne_zero.mpr (torusPair_ne_one hc1 hcc 0 1 l)
    field_simp
    ring
  have hlift : ∀ g g', ρ g = ρ g' → f' g = f' g' := by
    intro g g' h
    have ha : ρ (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have e1 := hf'mul g (g⁻¹ * g')
    rw [mul_inv_cancel_left, hf'ker _ ha] at e1
    rw [e1]
    funext i
    simp [dact]
  let P : SpecialLinearGroup (Fin 3) F → Prop := fun γ => ∀ g, ρ g = γ → f' g = 0
  have hP0 : P d₀ := fun g hg => (hlift g k₀ (hg.trans hk₀.symm)).trans hf'k₀
  have hPmul : ∀ A B, P A → P B → P (A * B) := by
    intro A B hA hB g hg
    obtain ⟨a, ha⟩ := hρ A
    obtain ⟨b, hb⟩ := hρ B
    rw [hlift g (a * b) (by rw [hg, map_mul, ha, hb]), hf'mul, hA a ha, hB b hb]
    funext i
    simp [dact]
  have hkey : ∀ γ d : SpecialLinearGroup (Fin 3) F, γ * d = d * γ →
      (∀ v : Fin 3 → F, (d : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v → v = 0) → P d → P γ := by
    intro γ d hγd hfp hd g hg
    obtain ⟨kd, hkd⟩ := hρ d
    have e1 := hf'mul g kd
    have e2 := hf'mul kd g
    rw [hd kd hkd] at e1
    have e3 : f' (g * kd) = f' (kd * g) := hlift _ _ (by rw [map_mul, map_mul, hg, hkd, hγd])
    rw [e1, e2, hd kd hkd, hkd] at e3
    have e4 : f' g = dact (d : Matrix (Fin 3) (Fin 3) F) (f' g) := by
      have h0 : dact (ρ g : Matrix (Fin 3) (Fin 3) F) (0 : Fin k → Fin 3 → F) = 0 := by
        funext i
        simp [dact]
      simpa [h0] using e3
    funext i
    exact hfp _ (congrFun e4 i).symm
  have hd₀diag : ∃ f, (d₀ : Matrix (Fin 3) (Fin 3) F) = diagonal f :=
    ⟨_, torusSL_coe _ _ _ _ _⟩
  have hPdiag : ∀ γ : SpecialLinearGroup (Fin 3) F,
      (∃ f, (γ : Matrix (Fin 3) (Fin 3) F) = diagonal f) → P γ :=
    fun γ hγ => hkey γ d₀ (commute_of_diagonal hγ hd₀diag)
      (fun v hv => eq_zero_of_torusPair_fixed hc1 hcc hv) hP0
  have hPtr : ∀ (i j : Fin 3) (hij : i ≠ j) (b : F),
      P (Matrix.SpecialLinearGroup.transvection hij b) := by
    intro i j hij b
    exact hkey _ (torusSL c hc0 i j hij) (torusSL_mul_transvection hc0 hij b).symm
      (fun v hv => eq_zero_of_torusPair_fixed hc1 hcc hv) (hPdiag _ ⟨_, torusSL_coe _ _ _ _ _⟩)
  have hPall : ∀ γ, P γ := fun γ =>
    Matrix.SpecialLinearGroup.diagonal_transvection_induction' P γ
      (fun i j hij c' hc' => hPdiag _ ⟨_, Matrix.SpecialLinearGroup.diag2n_coe hij c' hc'⟩)
      hPtr hPmul
  refine ⟨m, fun g => ?_⟩
  have h := hPall (ρ g) g rfl
  simp only [hf'] at h
  exact sub_eq_zero.mp h

theorem transvection_inv {i j : Fin 3} (hij : i ≠ j) (b : F) :
    (Matrix.SpecialLinearGroup.transvection hij b)⁻¹ =
      Matrix.SpecialLinearGroup.transvection hij (-b) := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  show Matrix.transvection i j b * Matrix.transvection i j (-b) = 1
  rw [transvection_mul_transvection_same i j hij, add_neg_cancel, transvection_zero]

theorem dualHom_transvection_mulVec {i j : Fin 3} (hij : i ≠ j) (b : F) (w : Fin 3 → F) :
    ((dualHom (Matrix.SpecialLinearGroup.transvection hij b) : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ w = w - Pi.single j (b * w i) := by
  rw [coe_dualHom, transvection_inv, Matrix.SpecialLinearGroup.transvection_coe, transpose_add,
    transpose_one, transpose_single, add_mulVec, one_mulVec, single_mulVec, neg_mul]
  funext l
  by_cases hl : l = j
  · subst hl
    simp [sub_eq_add_neg]
  · simp [hl]

theorem eq_zero_of_dual_equivariant (φ : (Fin 3 → F) → (Fin 3 → F))
    (h : ∀ (γ : SpecialLinearGroup (Fin 3) F) (v : Fin 3 → F),
      φ (((dualHom γ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
        (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ φ v) (v : Fin 3 → F) : φ v = 0 := by
  classical
  have hfix : ∀ (i j : Fin 3) (hij : i ≠ j) (w : Fin 3 → F), w i = 0 → φ w j = 0 := by
    intro i j hij w hw
    have h1 := h (Matrix.SpecialLinearGroup.transvection hij 1) w
    rw [dualHom_transvection_mulVec, hw, mul_zero, Pi.single_zero, sub_zero,
      transvection_mulVec] at h1
    have h2 := congrFun h1 i
    simp only [Pi.add_apply, Pi.single_eq_same, one_mul] at h2
    linear_combination -h2
  have he₀ : φ ![1, 0, 0] = 0 := by
    funext j
    fin_cases j
    · exact hfix 1 0 (by decide) _ rfl
    · exact hfix 2 1 (by decide) _ rfl
    · exact hfix 1 2 (by decide) _ rfl
  by_cases hv : v = 0
  · subst hv
    funext j
    obtain ⟨i, hij⟩ : ∃ i : Fin 3, i ≠ j := by
      by_cases h0 : j = 0
      · exact ⟨1, by rw [h0]; decide⟩
      · exact ⟨0, fun h' => h0 h'.symm⟩
    exact hfix i j hij 0 rfl
  · obtain ⟨g, hg⟩ := SL3Pt.exists_mulVec_e0 hv
    have h1 := h (dualHom g) ![1, 0, 0]
    rw [dualHom_dualHom, hg, he₀, mulVec_zero] at h1
    exact h1

theorem eq_zero_of_dual_equivariant_pi {k : ℕ} (φ : (Fin k → Fin 3 → F) →+ (Fin 3 → F))
    (h : ∀ (γ : Matrix.SpecialLinearGroup (Fin 3) F) (v : Fin k → Fin 3 → F),
      φ (dact ((dualHom γ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) v) =
        (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ φ v) : φ = 0 := by
  classical
  have hsingle : ∀ (i : Fin k) (y : Fin 3 → F), φ (Pi.single i y) = 0 := by
    intro i y
    refine eq_zero_of_dual_equivariant (fun y => φ (Pi.single i y)) (fun γ v => ?_) y
    rw [← dact_single, h]
  refine AddMonoidHom.ext fun v => ?_
  rw [← Finset.univ_sum_single v, map_sum, AddMonoidHom.zero_apply]
  exact Finset.sum_eq_zero fun i _ => hsingle i (v i)

end CFSG.Quasithin.H13.Ch4.C135

end
