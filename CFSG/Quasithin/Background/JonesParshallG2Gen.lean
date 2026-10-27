module

public import CFSG.Quasithin.Background.JonesParshallG2Stab

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Quasithin.Explicit CFSG.Open

variable {F : Type} [Field F] [CharP F 2]

@[expose] def gensG2 (F : Type) [Field F] [CharP F 2] :
    Set (quasithinZorn F ≃ₗ[F] quasithinZorn F) :=
  {g | (∃ a : Fin 3 → F, g = g2X a) ∨ (∃ b : Fin 3 → F, g = g2Y b) ∨ ∃ A : SL3 F, g = g2A A}

theorem gensG2_subset : gensG2 F ⊆ cayleyGroup F := by
  rintro g (⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨A, rfl⟩) <;> exact Subtype.property _

theorem g2X_mem_closure (a : Fin 3 → F) :
    ((g2X a : ↥(cayleyGroup F)) : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈
      Subgroup.closure (gensG2 F) :=
  Subgroup.subset_closure (Or.inl ⟨a, rfl⟩)

theorem g2Y_mem_closure (b : Fin 3 → F) :
    ((g2Y b : ↥(cayleyGroup F)) : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈
      Subgroup.closure (gensG2 F) :=
  Subgroup.subset_closure (Or.inr (Or.inl ⟨b, rfl⟩))

theorem g2A_mem_closure (A : SL3 F) :
    ((g2A A : ↥(cayleyGroup F)) : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈
      Subgroup.closure (gensG2 F) :=
  Subgroup.subset_closure (Or.inr (Or.inr ⟨A, rfl⟩))

theorem norm_zero_of_u_zero {ρ v₀ v₁ v₂ σ : F} (htr : ρ + σ = 0)
    (hN : ρ * σ + (0 * v₀ + 0 * v₁ + 0 * v₂) = 0) : ρ = 0 := by
  have hσ : σ = ρ := by
    have := eq_neg_of_add_eq_zero_right htr
    rw [this, CharTwo.neg_eq]
  rw [hσ] at hN
  simp only [zero_mul, add_zero] at hN
  exact pow_eq_zero_iff (two_ne_zero) |>.mp (by rw [sq]; exact hN)

theorem exists_closure_apply_zU0 {x : quasithinZorn F} (hx : x ≠ 0) (htr : cayleyTr x = 0)
    (hN : cayleyNorm x = 0) : ∃ g ∈ Subgroup.closure (gensG2 F), g (zU0 F) = x := by
  have h2 : ∀ c : F, c + c = 0 := CharTwo.add_self_eq_zero
  have base : ∀ ρ v₀ v₁ v₂ σ : F, ρ + σ = 0 → ρ * σ + (1 * v₀ + 0 * v₁ + 0 * v₂) = 0 →
      ∃ g ∈ Subgroup.closure (gensG2 F), g (zU0 F) = zmk ρ 1 0 0 v₀ v₁ v₂ σ := by
    intro ρ v₀ v₁ v₂ σ ht hn
    have hσ : σ = ρ := by
      have := eq_neg_of_add_eq_zero_right ht
      rw [this, CharTwo.neg_eq]
    subst hσ
    have hv₀ : v₀ = σ * σ := by
      have : σ * σ + v₀ = 0 := by linear_combination hn
      rw [eq_neg_of_add_eq_zero_right this, CharTwo.neg_eq]
    by_cases hρ : σ = 0
    · subst hρ
      refine ⟨g2X ![0, -v₂, v₁], g2X_mem_closure _, ?_⟩
      change xaFun ![0, -v₂, v₁] (zmk 0 1 0 0 0 0 0 0) = _
      rw [xaFun_zmk, hv₀]
      apply zmk_congr <;> simp
    · refine ⟨g2Y ![σ, v₁ / σ, v₂ / σ], g2Y_mem_closure _, ?_⟩
      change ybFun ![σ, v₁ / σ, v₂ / σ] (zmk 0 1 0 0 0 0 0 0) = _
      rw [ybFun_zmk, hv₀]
      apply zmk_congr <;> simp <;> field_simp
  have hu : ∀ y : quasithinZorn F, cayleyTr y = 0 → cayleyNorm y = 0 → y.2.1 ≠ 0 →
      ∃ g ∈ Subgroup.closure (gensG2 F), g (zU0 F) = y := by
    intro y hyt hyn hy
    obtain ⟨B, hB⟩ := MulAction.mem_orbit_iff.mp (mulVec3_e0_mem_orbit y.2.1 hy)
    set y' := gAFun ((B⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) y with hy'
    have hy'u : y'.2.1 = ![1, 0, 0] := by
      change ((B⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y.2.1 = _
      rw [← hB]
      change ((B⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        ((B : Matrix (Fin 3) (Fin 3) F) *ᵥ e0) = _
      rw [mulVec_mulVec, sl3_inv_mul_coe, one_mulVec]
      rfl
    have hy't : cayleyTr y' = 0 := by rw [hy', gAFun_tr]; exact hyt
    have hy'n : cayleyNorm y' = 0 := by rw [hy', gAFun_norm (B⁻¹).2]; exact hyn
    rw [zorn_eta y', hy'u] at hy't hy'n
    rw [cayleyTr_zmk] at hy't
    rw [cayleyNorm_zmk] at hy'n
    simp only [cons_val_zero, cons_val_one, cons_val_two, head_cons, tail_cons] at hy'n
    obtain ⟨g, hg, hge⟩ := base _ _ _ _ _ hy't hy'n
    refine ⟨g2A B * g, Subgroup.mul_mem _ (g2A_mem_closure B) hg, ?_⟩
    change gAFun (B : Matrix (Fin 3) (Fin 3) F) (g (zU0 F)) = y
    have hyy : y = gAFun (B : Matrix (Fin 3) (Fin 3) F) y' := by
      rw [hy', gAFun_mul_mat, sl3_mul_inv_coe, gAFun_one]
    rw [hge, hyy]
    congr 1
    conv_rhs => rw [zorn_eta y']
    simp [hy'u]
  by_cases hx0 : x.2.1 = 0
  ·
    rw [zorn_eta x, cayleyTr_zmk] at htr
    rw [zorn_eta x, cayleyNorm_zmk] at hN
    have hu0 : x.2.1 0 = 0 := congrFun hx0 0
    have hu1 : x.2.1 1 = 0 := congrFun hx0 1
    have hu2 : x.2.1 2 = 0 := congrFun hx0 2
    rw [hu0, hu1, hu2] at hN
    have hρ := norm_zero_of_u_zero htr hN
    have hσ : x.2.2.2 = 0 := by rw [hρ, zero_add] at htr; exact htr
    have hv : ∃ i, x.2.2.1 i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hx
      rw [zorn_eta x, hρ, hu0, hu1, hu2, hcon 0, hcon 1, hcon 2, hσ, zmk_zero]
    obtain ⟨i, hi⟩ := hv
    set a : Fin 3 → F := Pi.single i 1 with ha
    set y := xaFun a x with hy
    have hyt : cayleyTr y = 0 := by rw [hy, xaFun_tr, zorn_eta x, cayleyTr_zmk]; exact htr
    have hyn : cayleyNorm y = 0 := by
      rw [hy, xaFun_norm, zorn_eta x, cayleyNorm_zmk, hu0, hu1, hu2]
      exact hN
    have hyu : y.2.1 ≠ 0 := by
      intro h0
      have hc := congrFun h0 i
      rw [hy, zorn_eta x, xaFun_zmk] at hc
      simp only [zmk] at hc
      fin_cases i <;> simp [ha, hu0, hu1, hu2, hρ, hσ] at hc <;> exact hi hc
    obtain ⟨g, hg, hge⟩ := hu y hyt hyn hyu
    refine ⟨g2X a * g, Subgroup.mul_mem _ (g2X_mem_closure a) hg, ?_⟩
    change xaFun a (g (zU0 F)) = x
    rw [hge, hy, xaFun_xaFun]
  · exact hu x htr hN hx0

theorem cayleyGroup_eq_closure : cayleyGroup F = Subgroup.closure (gensG2 F) := by
  refine le_antisymm (fun g hg => ?_) ((Subgroup.closure_le _).mpr gensG2_subset)
  set g' : ↥(cayleyGroup F) := ⟨g, hg⟩
  have hx : cgE g' (zU0 F) ≠ 0 := by
    intro h0
    have : zU0 F = 0 := by
      rw [← cg_inv_apply g' (zU0 F), h0, map_zero]
    have h1 := congrArg Prod.fst (congrArg Prod.snd this)
    exact one_ne_zero (congrFun h1 0)
  have htr : cayleyTr (cgE g' (zU0 F)) = 0 := by rw [cg_tr, zU0, cayleyTr_zmk, add_zero]
  have hN : cayleyNorm (cgE g' (zU0 F)) = 0 := by
    rw [cg_norm, zU0, cayleyNorm_zmk]
    ring
  obtain ⟨r, hr, hre⟩ := exists_closure_apply_zU0 hx htr hN
  have hrC : r ∈ cayleyGroup F := (Subgroup.closure_le _).mpr gensG2_subset hr
  set r' : ↥(cayleyGroup F) := ⟨r, hrC⟩
  have hfix : cgE (r'⁻¹ * g') (zU0 F) = zU0 F := by
    rw [cg_mul_apply, ← hre]
    exact cg_inv_apply r' (zU0 F)
  obtain ⟨α, β, γ, A, -, hA⟩ := eq_uW_mul_g2A hfix
  have hg' : g = r * ((g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A A : ↥(cayleyGroup F)) :
      quasithinZorn F ≃ₗ[F] quasithinZorn F) := by
    rw [← hA]
    change g = r * (r⁻¹ * g)
    group
  rw [hg']
  refine Subgroup.mul_mem _ hr ?_
  simp only [Subgroup.coe_mul]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (g2X_mem_closure _) (g2Y_mem_closure _))
    (g2A_mem_closure _)

end CFSG.Quasithin.JonesParshall
