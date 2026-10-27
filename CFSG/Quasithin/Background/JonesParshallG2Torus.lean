module

public import CFSG.Quasithin.Background.JonesParshallG2Module
public import CFSG.Quasithin.Background.JonesParshallSL3Perfect

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix Matrix.SpecialLinearGroup CFSG.Quasithin.Explicit CFSG.Open

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem gAFun_diag3 {a b e : F} (h : a * b * e = 1) (r u₀ u₁ u₂ v₀ v₁ v₂ s : F) :
    gAFun ((diag3 a b e h : SL3 F) : Matrix (Fin 3) (Fin 3) F) (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s) =
      zmk r (a * u₀) (b * u₁) (e * u₂) (b * e * v₀) (a * e * v₁) (a * b * v₂) s := by
  have hD : ((diag3 a b e h : SL3 F) : Matrix (Fin 3) (Fin 3) F) = diagonal ![a, b, e] := rfl
  rw [gAFun_zmk, hD, adjugate_fin_three]
  apply zmk_congr <;> simp

theorem g2Act_diag3 {a b e : F} (h : a * b * e = 1) (u₀ u₁ u₂ v₀ v₁ v₂ : F) :
    g2Act (g2A (diag3 a b e h)) (q6 u₀ u₁ u₂ v₀ v₁ v₂) =
      q6 (a * u₀) (b * u₁) (e * u₂) (b * e * v₀) (a * e * v₁) (a * b * v₂) := by
  rw [g2Act_apply, zI_q6]
  change zP (gAFun _ _) = _
  rw [gAFun_diag3, zP_zmk]

theorem g2Act_g2A (A : SL3 F) (u₀ u₁ u₂ v₀ v₁ v₂ : F) :
    g2Act (g2A A) (q6 u₀ u₁ u₂ v₀ v₁ v₂) =
      q6 ((A : Matrix (Fin 3) (Fin 3) F) 0 0 * u₀ + (A : Matrix (Fin 3) (Fin 3) F) 0 1 * u₁ +
          (A : Matrix (Fin 3) (Fin 3) F) 0 2 * u₂)
        ((A : Matrix (Fin 3) (Fin 3) F) 1 0 * u₀ + (A : Matrix (Fin 3) (Fin 3) F) 1 1 * u₁ +
          (A : Matrix (Fin 3) (Fin 3) F) 1 2 * u₂)
        ((A : Matrix (Fin 3) (Fin 3) F) 2 0 * u₀ + (A : Matrix (Fin 3) (Fin 3) F) 2 1 * u₁ +
          (A : Matrix (Fin 3) (Fin 3) F) 2 2 * u₂)
        (adjugate (A : Matrix (Fin 3) (Fin 3) F) 0 0 * v₀ +
          adjugate (A : Matrix (Fin 3) (Fin 3) F) 1 0 * v₁ +
          adjugate (A : Matrix (Fin 3) (Fin 3) F) 2 0 * v₂)
        (adjugate (A : Matrix (Fin 3) (Fin 3) F) 0 1 * v₀ +
          adjugate (A : Matrix (Fin 3) (Fin 3) F) 1 1 * v₁ +
          adjugate (A : Matrix (Fin 3) (Fin 3) F) 2 1 * v₂)
        (adjugate (A : Matrix (Fin 3) (Fin 3) F) 0 2 * v₀ +
          adjugate (A : Matrix (Fin 3) (Fin 3) F) 1 2 * v₁ +
          adjugate (A : Matrix (Fin 3) (Fin 3) F) 2 2 * v₂) := by
  rw [g2Act_apply, zI_q6]
  change zP (gAFun _ _) = _
  rw [gAFun_zmk, zP_zmk]

omit [CharP F 2] in
theorem diag3_torus_prod (c d : Fˣ) : (c : F) * (d : F) * ((c : F) * (d : F))⁻¹ = 1 :=
  mul_inv_cancel₀ (mul_ne_zero c.ne_zero d.ne_zero)

@[expose] def sl3Torus : Fˣ × Fˣ →* SL3 F where
  toFun s := diag3 (s.1 : F) (s.2 : F) (((s.1 : F) * (s.2 : F))⁻¹) (diag3_torus_prod s.1 s.2)
  map_one' := by
    apply Subtype.ext
    change diagonal ![(1 : F), 1, (1 * 1)⁻¹] = 1
    rw [mul_one, inv_one, ← diagonal_one]
    congr 1
    funext k
    fin_cases k <;> rfl
  map_mul' s t := by
    rw [diag3_mul _ _ (by
      have := diag3_torus_prod (s.1 * t.1) (s.2 * t.2)
      simp only [Units.val_mul] at this ⊢
      rw [← this]
      field_simp)]
    exact diag3_congr (by simp) (by simp) (by simp; ring)

@[expose] def g2T : Fˣ × Fˣ →* ↥(cayleyGroup F) := g2A.comp sl3Torus

omit [CharP F 2] in
theorem g2T_apply (s : Fˣ × Fˣ) :
    g2T s = g2A (diag3 (s.1 : F) (s.2 : F) (((s.1 : F) * (s.2 : F))⁻¹)
      (diag3_torus_prod s.1 s.2)) := rfl

@[expose] def TEquiv (ψ : ↥(cayleyGroup F) → (Ix3 → F)) : Prop :=
  ψ ∈ Z1A (g2Act (F := F)) ∧ ∀ (s : Fˣ × Fˣ) (g : ↥(cayleyGroup F)),
    ψ (g2T s * g * (g2T s)⁻¹) = g2Act (g2T s) (ψ g)

theorem fixed_eq_zero {a b e : F} (h : a * b * e = 1) (ha : a ≠ 1) (hb : b ≠ 1) (he : e ≠ 1)
    (hbe : b * e ≠ 1) (hae : a * e ≠ 1) (hab : a * b ≠ 1) {w : Ix3 → F}
    (hw : g2Act (g2A (diag3 a b e h)) w = w) : w = 0 := by
  rw [q6_eta w, g2Act_diag3] at hw
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := q6_inj hw
  have k : ∀ {x y : F}, x ≠ 1 → x * y = y → y = 0 := fun {x y} hx hxy => by
    have : (x - 1) * y = 0 := by linear_combination hxy
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hx)
  rw [q6_eta w, k ha h1, k hb h2, k he h3, k hbe h4, k hae h5, k hab h6, q6_zero]

theorem sq_ne_one {c : F} (hc1 : c ≠ 1) : c ^ 2 ≠ 1 := by
  intro h
  apply hc1
  have : (c + 1) ^ 2 = 0 := by rw [add_sq_F, one_pow, h, CharTwo.add_self_eq_zero]
  exact CharTwo.add_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)

omit [CharP F 2] in
theorem inv_ne_one' {c : F} (hc1 : c ≠ 1) : c⁻¹ ≠ 1 := fun h => hc1 (inv_eq_one.mp h)

theorem fix_of_commute {ψ : ↥(cayleyGroup F) → (Ix3 → F)} (hψ : ψ ∈ Z1A (g2Act (F := F)))
    {g g' : ↥(cayleyGroup F)} (hc : g' * g = g * g') (h0 : ψ g' = 0) :
    g2Act g' (ψ g) = ψ g := by
  have e1 := hψ g' g
  have e2 := hψ g g'
  rw [hc, e2, h0, map_zero, add_zero, zero_add] at e1
  exact e1.symm

@[expose] def tCC (c : Fˣ) : Fˣ × Fˣ := (c, c)

namespace TEquiv

variable {ψ : ↥(cayleyGroup F) → (Ix3 → F)} (hψ : TEquiv ψ)
include hψ

theorem conj_fix {s : Fˣ × Fˣ} {g : ↥(cayleyGroup F)} (hc : g2T s * g = g * g2T s) :
    g2Act (g2T s) (ψ g) = ψ g := by
  rw [← hψ.2 s g, hc, mul_inv_cancel_right]

theorem torus_eq_zero {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (s : Fˣ × Fˣ) : ψ (g2T s) = 0 := by
  set c' : Fˣ := Units.mk0 c hc0
  have hfix := hψ.conj_fix (s := (c', c')) (g := g2T s) (by rw [← map_mul, ← map_mul, mul_comm])
  rw [g2T_apply] at hfix
  have hcc : c * c ≠ 1 := by rw [← sq]; exact sq_ne_one hc1
  have hci : c * (c * c)⁻¹ = c⁻¹ := by field_simp
  refine fixed_eq_zero _ hc1 hc1 (inv_ne_one' hcc) (by rw [hci]; exact inv_ne_one' hc1)
    (by rw [hci]; exact inv_ne_one' hc1) hcc hfix

end TEquiv

@[expose] def sl3P : SL3 F :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by simp [det_fin_three, CharTwo.neg_eq]⟩

@[expose] def gW : ↥(cayleyGroup F) := g2X ![1, 0, 0] * g2Y ![1, 0, 0] * g2X ![1, 0, 0]

@[expose] def gN : ↥(cayleyGroup F) := g2A sl3P * gW

theorem gW_fun_x (x : quasithinZorn F) :
    xaFun ![1, 0, 0] (ybFun ![1, 0, 0] (xaFun ![1, 0, 0] (xaFun ![1, 0, 0] x))) =
      ybFun ![1, 0, 0] (xaFun ![1, 0, 0] (ybFun ![1, 0, 0] (xaFun ![1, 0, 0] x))) := by
  rw [zorn_eta x]
  simp only [xaFun_zmk, ybFun_zmk]
  apply zmk_congr <;> simp <;> ring_nf <;> reduce_mod_char!

theorem gW_mul_g2X :
    gW * g2X (![1, 0, 0] : Fin 3 → F) = g2Y (![1, 0, 0] : Fin 3 → F) * gW := by
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  change cgE (gW * g2X (![1, 0, 0] : Fin 3 → F)) x = cgE (g2Y (![1, 0, 0] : Fin 3 → F) * gW) x
  simp only [gW, cg_mul_apply, cgE, g2X_apply, g2Y_apply]
  exact gW_fun_x x

theorem gW_fun_torus {c d : F} (hc : c ≠ 0) (hd : d ≠ 0) (x : quasithinZorn F) :
    xaFun ![1, 0, 0] (ybFun ![1, 0, 0] (xaFun ![1, 0, 0]
      (gAFun ((diag3 c d (c * d)⁻¹ (mul_inv_cancel₀ (mul_ne_zero hc hd)) : SL3 F) :
        Matrix (Fin 3) (Fin 3) F) x))) =
      gAFun ((diag3 (d * (c * d)⁻¹) (c * d) (c * (c * d)⁻¹) (by field_simp) : SL3 F) :
        Matrix (Fin 3) (Fin 3) F) (xaFun ![1, 0, 0] (ybFun ![1, 0, 0] (xaFun ![1, 0, 0] x))) := by
  rw [zorn_eta x]
  simp only [xaFun_zmk, ybFun_zmk, gAFun_diag3]
  apply zmk_congr
  all_goals (try simp)
  all_goals (try field_simp)
  all_goals (try ring_nf)
  all_goals (try reduce_mod_char!)
  all_goals (try simp)

theorem gW_mul_torus {c d : F} (hc : c ≠ 0) (hd : d ≠ 0) :
    gW * g2A (diag3 c d (c * d)⁻¹ (mul_inv_cancel₀ (mul_ne_zero hc hd))) =
      g2A (diag3 (d * (c * d)⁻¹) (c * d) (c * (c * d)⁻¹) (by field_simp)) * gW := by
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  change cgE (gW * g2A (diag3 c d (c * d)⁻¹ (mul_inv_cancel₀ (mul_ne_zero hc hd)))) x =
    cgE (g2A (diag3 (d * (c * d)⁻¹) (c * d) (c * (c * d)⁻¹) (by field_simp)) * gW) x
  simp only [gW, cg_mul_apply, cgE, g2X_apply, g2Y_apply, g2A_apply]
  exact gW_fun_torus hc hd x

theorem sl3P_mul_diag3 {a b e : F} (h : a * b * e = 1) (h' : b * a * e = 1) :
    sl3P * diag3 a b e h = diag3 b a e h' * sl3P := by
  apply Subtype.ext
  change !![(0 : F), 1, 0; 1, 0, 0; 0, 0, 1] * diagonal ![a, b, e] =
    diagonal ![b, a, e] * !![(0 : F), 1, 0; 1, 0, 0; 0, 0, 1]
  ext k l
  fin_cases k <;> fin_cases l <;> simp [mul_apply, Fin.sum_univ_three]

theorem adj_sl3P_e0 :
    (adjugate ((sl3P : SL3 F) : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ ![1, 0, 0] = ![0, 1, 0] := by
  change (adjugate !![(0 : F), 1, 0; 1, 0, 0; 0, 0, 1])ᵀ *ᵥ ![1, 0, 0] = ![0, 1, 0]
  rw [adjugate_fin_three]
  funext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three, CharTwo.neg_eq]

theorem gN_conj_g2X :
    gN * g2X (![1, 0, 0] : Fin 3 → F) * gN⁻¹ = g2Y (![0, 1, 0] : Fin 3 → F) := by
  have e1 : gN * g2X (![1, 0, 0] : Fin 3 → F) * gN⁻¹ =
      g2A sl3P * (gW * g2X (![1, 0, 0] : Fin 3 → F)) * gW⁻¹ * (g2A sl3P)⁻¹ := by
    rw [gN]
    group
  rw [e1, gW_mul_g2X]
  have e2 : g2A sl3P * (g2Y (![1, 0, 0] : Fin 3 → F) * gW) * gW⁻¹ * (g2A sl3P)⁻¹ =
      g2A sl3P * g2Y (![1, 0, 0] : Fin 3 → F) * (g2A sl3P)⁻¹ := by group
  rw [e2, g2A_mul_g2Y, adj_sl3P_e0, mul_inv_cancel_right]

theorem gN_conj_torus {c d : F} (hc : c ≠ 0) (hd : d ≠ 0) :
    gN * g2A (diag3 c d (c * d)⁻¹ (mul_inv_cancel₀ (mul_ne_zero hc hd))) * gN⁻¹ =
      g2A (diag3 (c * d) (d * (c * d)⁻¹) (c * (c * d)⁻¹) (by field_simp)) := by
  have e1 : gN * g2A (diag3 c d (c * d)⁻¹ (mul_inv_cancel₀ (mul_ne_zero hc hd))) * gN⁻¹ =
      g2A sl3P * (gW * g2A (diag3 c d (c * d)⁻¹ (mul_inv_cancel₀ (mul_ne_zero hc hd)))) *
        gW⁻¹ * (g2A sl3P)⁻¹ := by
    rw [gN]
    group
  rw [e1, gW_mul_torus hc hd]
  have e2 : g2A sl3P * (g2A (diag3 (d * (c * d)⁻¹) (c * d) (c * (c * d)⁻¹) (by field_simp)) *
      gW) * gW⁻¹ * (g2A sl3P)⁻¹ = g2A (sl3P * diag3 (d * (c * d)⁻¹) (c * d) (c * (c * d)⁻¹)
        (by field_simp)) * (g2A sl3P)⁻¹ := by
    rw [map_mul]
    group
  rw [e2, sl3P_mul_diag3 _ (by field_simp), map_mul, mul_inv_cancel_right]

namespace TEquiv

variable {ψ : ↥(cayleyGroup F) → (Ix3 → F)} (hψ : TEquiv ψ)
include hψ

theorem gN_eq_zero {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) : ψ gN = 0 := by
  have hT : g2T (Units.mk0 c hc0, Units.mk0 c hc0) =
      g2A (diag3 c c (c * c)⁻¹ (mul_inv_cancel₀ (mul_ne_zero hc0 hc0))) := rfl
  have h0 : ψ (g2A (diag3 c c (c * c)⁻¹ (mul_inv_cancel₀ (mul_ne_zero hc0 hc0)))) = 0 := by
    rw [← hT]
    exact hψ.torus_eq_zero hc0 hc1 _
  have hci : c * (c * c)⁻¹ = c⁻¹ := by field_simp
  have hT1 : g2T (Units.mk0 (c * c) (mul_ne_zero hc0 hc0),
      Units.mk0 (c * (c * c)⁻¹) (by rw [hci]; exact inv_ne_zero hc0)) =
      g2A (diag3 (c * c) (c * (c * c)⁻¹) (c * (c * c)⁻¹) (by field_simp)) := by
    rw [g2T_apply]
    congr 1
    exact diag3_congr rfl rfl (by simp only [Units.val_mk0]; field_simp)
  have h1 : ψ (g2A (diag3 (c * c) (c * (c * c)⁻¹) (c * (c * c)⁻¹) (by field_simp))) = 0 := by
    rw [← hT1]
    exact hψ.torus_eq_zero hc0 hc1 _
  have e := Z1A_conj hψ.1 gN (g2A (diag3 c c (c * c)⁻¹ (mul_inv_cancel₀ (mul_ne_zero hc0 hc0))))
  rw [gN_conj_torus hc0 hc0, h1, h0, map_zero, zero_add] at e
  have hfix : g2Act (g2A (diag3 (c * c) (c * (c * c)⁻¹) (c * (c * c)⁻¹) (by field_simp)))
      (ψ gN) = ψ gN := by
    have := sub_eq_zero.mp e.symm
    exact this.symm
  have hcc : c * c ≠ 1 := by rw [← sq]; exact sq_ne_one hc1
  refine fixed_eq_zero _ hcc (by rw [hci]; exact inv_ne_one' hc1)
    (by rw [hci]; exact inv_ne_one' hc1) ?_ ?_ ?_ hfix
  · rw [hci, ← mul_inv]
    exact inv_ne_one' (by rw [← sq]; exact sq_ne_one hc1)
  · rw [hci]
    intro h
    exact hc1 (by field_simp at h; exact h)
  · rw [hci]
    intro h
    exact hc1 (by field_simp at h; exact h)

end TEquiv

end CFSG.Quasithin.JonesParshall
