module

public import CFSG.Quasithin.MS93.S33LamQ
public import CFSG.Quasithin.Background.JonesParshallSL2

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.Quasithin.JonesParshall MSP Matrix

variable {F : Type} [Field F]

theorem fixSp_eq_perp_commSp (Γ : Subgroup (Sp4 F)) : fixSp Γ = perp (commSp Γ) := by
  refine le_antisymm (fun v hv => ?_) (perp_commSp_le_fixSp Γ)
  rw [mem_perp]
  intro w hw
  have hle : commSp Γ ≤ LinearMap.ker ((form F).flip v) := by
    refine commSp_le_iff.2 fun a ha x => ?_
    rw [LinearMap.mem_ker]
    change form F (mat a *ᵥ x - x) v = 0
    rw [map_sub, LinearMap.sub_apply, ← form_mat a x v, hv a ha, sub_self]
  exact hle hw

theorem commSp_eq_perp_fixSp (Γ : Subgroup (Sp4 F)) : commSp Γ = perp (fixSp Γ) := by
  rw [fixSp_eq_perp_commSp, perp_perp]

theorem finrank_fixSp_le_three' {Γ : Subgroup (Sp4 F)} (hΓ : Γ ≠ ⊥) :
    Module.finrank F (fixSp Γ) ≤ 3 := by
  have hne : fixSp Γ ≠ ⊤ := by
    intro htop
    apply hΓ
    refine eq_bot_iff.2 fun g hg => ?_
    rw [Subgroup.mem_bot]
    refine ext_mulVec fun w => ?_
    have hw : w ∈ fixSp Γ := htop ▸ Submodule.mem_top
    rw [hw g hg, mat_one, one_mulVec]
  have h4 := Submodule.finrank_lt hne
  have hV : Module.finrank F (V4 F) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  omega

variable [Fintype F] [CharP F 2]

theorem mulVec_eq_of_commute_transv' {g : Sp4 F} {x : V4 F} (hx : x ≠ 0) {c : F} (hc : c ≠ 0)
    (h : g * transv x c = transv x c * g) : mat g *ᵥ x = x := by
  have hμ : sqrtF c ≠ 0 := fun h0 => hc (by rw [← sqrtF_sq c, h0, zero_pow two_ne_zero])
  have ht : transv x c = transv (sqrtF c • x) 1 := by
    rw [transv_smul_vec, sqrtF_sq, mul_one]
  rw [ht] at h
  have h1 := mulVec_eq_of_commute_transv (smul_ne_zero hμ hx) h
  rw [mulVec_smul] at h1
  exact smul_right_injective _ hμ h1

omit [Fintype F] in
theorem fix_of_xPoint_le {E : Subgroup (Sp4 F)} {p : Submodule F (V4 F)} (hp : IsPoint p)
    (hpE : xPoint p ≤ E) {g : Sp4 F} (hg : ∀ e ∈ E, g * e = e * g) {v : V4 F} (hv : v ∈ p) :
    mat g *ᵥ v = v := by
  obtain ⟨x, hx, rfl⟩ := exists_eq_span_of_isPoint hp
  have hgx := mulVec_eq_of_commute_transv hx (hg _ (hpE (transv_mem_xPoint x 1)))
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  rw [mulVec_smul, hgx]

omit [Fintype F] [CharP F 2] in
theorem levHom₁_wJ_mulVec_e₂ : mat (levHom₁ (wJ F)) *ᵥ e₂ F = e₁ F := by
  rw [mat_levHom₁]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [wJ, mulVec, dotProduct, Fin.sum_univ_two]

theorem mem_Q₁_of_commute {E : Subgroup (Sp4 F)} (hE : E ≤ Q₁ F)
    (hc : Nat.card F ^ 2 < Nat.card E) {y : Sp4 F} (hy : ∀ e ∈ E, y * e = e * y) :
    y ∈ Q₁ F := by
  obtain ⟨c, hc0, hcE⟩ := exists_transv_e₂_mem hE hc
  have hy2 : mat y *ᵥ e₂ F = e₂ F :=
    mulVec_eq_of_commute_transv' (by simp) hc0 (hy _ hcE)
  set w : Sp4 F := levHom₁ (wJ F)
  have hwP : w⁻¹ ∈ P₁ F := inv_mem (lev₁_le_P₁ ⟨wJ F, rfl⟩)
  have hwn : w⁻¹ ∈ Subgroup.normalizer (Q₁ F : Set (Sp4 F)) := by
    rw [normalizer_Q₁]
    exact hwP
  have hE' : E.map (MulAut.conj w⁻¹).toMonoidHom ≤ Q₁ F := by
    rintro _ ⟨e, he, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hwn e).1 (hE he)
  have hc' : Nat.card F ^ 2 < Nat.card (E.map (MulAut.conj w⁻¹).toMonoidHom) := by
    rwa [card_map_conj]
  obtain ⟨c', hc'0, hc'E⟩ := exists_transv_e₂_mem hE' hc'
  obtain ⟨e, he, hee⟩ := hc'E
  have he1 : e = transv (e₁ F) c' := by
    have h1 : w⁻¹ * e * w⁻¹⁻¹ = transv (e₂ F) c' := hee
    have h2 : e = w * transv (e₂ F) c' * w⁻¹ := by
      rw [← h1]
      group
    rw [h2, transv_conj, levHom₁_wJ_mulVec_e₂]
  have hy1 : mat y *ᵥ e₁ F = e₁ F :=
    mulVec_eq_of_commute_transv' (by simp) hc'0 (he1 ▸ hy e he)
  intro v hv
  obtain ⟨h0, h1⟩ := mem_ln₀.1 hv
  have hv' : v = v (.inl 0) • e₁ F + v (.inl 1) • e₂ F := by
    refine ext4 ?_ ?_ ?_ ?_ <;> simp [h0, h1]
  rw [hv', mulVec_add, mulVec_smul, mulVec_smul, hy1, hy2]

theorem mem_qLine_of_commute {l : Submodule F (V4 F)} (hl : IsLine l) {E : Subgroup (Sp4 F)}
    (hE : E ≤ qLine l) (hc : Nat.card F ^ 2 < Nat.card E) {y : Sp4 F}
    (hy : ∀ e ∈ E, y * e = e * y) : y ∈ qLine l := by
  obtain ⟨g, rfl⟩ := exists_map_ln₀_eq hl
  rw [qLine_map_eq] at hE ⊢
  have hE₀ : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ Q₁ F := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨e₀, he₀, rfl⟩ := hE he
    show g⁻¹ * (g * e₀ * g⁻¹) * g⁻¹⁻¹ ∈ Q₁ F
    have e : g⁻¹ * (g * e₀ * g⁻¹) * g⁻¹⁻¹ = e₀ := by group
    rw [e]
    exact he₀
  have hc₀ : Nat.card F ^ 2 < Nat.card (E.map (MulAut.conj g⁻¹).toMonoidHom) := by
    rwa [card_map_conj]
  have hy₀ : ∀ e ∈ E.map (MulAut.conj g⁻¹).toMonoidHom,
      (g⁻¹ * y * g) * e = e * (g⁻¹ * y * g) := by
    rintro _ ⟨e, he, rfl⟩
    show (g⁻¹ * y * g) * (g⁻¹ * e * g⁻¹⁻¹) = (g⁻¹ * e * g⁻¹⁻¹) * (g⁻¹ * y * g)
    have := hy e he
    calc (g⁻¹ * y * g) * (g⁻¹ * e * g⁻¹⁻¹) = g⁻¹ * (y * e) * g := by group
      _ = g⁻¹ * (e * y) * g := by rw [this]
      _ = (g⁻¹ * e * g⁻¹⁻¹) * (g⁻¹ * y * g) := by group
  have h := mem_Q₁_of_commute hE₀ hc₀ hy₀
  refine ⟨g⁻¹ * y * g, h, ?_⟩
  show g * (g⁻¹ * y * g) * g⁻¹ = y
  group

theorem sub_mem_commSp_of_commute {E E' : Subgroup (Sp4 F)} {p p' : Submodule F (V4 F)}
    (hp : IsPoint p) (hp' : IsPoint p') (hpE : xPoint p ≤ E) (hpE' : xPoint p' ≤ E')
    (hE2 : IsPGroup 2 E) (hEab : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x)
    (h1 : 2 * Nat.card (V4 F) ≤ Nat.card (fixSp E') * Nat.card E)
    (h2 : 2 * Nat.card (V4 F) ≤ Nat.card (fixSp E) * Nat.card E')
    {y : Sp4 F} (hy : ∀ e ∈ E, y * e = e * y) (v : V4 F) : mat y *ᵥ v - v ∈ commSp E := by
  set q := Nat.card F with hq
  have hq2 : 2 ≤ q := by
    have := Fintype.one_lt_card (α := F)
    rw [hq, Nat.card_eq_fintype_card]
    omega
  rw [card_V4] at h1 h2
  rw [card_fixSp] at h1 h2
  have hpfix : p ≤ fixSp E := fun x hx e he => fix_of_xPoint_le hp hpE (hEab e he) hx
  have hd1 : 1 ≤ Module.finrank F (fixSp E) := by
    have := Submodule.finrank_mono hpfix
    rw [hp] at this
    exact this
  have hne : ∀ {Δ : Subgroup (Sp4 F)} {r : Submodule F (V4 F)}, IsPoint r → xPoint r ≤ Δ →
      Δ ≠ ⊥ := by
    intro Δ r hr hrΔ hbot
    have hcard := card_xPoint hr
    have hle : Nat.card (xPoint r) ≤ Nat.card Δ := Subgroup.card_le_of_le hrΔ
    rw [hbot, Subgroup.card_bot, hcard] at hle
    omega
  have hd3 := finrank_fixSp_le_three' (hne hp hpE)
  have hd3' := finrank_fixSp_le_three' (hne hp' hpE')
  have hsmall : ∀ {Δ : Subgroup (Sp4 F)}, Module.finrank F (fixSp Δ) = 3 → Nat.card Δ ≤ q := by
    intro Δ hΔ
    obtain ⟨r, hr, -, hΔr⟩ := exists_point_of_finrank_fixSp_three hΔ
    exact (Subgroup.card_le_of_le hΔr).trans (card_xPoint hr).le
  have hd2 : Module.finrank F (fixSp E) ≤ 2 := by
    by_contra hd
    have h3 : Module.finrank F (fixSp E) = 3 := by omega
    have hEq := hsmall h3
    have : 2 * q ^ 4 ≤ q ^ 3 * q := by
      calc 2 * q ^ 4 ≤ q ^ Module.finrank F (fixSp E') * Nat.card E := h1
        _ ≤ q ^ 3 * q := Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hd3') hEq
    have h4 : q ^ 3 * q = q ^ 4 := by ring
    have hq4 : 0 < q ^ 4 := by positivity
    omega
  have hd2' : Module.finrank F (fixSp E') ≤ 2 := by
    by_contra hd
    have h3 : Module.finrank F (fixSp E') = 3 := by omega
    have hEq := hsmall h3
    have : 2 * q ^ 4 ≤ q ^ 3 * q := by
      calc 2 * q ^ 4 ≤ q ^ Module.finrank F (fixSp E) * Nat.card E' := h2
        _ ≤ q ^ 3 * q := Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hd3) hEq
    have h4 : q ^ 3 * q = q ^ 4 := by ring
    have hq4 : 0 < q ^ 4 := by positivity
    omega
  have hEc : q ^ 2 < Nat.card E := by
    have h3 : 2 * q ^ 4 ≤ q ^ 2 * Nat.card E :=
      h1.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hd2'))
    by_contra hlt
    push Not at hlt
    have : q ^ 2 * Nat.card E ≤ q ^ 2 * q ^ 2 := Nat.mul_le_mul_left _ hlt
    have h4 : q ^ 2 * q ^ 2 = q ^ 4 := by ring
    have hq4 : 0 < q ^ 4 := by positivity
    omega
  have hyp : ∀ x ∈ p, mat y *ᵥ x = x := fun x hx => fix_of_xPoint_le hp hpE hy hx
  rcases Nat.lt_or_ge (Module.finrank F (fixSp E)) 2 with hlt | hge
  ·
    have hfix : fixSp E = p := (Submodule.eq_of_le_of_finrank_eq hpfix (by rw [hp]; omega)).symm
    rw [commSp_eq_perp_fixSp, hfix, mem_perp]
    intro x hx
    rw [map_sub, ← form_mat y x v, hyp x hx, sub_self]
  ·
    obtain ⟨hl, hEl⟩ := isLine_fixSp_of_finrank_two hE2 (by omega)
    have hyl := mem_qLine_of_commute hl hEl hEc hy
    have hsub : mat y *ᵥ v - v ∈ fixSp E := commSp_qLine_le hl (sub_mem_commSp hyl v)
    rwa [commSp_eq_perp_fixSp, hl.perp_eq]

end CFSG.Quasithin.MS93.S33
