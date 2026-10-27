module

public import CFSG.Quasithin.Background.JonesParshallG2

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Quasithin.Explicit CFSG.Open

variable {F : Type} [Field F]

@[expose] def zU0 (F : Type) [Field F] : quasithinZorn F := zmk 0 1 0 0 0 0 0 0

@[expose] def zE (F : Type) [Field F] : quasithinZorn F := zmk 1 0 0 0 0 0 0 0

@[expose] def zE' (F : Type) [Field F] : quasithinZorn F := zmk 0 0 0 0 0 0 0 1

theorem mul_zU0_left (t x₀ x₁ x₂ y₀ y₁ y₂ z : F) :
    cayleyMul (zU0 F) (zmk t x₀ x₁ x₂ y₀ y₁ y₂ z) = zmk y₀ z 0 0 0 (-x₂) x₁ 0 := by
  rw [zU0, cayleyMul_zmk]
  apply zmk_congr <;> ring

theorem mul_zU0_right (t x₀ x₁ x₂ y₀ y₁ y₂ z : F) :
    cayleyMul (zmk t x₀ x₁ x₂ y₀ y₁ y₂ z) (zU0 F) = zmk 0 t 0 0 0 x₂ (-x₁) y₀ := by
  rw [zU0, cayleyMul_zmk]
  apply zmk_congr <;> ring

theorem mul_zE_left (t x₀ x₁ x₂ y₀ y₁ y₂ z : F) :
    cayleyMul (zE F) (zmk t x₀ x₁ x₂ y₀ y₁ y₂ z) = zmk t x₀ x₁ x₂ 0 0 0 0 := by
  rw [zE, cayleyMul_zmk]
  apply zmk_congr <;> ring

theorem mul_zE_right (t x₀ x₁ x₂ y₀ y₁ y₂ z : F) :
    cayleyMul (zmk t x₀ x₁ x₂ y₀ y₁ y₂ z) (zE F) = zmk t 0 0 0 y₀ y₁ y₂ 0 := by
  rw [zE, cayleyMul_zmk]
  apply zmk_congr <;> ring

theorem mul_zE'_left (t x₀ x₁ x₂ y₀ y₁ y₂ z : F) :
    cayleyMul (zE' F) (zmk t x₀ x₁ x₂ y₀ y₁ y₂ z) = zmk 0 0 0 0 y₀ y₁ y₂ z := by
  rw [zE', cayleyMul_zmk]
  apply zmk_congr <;> ring

theorem mul_zE'_right (t x₀ x₁ x₂ y₀ y₁ y₂ z : F) :
    cayleyMul (zmk t x₀ x₁ x₂ y₀ y₁ y₂ z) (zE' F) = zmk 0 x₀ x₁ x₂ 0 0 0 z := by
  rw [zE', cayleyMul_zmk]
  apply zmk_congr <;> ring

theorem zmk_decomp (r u₀ u₁ u₂ v₀ v₁ v₂ s : F) :
    zmk r u₀ u₁ u₂ v₀ v₁ v₂ s = r • zmk 1 0 0 0 0 0 0 0 + u₀ • zmk 0 1 0 0 0 0 0 0 +
      u₁ • zmk 0 0 1 0 0 0 0 0 + u₂ • zmk 0 0 0 1 0 0 0 0 + v₀ • zmk 0 0 0 0 1 0 0 0 +
      v₁ • zmk 0 0 0 0 0 1 0 0 + v₂ • zmk 0 0 0 0 0 0 1 0 + s • zmk 0 0 0 0 0 0 0 1 := by
  simp only [zmk_smul, zmk_add, mul_one, mul_zero, add_zero, zero_add]

theorem zorn_linearMap_ext {φ ψ : quasithinZorn F →ₗ[F] quasithinZorn F}
    (h1 : φ (zmk 1 0 0 0 0 0 0 0) = ψ (zmk 1 0 0 0 0 0 0 0))
    (h2 : φ (zmk 0 1 0 0 0 0 0 0) = ψ (zmk 0 1 0 0 0 0 0 0))
    (h3 : φ (zmk 0 0 1 0 0 0 0 0) = ψ (zmk 0 0 1 0 0 0 0 0))
    (h4 : φ (zmk 0 0 0 1 0 0 0 0) = ψ (zmk 0 0 0 1 0 0 0 0))
    (h5 : φ (zmk 0 0 0 0 1 0 0 0) = ψ (zmk 0 0 0 0 1 0 0 0))
    (h6 : φ (zmk 0 0 0 0 0 1 0 0) = ψ (zmk 0 0 0 0 0 1 0 0))
    (h7 : φ (zmk 0 0 0 0 0 0 1 0) = ψ (zmk 0 0 0 0 0 0 1 0))
    (h8 : φ (zmk 0 0 0 0 0 0 0 1) = ψ (zmk 0 0 0 0 0 0 0 1)) : φ = ψ := by
  refine LinearMap.ext fun x => ?_
  rw [zorn_eta x, zmk_decomp]
  simp only [map_add, map_smul, h1, h2, h3, h4, h5, h6, h7, h8]

theorem gAFun_zmk (A : Matrix (Fin 3) (Fin 3) F) (r u₀ u₁ u₂ v₀ v₁ v₂ s : F) :
    gAFun A (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s) =
      zmk r (A 0 0 * u₀ + A 0 1 * u₁ + A 0 2 * u₂) (A 1 0 * u₀ + A 1 1 * u₁ + A 1 2 * u₂)
        (A 2 0 * u₀ + A 2 1 * u₁ + A 2 2 * u₂)
        (adjugate A 0 0 * v₀ + adjugate A 1 0 * v₁ + adjugate A 2 0 * v₂)
        (adjugate A 0 1 * v₀ + adjugate A 1 1 * v₁ + adjugate A 2 1 * v₂)
        (adjugate A 0 2 * v₀ + adjugate A 1 2 * v₁ + adjugate A 2 2 * v₂) s := by
  simp only [gAFun, zmk, Prod.mk.injEq]
  refine ⟨trivial, ?_, ?_, trivial⟩ <;> funext i <;> fin_cases i <;>
    simp [mulVec, dotProduct, Fin.sum_univ_three]

abbrev cgE (g : ↥(cayleyGroup F)) : quasithinZorn F ≃ₗ[F] quasithinZorn F := g

theorem cg_mul (g : ↥(cayleyGroup F)) (x y : quasithinZorn F) :
    cgE g (cayleyMul x y) = cayleyMul (cgE g x) (cgE g y) := g.2.2.1 x y

theorem cg_one (g : ↥(cayleyGroup F)) : cgE g (cayleyOne F) = cayleyOne F := g.2.1

theorem cg_tr (g : ↥(cayleyGroup F)) (x : quasithinZorn F) : cayleyTr (cgE g x) = cayleyTr x :=
  g.2.2.2.1 x

theorem cg_norm (g : ↥(cayleyGroup F)) (x : quasithinZorn F) :
    cayleyNorm (cgE g x) = cayleyNorm x := g.2.2.2.2 x

theorem cg_mul_apply (a b : ↥(cayleyGroup F)) (x : quasithinZorn F) :
    cgE (a * b) x = cgE a (cgE b x) := rfl

theorem cg_inv_apply (a : ↥(cayleyGroup F)) (x : quasithinZorn F) : cgE a⁻¹ (cgE a x) = x := by
  rw [← cg_mul_apply, inv_mul_cancel]
  rfl

theorem form_of_peirceU {y : quasithinZorn F} (h1 : cayleyMul (zE F) y = y)
    (h2 : cayleyMul y (zE' F) = y) :
    y = zmk 0 (y.2.1 0) (y.2.1 1) (y.2.1 2) 0 0 0 0 := by
  rw [zorn_eta y, mul_zE_left] at h1
  rw [zorn_eta y, mul_zE'_right] at h2
  obtain ⟨-, -, -, -, h5, h6, h7, h8⟩ := zmk_inj h1
  obtain ⟨g1, -, -, -, -, -, -, -⟩ := zmk_inj h2
  rw [zorn_eta y]
  exact zmk_congr g1.symm rfl rfl rfl h5.symm h6.symm h7.symm h8.symm

theorem form_of_peirceV {y : quasithinZorn F} (h1 : cayleyMul (zE' F) y = y)
    (h2 : cayleyMul y (zE F) = y) :
    y = zmk 0 0 0 0 (y.2.2.1 0) (y.2.2.1 1) (y.2.2.1 2) 0 := by
  rw [zorn_eta y, mul_zE'_left] at h1
  rw [zorn_eta y, mul_zE_right] at h2
  obtain ⟨h1', h2', h3', h4', -, -, -, -⟩ := zmk_inj h1
  obtain ⟨-, -, -, -, -, -, -, g8⟩ := zmk_inj h2
  rw [zorn_eta y]
  exact zmk_congr h1'.symm h2'.symm h3'.symm h4'.symm rfl rfl rfl g8.symm

variable [CharP F 2]

theorem uW_zE (α β γ : F) :
    cgE (g2X ![α, 0, 0] * g2Y ![0, β, γ]) (zE F) = zmk 1 α 0 0 0 β γ 0 := by
  rw [cg_mul_apply]
  change xaFun ![α, 0, 0] (ybFun ![0, β, γ] (zE F)) = _
  rw [zE, ybFun_zmk, xaFun_zmk]
  apply zmk_congr <;> simp

theorem uW_zU0 (α β γ : F) :
    cgE (g2X ![α, 0, 0] * g2Y ![0, β, γ]) (zU0 F) = zU0 F := by
  rw [cg_mul_apply]
  change xaFun ![α, 0, 0] (ybFun ![0, β, γ] (zU0 F)) = _
  rw [zU0, ybFun_zmk, xaFun_zmk]
  apply zmk_congr <;> simp

theorem eq_uW_mul_g2A {g : ↥(cayleyGroup F)} (hg : cgE g (zU0 F) = zU0 F) :
    ∃ (α β γ : F) (A : SL3 F), (A : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] ∧
      g = g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A A := by
  obtain ⟨p₁, p₂, p₃, p₄, p₅, p₆, p₇, p₈, hp⟩ : ∃ p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ : F,
      cgE g (zE F) = zmk p₁ p₂ p₃ p₄ p₅ p₆ p₇ p₈ := ⟨_, _, _, _, _, _, _, _, zorn_eta _⟩
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈, hq⟩ : ∃ q₁ q₂ q₃ q₄ q₅ q₆ q₇ q₈ : F,
      cgE g (zE' F) = zmk q₁ q₂ q₃ q₄ q₅ q₆ q₇ q₈ := ⟨_, _, _, _, _, _, _, _, zorn_eta _⟩
  have hUE : cayleyMul (zU0 F) (zE F) = 0 := by
    rw [zE, mul_zU0_left, ← zmk_zero]
    apply zmk_congr <;> simp
  have hE'U : cayleyMul (zE' F) (zU0 F) = 0 := by
    rw [zE', mul_zU0_right, ← zmk_zero]
    apply zmk_congr <;> simp
  have e1 := cg_mul g (zU0 F) (zE F)
  rw [hUE, map_zero, hg, hp, mul_zU0_left, ← zmk_zero] at e1
  obtain ⟨hp5, hp8, -, -, -, hp4, hp3, -⟩ := zmk_inj e1
  have e2 := cg_mul g (zE' F) (zU0 F)
  rw [hE'U, map_zero, hg, hq, mul_zU0_right, ← zmk_zero] at e2
  obtain ⟨-, hq1, -, -, -, hq4, hq3, hq5⟩ := zmk_inj e2
  have hsum : zE F + zE' F = cayleyOne F := by
    rw [zE, zE', zmk_add, cayleyOne_eq]
    apply zmk_congr <;> simp
  have e3 : cgE g (zE F) + cgE g (zE' F) = cayleyOne F := by
    rw [← map_add, hsum, cg_one]
  rw [hp, hq, zmk_add, cayleyOne_eq] at e3
  obtain ⟨hp1, -, -, -, -, -, -, -⟩ := zmk_inj e3
  have hp1' : p₁ = 1 := by rw [← hp1, ← hq1, add_zero]
  set u := g2X ![p₂, 0, 0] * g2Y ![0, p₆, p₇] with hu
  set h := u⁻¹ * g with hh
  have hp4' : p₄ = 0 := neg_eq_zero.mp hp4.symm
  have hgE : cgE g (zE F) = cgE u (zE F) := by
    rw [hp, hu, uW_zE, hp1', ← hp3, hp4', ← hp5, ← hp8]
  have hhE : cgE h (zE F) = zE F := by
    rw [hh, cg_mul_apply, hgE, cg_inv_apply]
  have hhU : cgE h (zU0 F) = zU0 F := by
    rw [hh, cg_mul_apply, hg]
    conv_lhs => rw [← uW_zU0 p₂ p₆ p₇]
    rw [← hu, cg_inv_apply]
  have hE' : zE' F = cayleyOne F - zE F := by
    rw [← hsum]
    abel
  have hhE' : cgE h (zE' F) = zE' F := by
    rw [hE', map_sub, cg_one, hhE]
  have hpU : ∀ x : quasithinZorn F, cayleyMul (zE F) x = x → cayleyMul x (zE' F) = x →
      cgE h x = zmk 0 ((cgE h x).2.1 0) ((cgE h x).2.1 1) ((cgE h x).2.1 2) 0 0 0 0 := by
    intro x h1 h2
    refine form_of_peirceU ?_ ?_
    · rw [← hhE, ← cg_mul, h1]
    · rw [← hhE', ← cg_mul, h2]
  have hU : ∀ j : Fin 3, cgE h (zmk 0 (if j = 0 then 1 else 0) (if j = 1 then 1 else 0)
      (if j = 2 then 1 else 0) 0 0 0 0) = zmk 0 ((cgE h (zmk 0 (if j = 0 then 1 else 0)
        (if j = 1 then 1 else 0) (if j = 2 then 1 else 0) 0 0 0 0)).2.1 0)
        ((cgE h (zmk 0 (if j = 0 then 1 else 0) (if j = 1 then 1 else 0)
          (if j = 2 then 1 else 0) 0 0 0 0)).2.1 1)
        ((cgE h (zmk 0 (if j = 0 then 1 else 0) (if j = 1 then 1 else 0)
          (if j = 2 then 1 else 0) 0 0 0 0)).2.1 2) 0 0 0 0 := fun j => by
    refine hpU _ ?_ ?_
    · rw [mul_zE_left]
    · rw [mul_zE'_right]
  set A : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j => (cgE h (zmk 0 (if j = 0 then 1 else 0)
    (if j = 1 then 1 else 0) (if j = 2 then 1 else 0) 0 0 0 0)).2.1 i with hA
  have hU0 : cgE h (zmk 0 1 0 0 0 0 0 0) = zmk 0 (A 0 0) (A 1 0) (A 2 0) 0 0 0 0 := hU 0
  have hU1 : cgE h (zmk 0 0 1 0 0 0 0 0) = zmk 0 (A 0 1) (A 1 1) (A 2 1) 0 0 0 0 := hU 1
  have hU2 : cgE h (zmk 0 0 0 1 0 0 0 0) = zmk 0 (A 0 2) (A 1 2) (A 2 2) 0 0 0 0 := hU 2
  have hV0 : cgE h (zmk 0 0 0 0 1 0 0 0) = cayleyMul (zmk 0 (A 0 1) (A 1 1) (A 2 1) 0 0 0 0)
      (zmk 0 (A 0 2) (A 1 2) (A 2 2) 0 0 0 0) := by
    have e : zmk (0 : F) 0 0 0 1 0 0 0 = cayleyMul (zmk 0 0 1 0 0 0 0 0) (zmk 0 0 0 1 0 0 0 0) := by
      rw [cayleyMul_zmk]
      apply zmk_congr <;> ring
    rw [e, cg_mul, hU1, hU2]
  have hV1 : cgE h (zmk 0 0 0 0 0 1 0 0) = cayleyMul (zmk 0 (A 0 2) (A 1 2) (A 2 2) 0 0 0 0)
      (zmk 0 (A 0 0) (A 1 0) (A 2 0) 0 0 0 0) := by
    have e : zmk (0 : F) 0 0 0 0 1 0 0 = cayleyMul (zmk 0 0 0 1 0 0 0 0) (zmk 0 1 0 0 0 0 0 0) := by
      rw [cayleyMul_zmk]
      apply zmk_congr <;> ring
    rw [e, cg_mul, hU2, hU0]
  have hV2 : cgE h (zmk 0 0 0 0 0 0 1 0) = cayleyMul (zmk 0 (A 0 0) (A 1 0) (A 2 0) 0 0 0 0)
      (zmk 0 (A 0 1) (A 1 1) (A 2 1) 0 0 0 0) := by
    have e : zmk (0 : F) 0 0 0 0 0 1 0 = cayleyMul (zmk 0 1 0 0 0 0 0 0) (zmk 0 0 1 0 0 0 0 0) := by
      rw [cayleyMul_zmk]
      apply zmk_congr <;> ring
    rw [e, cg_mul, hU0, hU1]
  have hlin : (cgE h).toLinearMap = gALin A := by
    refine zorn_linearMap_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · change cgE h (zE F) = gAFun A (zmk 1 0 0 0 0 0 0 0)
      rw [hhE, gAFun_zmk, zE]
      apply zmk_congr <;> ring
    · change cgE h (zmk 0 1 0 0 0 0 0 0) = gAFun A (zmk 0 1 0 0 0 0 0 0)
      rw [hU0, gAFun_zmk]
      apply zmk_congr <;> ring
    · change cgE h (zmk 0 0 1 0 0 0 0 0) = gAFun A (zmk 0 0 1 0 0 0 0 0)
      rw [hU1, gAFun_zmk]
      apply zmk_congr <;> ring
    · change cgE h (zmk 0 0 0 1 0 0 0 0) = gAFun A (zmk 0 0 0 1 0 0 0 0)
      rw [hU2, gAFun_zmk]
      apply zmk_congr <;> ring
    · change cgE h (zmk 0 0 0 0 1 0 0 0) = gAFun A (zmk 0 0 0 0 1 0 0 0)
      rw [hV0, gAFun_zmk, cayleyMul_zmk, adjugate_fin_three]
      apply zmk_congr <;> simp <;> ring
    · change cgE h (zmk 0 0 0 0 0 1 0 0) = gAFun A (zmk 0 0 0 0 0 1 0 0)
      rw [hV1, gAFun_zmk, cayleyMul_zmk, adjugate_fin_three]
      apply zmk_congr <;> simp <;> ring
    · change cgE h (zmk 0 0 0 0 0 0 1 0) = gAFun A (zmk 0 0 0 0 0 0 1 0)
      rw [hV2, gAFun_zmk, cayleyMul_zmk, adjugate_fin_three]
      apply zmk_congr <;> simp <;> ring
    · change cgE h (zE' F) = gAFun A (zmk 0 0 0 0 0 0 0 1)
      rw [hhE', gAFun_zmk, zE']
      apply zmk_congr <;> ring
  have happ : ∀ x, cgE h x = gAFun A x := fun x => LinearMap.congr_fun hlin x
  have hdet : A.det = 1 := by
    have e := cg_norm h (zmk 0 1 0 0 1 0 0 0)
    rw [happ, gAFun_zmk, cayleyNorm_zmk, cayleyNorm_zmk, adjugate_fin_three] at e
    rw [det_fin_three]
    simp at e
    linear_combination e
  have hAe : A *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
    have e := happ (zU0 F)
    rw [hhU, zU0, gAFun_zmk] at e
    obtain ⟨-, h1, h2, h3, -, -, -, -⟩ := zmk_inj e
    have hm : A *ᵥ ![1, 0, 0] = ![A 0 0, A 1 0, A 2 0] := by
      funext i
      fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three]
    simp only [mul_one, mul_zero, add_zero] at h1 h2 h3
    rw [hm, ← h1, ← h2, ← h3]
  refine ⟨p₂, p₆, p₇, ⟨A, hdet⟩, hAe, ?_⟩
  have hh' : h = g2A ⟨A, hdet⟩ := Subtype.ext (LinearEquiv.ext fun x => happ x)
  rw [← hh', hh, ← mul_assoc, mul_inv_cancel, one_mul]

end CFSG.Quasithin.JonesParshall
