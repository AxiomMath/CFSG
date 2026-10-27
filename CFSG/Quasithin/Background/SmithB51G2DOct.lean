module

public import CFSG.Quasithin.Background.FFC2G2
public import CFSG.Quasithin.Background.P3G2Zorn

public section

namespace CFSG.Quasithin.B5.G2D

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Open

variable {F : Type} [Field F]

theorem cayleyPolar_zmk (r u₀ u₁ u₂ v₀ v₁ v₂ s t x₀ x₁ x₂ y₀ y₁ y₂ z : F) :
    cayleyPolar (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s) (zmk t x₀ x₁ x₂ y₀ y₁ y₂ z) =
      r * z + t * s + (u₀ * y₀ + x₀ * v₀ + (u₁ * y₁ + x₁ * v₁) + (u₂ * y₂ + x₂ * v₂)) := by
  rw [cayleyPolar_eq]
  simp [zmk, Fin.sum_univ_three]

theorem cayleyPolar_comm (x y : quasithinZorn F) : cayleyPolar x y = cayleyPolar y x := by
  rw [cayleyPolar_eq, cayleyPolar_eq]
  simp only [Fin.sum_univ_three]
  ring

theorem cayleyPolar_add_left (x x' y : quasithinZorn F) :
    cayleyPolar (x + x') y = cayleyPolar x y + cayleyPolar x' y := by
  rw [zorn_eta x, zorn_eta x', zorn_eta y, zmk_add]
  simp only [cayleyPolar_zmk]
  ring

theorem cayleyPolar_smul_left (c : F) (x y : quasithinZorn F) :
    cayleyPolar (c • x) y = c * cayleyPolar x y := by
  rw [zorn_eta x, zorn_eta y, zmk_smul]
  simp only [cayleyPolar_zmk]
  ring

theorem cayleyPolar_add_right (x y y' : quasithinZorn F) :
    cayleyPolar x (y + y') = cayleyPolar x y + cayleyPolar x y' := by
  rw [cayleyPolar_comm, cayleyPolar_add_left, cayleyPolar_comm, cayleyPolar_comm y']

theorem cayleyPolar_smul_right (c : F) (x y : quasithinZorn F) :
    cayleyPolar x (c • y) = c * cayleyPolar x y := by
  rw [cayleyPolar_comm, cayleyPolar_smul_left, cayleyPolar_comm]

theorem cayleyPolar_one_left (x : quasithinZorn F) : cayleyPolar (cayleyOne F) x = cayleyTr x := by
  rw [cayleyOne_eq, zorn_eta x, cayleyPolar_zmk, cayleyTr_zmk]
  ring

theorem cayleyPolar_zI (w : Ix3 → F) (x : quasithinZorn F) :
    cayleyPolar (zI w) x = bilQ w (zP x) := by
  rw [q6_eta w, zI_q6, zorn_eta x, cayleyPolar_zmk, zP_zmk]
  simp only [bilQ, q6, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem cayleyPolar_cg (g : ↥(cayleyGroup F)) (x y : quasithinZorn F) :
    cayleyPolar (cgE g x) (cgE g y) = cayleyPolar x y := by
  simp only [cayleyPolar, ← map_add, cg_norm]

theorem cayleyMul_add_left (x x' y : quasithinZorn F) :
    cayleyMul (x + x') y = cayleyMul x y + cayleyMul x' y := by
  rw [zorn_eta x, zorn_eta x', zorn_eta y, zmk_add, cayleyMul_zmk, cayleyMul_zmk, cayleyMul_zmk,
    zmk_add]
  apply zmk_congr <;> ring

theorem cayleyMul_add_right (x y y' : quasithinZorn F) :
    cayleyMul x (y + y') = cayleyMul x y + cayleyMul x y' := by
  rw [zorn_eta x, zorn_eta y, zorn_eta y', zmk_add, cayleyMul_zmk, cayleyMul_zmk, cayleyMul_zmk,
    zmk_add]
  apply zmk_congr <;> ring

theorem cayleyMul_smul_left (c : F) (x y : quasithinZorn F) :
    cayleyMul (c • x) y = c • cayleyMul x y := by
  rw [zorn_eta x, zorn_eta y, zmk_smul, cayleyMul_zmk, cayleyMul_zmk, zmk_smul]
  apply zmk_congr <;> ring

theorem cayleyMul_smul_right (c : F) (x y : quasithinZorn F) :
    cayleyMul x (c • y) = c • cayleyMul x y := by
  rw [zorn_eta x, zorn_eta y, zmk_smul, cayleyMul_zmk, cayleyMul_zmk, zmk_smul]
  apply zmk_congr <;> ring

theorem cayleyMul_one_left (x : quasithinZorn F) : cayleyMul (cayleyOne F) x = x := by
  rw [cayleyOne_eq, zorn_eta x, cayleyMul_zmk]
  apply zmk_congr <;> ring

variable [CharP F 2]

theorem cayleyMul_self (x : quasithinZorn F) :
    cayleyMul x x = cayleyTr x • x + cayleyNorm x • cayleyOne F := by
  rw [zorn_eta x]
  simp only [cayleyMul_zmk, cayleyTr_zmk, cayleyNorm_zmk, cayleyOne_eq, zmk_smul, zmk_add]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  apply zmk_congr <;> ring_nf <;> simp [h2]

theorem cayleyMul_alt (x y : quasithinZorn F) :
    cayleyMul x (cayleyMul x y) = cayleyMul (cayleyMul x x) y := by
  rw [zorn_eta x, zorn_eta y]
  simp only [cayleyMul_zmk]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  apply zmk_congr <;> simp only [sub_eq_add_neg, CharTwo.neg_eq] <;> ring_nf <;> simp [h2]

theorem cayleyTr_mul (x y : quasithinZorn F) :
    cayleyTr (cayleyMul x y) = cayleyPolar x y + cayleyTr x * cayleyTr y := by
  rw [zorn_eta x, zorn_eta y, cayleyMul_zmk]
  simp only [cayleyPolar_zmk, cayleyTr_zmk]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ring_nf
  simp [h2]

theorem cayleyPolar_mul_self (x y : quasithinZorn F) :
    cayleyPolar (cayleyMul x y) x = cayleyNorm x * cayleyTr y := by
  rw [zorn_eta x, zorn_eta y, cayleyMul_zmk]
  simp only [cayleyPolar_zmk, cayleyTr_zmk, cayleyNorm_zmk]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  simp only [sub_eq_add_neg, CharTwo.neg_eq]
  ring_nf
  simp [h2]

theorem cayleyPolar_mul_add (x y z : quasithinZorn F) :
    cayleyPolar (cayleyMul x y) z + cayleyPolar y (cayleyMul x z) =
      cayleyTr x * cayleyPolar y z := by
  rw [zorn_eta x, zorn_eta y, zorn_eta z, cayleyMul_zmk, cayleyMul_zmk]
  simp only [cayleyPolar_zmk, cayleyTr_zmk]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  simp only [sub_eq_add_neg, CharTwo.neg_eq]
  ring_nf
  simp [h2]

theorem cayleyPolar_of_tr {z z' : quasithinZorn F} (hz : cayleyTr z = 0) (hz' : cayleyTr z' = 0) :
    cayleyPolar z z' = bilQ (zP z) (zP z') := by
  conv_lhs => rw [trace_zero_eq hz, trace_zero_eq hz']
  have h1 : cayleyTr (cayleyOne F) = 0 := by
    rw [cayleyOne_eq, cayleyTr_zmk]
    exact CharTwo.add_self_eq_zero 1
  simp only [cayleyPolar_add_left, cayleyPolar_add_right, cayleyPolar_smul_left,
    cayleyPolar_smul_right, cayleyPolar_one_left, cayleyPolar_comm (zI _) (cayleyOne F),
    cayleyTr_zI, cayleyPolar_zI, zP_zI, h1]
  ring

theorem eq_smul_one_of_zP {z : quasithinZorn F} (hz : cayleyTr z = 0) (hP : zP z = 0) :
    z = z.1 • cayleyOne F := by
  conv_lhs => rw [trace_zero_eq hz, hP, zI_zero, zero_add]

theorem eq_one_of_g2Act (g : ↥(cayleyGroup F)) (hg : ∀ w, g2Act g w = w) : g = 1 := by
  have hq : (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ quasithinG2 F := by
    rw [G11.P3G2.quasithinG2_eq_cayleyGroup]
    exact g.2
  have hZ := FFC.zornAuto_eq_one (mem_quasithinG2_isZornAuto hq) (fun x hx => by
    have htr : cayleyTr x = 0 := hx
    have hd : cayleyTr (cgE g x - x) = 0 := by
      rw [show cayleyTr (cgE g x - x) = cayleyTr (cgE g x) - cayleyTr x by
        simp [cayleyTr, sub_add_sub_comm], cg_tr, sub_self]
    have hP : zP (cgE g x - x) = 0 := by
      rw [sub_eq_add_neg, zP_add, ← neg_one_smul F x, zP_smul, g2_zP_apply g x htr, ← g2Act_apply,
        hg, neg_one_smul, add_neg_cancel]
    refine ⟨(cgE g x - x).1, ?_⟩
    have h := eq_smul_one_of_zP hd hP
    rw [cayleyOne_eq] at h
    rw [← sub_add_cancel (cgE g x) x, add_comm, h]
    simp [zmk])
  apply Subtype.ext
  apply LinearEquiv.ext
  exact hZ

omit [CharP F 2] in
theorem cayleyPolar_zE' (y : quasithinZorn F) : cayleyPolar y (zE' F) = y.1 := by
  rw [cayleyPolar_eq]
  simp [zE', zmk, Fin.sum_univ_three]

omit [CharP F 2] in
theorem fG_eq_zP (g : ↥(cayleyGroup F)) : fG g = zP (cgE g (zE' F) - zE' F) := by
  refine eq_of_bilQ fun w => ?_
  rw [bilQ_fG, ellG]
  have hsymm : bilQ (zP (cgE g (zE' F) - zE' F)) w = bilQ w (zP (cgE g (zE' F) - zE' F)) := by
    simp only [bilQ]
    ring
  rw [hsymm, ← cayleyPolar_zI, sub_eq_add_neg, cayleyPolar_add_right, ← neg_one_smul F (zE' F),
    cayleyPolar_smul_right]
  have h0 : cayleyPolar (zI w) (zE' F) = 0 := by
    rw [cayleyPolar_zE', q6_eta w, zI_q6]
    rfl
  have h1 : cayleyPolar (zI w) (cgE g (zE' F)) = cayleyPolar (cgE g⁻¹ (zI w)) (zE' F) := by
    rw [← cayleyPolar_cg g⁻¹ (zI w) (cgE g (zE' F)), cg_inv_apply]
  rw [h0, h1, mul_zero, add_zero, cayleyPolar_zE']

@[expose] noncomputable def liftX (x : quasithinZorn F) (w : Ix3 → F) : quasithinZorn F :=
  zI w + (cayleyPolar (zI w) x / cayleyTr x) • cayleyOne F

theorem cayleyTr_liftX (x : quasithinZorn F) (w : Ix3 → F) : cayleyTr (liftX x w) = 0 := by
  rw [liftX, cayleyOne_eq, zmk_smul, q6_eta w, zI_q6, zmk_add, cayleyTr_zmk]
  simp only [mul_one, zero_add]
  exact CharTwo.add_self_eq_zero _

omit [CharP F 2] in
theorem zP_liftX (x : quasithinZorn F) (w : Ix3 → F) : zP (liftX x w) = w := by
  rw [liftX, zP_add, zP_smul, zP_one, smul_zero, add_zero, zP_zI]

theorem cayleyPolar_liftX {x : quasithinZorn F} (hx : cayleyTr x ≠ 0) (w : Ix3 → F) :
    cayleyPolar (liftX x w) x = 0 := by
  rw [liftX, cayleyPolar_add_left, cayleyPolar_smul_left, cayleyPolar_one_left,
    div_mul_cancel₀ _ hx]
  exact CharTwo.add_self_eq_zero _

theorem liftX_unique {x : quasithinZorn F} (hx : cayleyTr x ≠ 0) {z : quasithinZorn F}
    (hz : cayleyTr z = 0) (hzx : cayleyPolar z x = 0) : z = liftX x (zP z) := by
  have hdecomp := trace_zero_eq hz
  have hc : z.1 = cayleyPolar (zI (zP z)) x / cayleyTr x := by
    have h1 : cayleyPolar z x = cayleyPolar (zI (zP z)) x + z.1 * cayleyTr x := by
      conv_lhs => rw [hdecomp]
      rw [cayleyPolar_add_left, cayleyPolar_smul_left, cayleyPolar_one_left]
    rw [hzx] at h1
    rw [eq_div_iff hx]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination -h1 - (cayleyPolar (zI (zP z)) x) * h2
  rw [liftX, ← hc]
  exact hdecomp

omit [CharP F 2] in
theorem liftX_add (x : quasithinZorn F) (w w' : Ix3 → F) :
    liftX x (w + w') = liftX x w + liftX x w' := by
  simp only [liftX, zI_add, cayleyPolar_add_left, add_div, add_smul]
  abel

omit [CharP F 2] in
theorem zI_smul (c : F) (w : Ix3 → F) : zI (c • w) = c • zI w := by
  rw [q6_eta w, q6_smul, zI_q6, zI_q6, zmk_smul]
  simp

omit [CharP F 2] in
theorem liftX_smul (x : quasithinZorn F) (c : F) (w : Ix3 → F) :
    liftX x (c • w) = c • liftX x w := by
  simp only [liftX, zI_smul, cayleyPolar_smul_left, smul_add, smul_smul, mul_div_assoc]

theorem cg_liftX {x : quasithinZorn F} (hx : cayleyTr x ≠ 0) {g : ↥(cayleyGroup F)} {μ : F}
    (hg : cgE g x = x + μ • cayleyOne F) (w : Ix3 → F) :
    cgE g (liftX x w) = liftX x (g2Act g w) := by
  have htr : cayleyTr (cgE g (liftX x w)) = 0 := by rw [cg_tr, cayleyTr_liftX]
  have hpol : cayleyPolar (cgE g (liftX x w)) x = 0 := by
    have h1 : x = cgE g x + μ • cayleyOne F := by
      rw [hg, add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
    calc cayleyPolar (cgE g (liftX x w)) x =
        cayleyPolar (cgE g (liftX x w)) (cgE g x + μ • cayleyOne F) := by rw [← h1]
      _ = cayleyPolar (cgE g (liftX x w)) (cgE g x) +
          μ * cayleyPolar (cgE g (liftX x w)) (cayleyOne F) := by
        rw [cayleyPolar_add_right, cayleyPolar_smul_right]
      _ = 0 := by
        rw [cayleyPolar_cg, cayleyPolar_liftX hx, cayleyPolar_comm _ (cayleyOne F),
          cayleyPolar_one_left, htr, mul_zero, add_zero]
  rw [liftX_unique hx htr hpol, g2_zP_apply g _ (cayleyTr_liftX x w), zP_liftX, ← g2Act_apply]

@[expose] noncomputable def opJ (x : quasithinZorn F) (w : Ix3 → F) : Ix3 → F :=
  zP (cayleyMul x (liftX x w))

theorem cayleyTr_mul_liftX {x : quasithinZorn F} (hx : cayleyTr x ≠ 0) (w : Ix3 → F) :
    cayleyTr (cayleyMul x (liftX x w)) = 0 := by
  rw [cayleyTr_mul, cayleyPolar_comm, cayleyPolar_liftX hx, cayleyTr_liftX, mul_zero, add_zero]

omit [CharP F 2] in
theorem opJ_add (x : quasithinZorn F) (w w' : Ix3 → F) : opJ x (w + w') = opJ x w + opJ x w' := by
  rw [opJ, liftX_add, cayleyMul_add_right, zP_add, opJ, opJ]

omit [CharP F 2] in
theorem opJ_smul (x : quasithinZorn F) (c : F) (w : Ix3 → F) : opJ x (c • w) = c • opJ x w := by
  rw [opJ, liftX_smul, cayleyMul_smul_right, zP_smul, opJ]

theorem liftX_opJ {x : quasithinZorn F} (hx : cayleyTr x ≠ 0) (w : Ix3 → F) :
    liftX x (opJ x w) = cayleyMul x (liftX x w) := by
  have h := liftX_unique hx (cayleyTr_mul_liftX hx w)
    (by rw [cayleyPolar_mul_self, cayleyTr_liftX, mul_zero])
  rw [opJ]
  exact h.symm

theorem opJ_opJ {x : quasithinZorn F} (hx : cayleyTr x ≠ 0) (w : Ix3 → F) :
    opJ x (opJ x w) = cayleyTr x • opJ x w + cayleyNorm x • w := by
  rw [opJ, liftX_opJ hx, cayleyMul_alt, cayleyMul_self, cayleyMul_add_left, cayleyMul_smul_left,
    cayleyMul_smul_left, cayleyMul_one_left, zP_add, zP_smul, zP_smul, zP_liftX, opJ]

theorem bilQ_opJ_add {x : quasithinZorn F} (hx : cayleyTr x ≠ 0) (w w' : Ix3 → F) :
    bilQ (opJ x w) w' + bilQ w (opJ x w') = cayleyTr x * bilQ w w' := by
  have h := cayleyPolar_mul_add x (liftX x w) (liftX x w')
  rw [cayleyPolar_of_tr (cayleyTr_mul_liftX hx w) (cayleyTr_liftX x w'),
    cayleyPolar_of_tr (cayleyTr_liftX x w) (cayleyTr_mul_liftX hx w'),
    cayleyPolar_of_tr (cayleyTr_liftX x w) (cayleyTr_liftX x w'), zP_liftX, zP_liftX] at h
  exact h

theorem g2Act_opJ {x : quasithinZorn F} (hx : cayleyTr x ≠ 0) {g : ↥(cayleyGroup F)} {μ : F}
    (hg : cgE g x = x + μ • cayleyOne F) (w : Ix3 → F) :
    g2Act g (opJ x w) = opJ x (g2Act g w) + μ • g2Act g w := by
  have h1 : g2Act g (opJ x w) = zP (cgE g (cayleyMul x (liftX x w))) := by
    rw [opJ, g2Act_apply, g2_zP_apply g _ (cayleyTr_mul_liftX hx w)]
  rw [h1, cg_mul, hg, cg_liftX hx hg, cayleyMul_add_left, cayleyMul_smul_left, cayleyMul_one_left,
    zP_add, zP_smul, zP_liftX, opJ]

end CFSG.Quasithin.B5.G2D
