module

public import CFSG.Quasithin.Vol2.Ch3E213MOLB6

public section

namespace CFSG.Quasithin.Ch3E213M.OLB

variable {X : Type} [Group X] {W : Type} [Group W]

theorem lemmaA (hcomm : ∀ a b : W, a * b = b * a) (hexp : ∀ a : W, a * a = 1)
    {ρ : X →* MulAut W} {u u' c : X} (huu : u * u' = u' * u) (hu'3 : u' * u' * u' = 1)
    (hcu : c * u * c⁻¹ = u') (hcu' : c * u' * c⁻¹ = u⁻¹)
    (hN : ∀ w : W, w * ρ c w * ρ (c * c) w * ρ (c * c * c) w = 1) {w : W}
    (hw : ρ u w = w) (hw' : tri ρ u' w = 1) : w = 1 := by
  have hinv : ∀ a : W, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (hexp a)
  have h1 : c⁻¹ * u' * c = u := by rw [← hcu]; group
  have h2 : c⁻¹ * u * c = u'⁻¹ := by
    have h3 : c⁻¹ * u⁻¹ * c = u' := by rw [← hcu']; group
    calc c⁻¹ * u * c = (c⁻¹ * u⁻¹ * c)⁻¹ := by group
      _ = u'⁻¹ := by rw [h3]
  have hzu : (c * c)⁻¹ * u * (c * c) = u⁻¹ := by
    calc (c * c)⁻¹ * u * (c * c) = c⁻¹ * (c⁻¹ * u * c) * c := by group
      _ = (c⁻¹ * u' * c)⁻¹ := by rw [h2]; group
      _ = u⁻¹ := by rw [h1]
  have hzu' : (c * c)⁻¹ * u' * (c * c) = u'⁻¹ := by
    calc (c * c)⁻¹ * u' * (c * c) = c⁻¹ * (c⁻¹ * u' * c) * c := by group
      _ = u'⁻¹ := by rw [h1, h2]
  have key : ∀ w : W, ρ u w = w → tri ρ u' w = 1 → ρ (c * c) w = w := by
    intro w hw hw'
    have hwi : ρ u⁻¹ w = w := by
      calc ρ u⁻¹ w = ρ u⁻¹ (ρ u w) := by rw [hw]
        _ = w := by rw [map_inv, MulAut.inv_apply_self]
    have s1 : ρ u (ρ (c * c) w) = ρ (c * c) w := by
      rw [rho_rho, show u * (c * c) = c * c * ((c * c)⁻¹ * u * (c * c)) by group, hzu,
        ← rho_rho, hwi]
    have s2 : tri ρ u' (ρ (c * c) w) = 1 := by
      rw [tri_conj, hzu', tri_inv hcomm ρ hu'3, hw', map_one]
    set a := w * ρ (c * c) w with ha
    have s3 : ρ c a = a := by
      have h4 := hN w
      have e : ρ (c * c * c) w = ρ c (ρ (c * c) w) := by
        rw [rho_rho, mul_assoc]
      rw [e] at h4
      have h5 : a * ρ c a = 1 := by
        rw [ha, map_mul (ρ c)]
        let _ : CommGroup W := { ‹Group W› with mul_comm := hcomm }
        calc w * ρ (c * c) w * (ρ c w * ρ c (ρ (c * c) w)) =
            w * ρ c w * ρ (c * c) w * ρ c (ρ (c * c) w) := by
              simp only [mul_comm, mul_left_comm]
          _ = 1 := h4
      calc ρ c a = a * (a * ρ c a) := by rw [← mul_assoc, hexp, one_mul]
        _ = a := by rw [h5, mul_one]
    have s4 : ρ u a = a := by rw [ha, map_mul (ρ u), hw, s1]
    have s5 : ρ u' a = a := by
      calc ρ u' a = ρ u' (ρ c a) := by rw [s3]
        _ = ρ c (ρ u a) := by
          rw [rho_rho, rho_rho, show u' * c = c * (c⁻¹ * u' * c) by group, h1]
        _ = a := by rw [s4, s3]
    have s6 : a = 1 := by
      rw [← tri_of_fixed hexp ρ s5, ha, tri_mul hcomm, hw', s2, one_mul]
    calc ρ (c * c) w = w * (w * ρ (c * c) w) := by rw [← mul_assoc, hexp, one_mul]
      _ = w := by rw [← ha, s6, mul_one]
  have k1 := key w hw hw'
  have k2 := key (ρ u' w) (by rw [rho_rho, huu, ← rho_rho, hw])
    (by rw [tri_conj, show u'⁻¹ * u' * u' = u' by group, hw', map_one])
  have hzu'' : c * c * u' = u'⁻¹ * (c * c) := by
    have h3 : (c * c)⁻¹ * u'⁻¹ * (c * c) = u' := by
      have h4 : ((c * c)⁻¹ * u' * (c * c))⁻¹ = (c * c)⁻¹ * u'⁻¹ * (c * c) := by
        simp only [mul_inv_rev, inv_inv, mul_assoc]
      rw [← h4, hzu', inv_inv]
    calc c * c * u' = c * c * ((c * c)⁻¹ * u'⁻¹ * (c * c)) := by rw [h3]
      _ = u'⁻¹ * (c * c) := by group
  rw [rho_rho, hzu'', ← rho_rho, k1] at k2
  have hfix : ρ u' w = w := by
    have h3 : ρ (u' * u') w = w := by
      calc ρ (u' * u') w = ρ u' (ρ u'⁻¹ w) := by rw [k2, rho_rho]
        _ = w := by rw [map_inv, MulAut.apply_inv_self]
    calc ρ u' w = ρ u' (ρ (u' * u') w) := by rw [h3]
      _ = w := by rw [rho_rho, ← mul_assoc, hu'3, map_one, MulAut.one_apply]
  rw [← tri_of_fixed hexp ρ hfix, hw']

theorem fixed_of_pair (hcomm : ∀ a b : W, a * b = b * a) (hexp : ∀ a : W, a * a = 1)
    {ρ : X →* MulAut W} {u u' c : X} (huu : u * u' = u' * u) (hu'3 : u' * u' * u' = 1)
    (hcu : c * u * c⁻¹ = u') (hcu' : c * u' * c⁻¹ = u⁻¹)
    (hN : ∀ w : W, w * ρ c w * ρ (c * c) w * ρ (c * c * c) w = 1) {y : W} (hy : ρ u y = y) :
    ρ u' y = y := by
  set w := ρ u' y * ρ (u' * u') y with hw
  have huu' : u * (u' * u') = u' * u' * u := (Commute.mul_right huu huu).eq
  have hwu : ρ u w = w := by
    rw [hw, map_mul (ρ u), rho_rho, rho_rho, huu, huu', ← rho_rho, ← rho_rho, hy]
  have hw1 : w = 1 := lemmaA hcomm hexp huu hu'3 hcu hcu' hN hwu
    (tri_compl hcomm hexp ρ hu'3 y)
  have hdec := tri_decomp hcomm hexp ρ u' y
  rw [← hw, hw1, mul_one] at hdec
  rw [hdec, tri_fixed hcomm ρ hu'3]

theorem fix_of_norm (hcomm : ∀ a b : W, a * b = b * a) (hexp : ∀ a : W, a * a = 1)
    {ρ : X →* MulAut W} {a b c : X} (hab : a * b = b * a) (ha3 : a * a * a = 1)
    (hb3 : b * b * b = 1) (hca : c * a * c⁻¹ = b) (hcb : c * b * c⁻¹ = a⁻¹)
    (hN : ∀ w : W, w * ρ c w * ρ (c * c) w * ρ (c * c * c) w = 1) (x : W) : ρ a x = x := by
  have hab' : Commute a b := hab
  have hbi : b⁻¹ = b * b := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hb3])
  have hconj : ∀ g h : X, c * (g * h) * c⁻¹ = (c * g * c⁻¹) * (c * h * c⁻¹) := fun g h => by
    group
  have hcai : c * a⁻¹ * c⁻¹ = b⁻¹ := by
    rw [show c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ by group, hca]
  have hcbi : c * b⁻¹ * c⁻¹ = a := by
    rw [show c * b⁻¹ * c⁻¹ = (c * b * c⁻¹)⁻¹ by group, hcb, inv_inv]
  have cube : ∀ g : X, g ^ 3 = 1 → g * g * g = 1 := fun g h => by rwa [← pow_three']
  have ha3' : a ^ 3 = 1 := by rw [pow_three']; exact ha3
  have hb3' : b ^ 3 = 1 := by rw [pow_three']; exact hb3
  have c34 : Commute (a * b) (a * b⁻¹) :=
    ((Commute.refl a).mul_right hab'.inv_right).mul_left
      (hab'.symm.mul_right (Commute.refl b).inv_right)
  have e3 : (a * b) * (a * b) * (a * b) = 1 :=
    cube _ (by rw [hab'.mul_pow, ha3', hb3', one_mul])
  have e4 : (a * b⁻¹) * (a * b⁻¹) * (a * b⁻¹) = 1 :=
    cube _ (by rw [hab'.inv_right.mul_pow, ha3', inv_pow, hb3', inv_one, one_mul])
  have e4i : (a * b⁻¹)⁻¹ * (a * b⁻¹)⁻¹ * (a * b⁻¹)⁻¹ = 1 := by
    rw [← mul_inv_rev, ← mul_inv_rev, ← mul_assoc, e4, inv_one]
  have eai : a⁻¹ * a⁻¹ * a⁻¹ = 1 := by
    rw [← mul_inv_rev, ← mul_inv_rev, ← mul_assoc, ha3, inv_one]
  have p1 : ∀ y : W, ρ b y = y → ρ a⁻¹ y = y := fun y hy =>
    fixed_of_pair hcomm hexp (ρ := ρ) (u := b) (u' := a⁻¹) (c := c)
      hab'.symm.inv_right eai hcb hcai hN hy
  have p2 : ∀ y : W, ρ (a * b) y = y → ρ (a * b⁻¹)⁻¹ y = y := fun y hy =>
    fixed_of_pair hcomm hexp (ρ := ρ) (u := a * b) (u' := (a * b⁻¹)⁻¹) (c := c)
      c34.inv_right e4i (by rw [hconj, hca, hcb]; group)
      (by rw [show c * (a * b⁻¹)⁻¹ * c⁻¹ = (c * b * c⁻¹) * (c * a⁻¹ * c⁻¹) by group, hcb, hcai,
        show a⁻¹ * b⁻¹ = (b * a)⁻¹ by group, ← hab]) hN hy
  have p3 : ∀ y : W, ρ (a * b⁻¹) y = y → ρ (a * b) y = y := fun y hy =>
    fixed_of_pair hcomm hexp (ρ := ρ) (u := a * b⁻¹) (u' := a * b) (c := c)
      c34.symm e3 (by rw [hconj, hca, hcbi, ← hab]) (by rw [hconj, hca, hcb]; group) hN hy
  have g0 : a * a = a * b * (a * b⁻¹) := by
    rw [show a * b * (a * b⁻¹) = a * (b * a) * b⁻¹ by group, ← hab]
    group
  have fa : ∀ y : W, ρ (a * a) y = y → ρ a y = y := fun y hy => by
    calc ρ a y = ρ a (ρ (a * a) y) := by rw [hy]
      _ = y := by rw [rho_rho, ← mul_assoc, ha3, map_one, MulAut.one_apply]
  have f1 : ρ a (tri ρ a (tri ρ b x)) = tri ρ a (tri ρ b x) := tri_fixed hcomm ρ ha3 _
  have f2 : ρ a (tri ρ a x) = tri ρ a x := tri_fixed hcomm ρ ha3 _
  have f3 : ρ a (tri ρ b x) = tri ρ b x := by
    have h1 := p1 _ (tri_fixed hcomm ρ hb3 x)
    calc ρ a (tri ρ b x) = ρ a (ρ a⁻¹ (tri ρ b x)) := by rw [h1]
      _ = tri ρ b x := by rw [map_inv, MulAut.apply_inv_self]
  have f4 : ρ a (tri ρ (a * b) x) = tri ρ (a * b) x := by
    have h1 := tri_fixed hcomm ρ e3 x
    have h2 := p2 _ h1
    have h3 : ρ (a * b⁻¹) (tri ρ (a * b) x) = tri ρ (a * b) x := by
      calc ρ (a * b⁻¹) (tri ρ (a * b) x) =
          ρ (a * b⁻¹) (ρ (a * b⁻¹)⁻¹ (tri ρ (a * b) x)) := by rw [h2]
        _ = tri ρ (a * b) x := by rw [map_inv, MulAut.apply_inv_self]
    apply fa
    rw [g0, ← rho_rho, h3, h1]
  have f5 : ρ a (tri ρ (a * b⁻¹) x) = tri ρ (a * b⁻¹) x := by
    have h1 := tri_fixed hcomm ρ e4 x
    have h2 := p3 _ h1
    apply fa
    rw [g0, ← rho_rho, h1, h2]
  have g1 : a * (b * b) = a * b⁻¹ := by rw [hbi]
  have g2 : a * b * (a * b) = a * a * (b * b) := by
    rw [show a * b * (a * b) = a * (b * a) * b by group, ← hab]; group
  have g3 : a * b⁻¹ * (a * b⁻¹) = a * a * b := by
    rw [show a * b⁻¹ * (a * b⁻¹) = a * (b⁻¹ * a) * b⁻¹ by group, hab'.symm.inv_left.eq, hbi]
    calc a * (a * (b * b)) * (b * b) = a * a * (b * b * b) * b := by group
      _ = a * a * b := by rw [hb3, mul_one]
  have hid : x = tri ρ a (tri ρ b x) * tri ρ a x * tri ρ b x * tri ρ (a * b) x *
      tri ρ (a * b⁻¹) x := by
    simp only [tri, map_mul (ρ a), map_mul (ρ (a * a)), rho_rho]
    rw [g1, g2, g3]
    exact nine hcomm hexp _ _ _ _ _ _ _ _ _
  rw [hid, map_mul, map_mul, map_mul, map_mul, f1, f2, f3, f4, f5]

end CFSG.Quasithin.Ch3E213M.OLB
