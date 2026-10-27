module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddGap7FL

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Odd.Gap7.Model

open CFSG.Quasithin.F53Mod Equiv
open scoped commutatorElement

variable {G : Type} [Group G]

theorem comm_mul_left_eq (a a' b : G) : ⁅a * a', b⁆ = a * ⁅a', b⁆ * a⁻¹ * ⁅a, b⁆ := by
  simp only [commutatorElement_def]; group

theorem comm_mul_right_eq (a b b' : G) : ⁅a, b * b'⁆ = ⁅a, b⁆ * (b * ⁅a, b'⁆ * b⁻¹) := by
  simp only [commutatorElement_def]; group

theorem conj_comm_eq (k a b : G) : k * ⁅a, b⁆ * k⁻¹ = ⁅k * a * k⁻¹, k * b * k⁻¹⁆ := by
  simp only [commutatorElement_def]; group

theorem comm_inv_left_eq (a b : G) : ⁅a⁻¹, b⁆ = a⁻¹ * ⁅a, b⁆⁻¹ * a := by
  simp only [commutatorElement_def]; group

theorem comm_inv_right_eq (a b : G) : ⁅a, b⁻¹⁆ = b⁻¹ * ⁅a, b⁆⁻¹ * b := by
  simp only [commutatorElement_def]; group

theorem comm_mul_left_central {a b z : G} (ha : z * a = a * z) (hb : z * b = b * z) :
    ⁅z * a, b⁆ = ⁅a, b⁆ := by
  have hb' : z⁻¹ * b = b * z⁻¹ := by
    calc z⁻¹ * b = z⁻¹ * (b * z) * z⁻¹ := by group
      _ = z⁻¹ * (z * b) * z⁻¹ := by rw [hb]
      _ = b * z⁻¹ := by group
  simp only [commutatorElement_def]
  calc z * a * b * (z * a)⁻¹ * b⁻¹ = (z * a) * b * a⁻¹ * z⁻¹ * b⁻¹ := by group
    _ = (a * z) * b * a⁻¹ * z⁻¹ * b⁻¹ := by rw [ha]
    _ = a * (z * b) * a⁻¹ * z⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * a⁻¹ * z⁻¹ * b⁻¹ := by rw [hb]
    _ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by
        rw [show z * a⁻¹ = a⁻¹ * z by
          calc z * a⁻¹ = a⁻¹ * (a * z) * a⁻¹ := by group
            _ = a⁻¹ * (z * a) * a⁻¹ := by rw [ha]
            _ = a⁻¹ * z := by group]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem comm_swap_of_sq {a b : G} (h : ⁅a, b⁆ * ⁅a, b⁆ = 1) : ⁅b, a⁆ = ⁅a, b⁆ := by
  rw [← commutatorElement_inv]
  exact inv_eq_of_mul_eq_one_right h

theorem mul_sq_eq {a P : G} (ha : a * a = 1) : a * P * (a * P) = ⁅a, P⁆ * (P * P) := by
  have hi : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  rw [commutatorElement_def, hi]
  group

variable {W : Type} [CommGroup W] {X : Type}

theorem comm_prod_right (e : W →* G) (f : X → G) (c : X → X → W)
    (hc : ∀ h h', e (c h h') = ⁅f h, f h'⁆) (hcen : ∀ h w, f h * e w = e w * f h) (a : X) :
    ∀ t : List X, ⁅f a, (t.map f).prod⁆ = e ((t.map (c a)).prod)
  | [] => by simp
  | h' :: t => by
    simp only [List.map_cons, List.prod_cons]
    rw [comm_mul_right_eq, comm_prod_right e f c hc hcen a t, map_mul, hc, hcen h',
      mul_inv_cancel_right]

theorem comm_prod_left (e : W →* G) (f : X → G) (c : X → X → W)
    (hc : ∀ h h', e (c h h') = ⁅f h, f h'⁆) (hcen : ∀ h w, f h * e w = e w * f h) (b : X) :
    ∀ t : List X, ⁅(t.map f).prod, f b⁆ = e ((t.map (fun h => c h b)).prod)
  | [] => by simp
  | h :: t => by
    simp only [List.map_cons, List.prod_cons]
    rw [comm_mul_left_eq, comm_prod_left e f c hc hcen b t, hcen h, mul_inv_cancel_right, ← hc,
      ← map_mul, mul_comm (c h b)]

theorem sq_prod_eq_qList (e : orth.W →* G) (f : Perm (Fin 5) → G)
    (c : Perm (Fin 5) → Perm (Fin 5) → orth.W) (hc : ∀ h h', e (c h h') = ⁅f h, f h'⁆)
    (hcen : ∀ h w, f h * e w = e w * f h) (hsq : ∀ h, f h * f h = 1) :
    ∀ x : List (Perm (Fin 5)), (x.map f).prod * (x.map f).prod = e (qList c x)
  | [] => by simp [qList]
  | h :: t => by
    simp only [List.map_cons, List.prod_cons]
    rw [mul_sq_eq (hsq h), sq_prod_eq_qList e f c hc hcen hsq t,
      comm_prod_right e f c hc hcen h t, qList, ← map_mul, mul_comm (qList c t)]

end CFSG.Quasithin.F53.Stellmacher.S43.Odd.Gap7.Model
