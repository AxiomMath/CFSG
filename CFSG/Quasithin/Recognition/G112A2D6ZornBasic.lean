module

public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.Quasithin.G112A2

open CFSG.Open

abbrev z6O : Type := quasithinZorn (ZMod 2)

@[expose] def z6Tr (x : z6O) : ZMod 2 := x.1 + x.2.2.2

@[expose] def z6Nrm (x : z6O) : ZMod 2 := x.1 * x.2.2.2 + ∑ i, x.2.1 i * x.2.2.1 i

@[expose] def z6Bar (x : z6O) : z6O := (x.2.2.2, -x.2.1, -x.2.2.1, x.1)

@[expose] def z6Pol (x y : z6O) : ZMod 2 :=
  x.1 * y.2.2.2 + y.1 * x.2.2.2 + ∑ i, x.2.1 i * y.2.2.1 i + ∑ i, y.2.1 i * x.2.2.1 i

@[expose] def z6One : z6O := (1, 0, 0, 1)

@[expose] def z6E : Fin 8 → z6O :=
  ![(1, 0, 0, 0), (0, 0, 0, 1),
    (0, ![1, 0, 0], 0, 0), (0, ![0, 1, 0], 0, 0), (0, ![0, 0, 1], 0, 0),
    (0, 0, ![1, 0, 0], 0), (0, 0, ![0, 1, 0], 0), (0, 0, ![0, 0, 1], 0)]

@[expose] def z6Coord (x : z6O) : Fin 8 → ZMod 2 :=
  ![x.1, x.2.2.2, x.2.1 0, x.2.1 1, x.2.1 2, x.2.2.1 0, x.2.2.1 1, x.2.2.1 2]

theorem z6_zmod2 (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide



theorem z6_zmod2_add_self (c : ZMod 2) : c + c = 0 := by
  revert c
  decide

theorem z6_add_self (v : z6O) : v + v = 0 := by
  obtain ⟨a, u, w, b⟩ := v
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact z6_zmod2_add_self a
  · funext i
    simp [z6_zmod2_add_self]
  · funext i
    simp [z6_zmod2_add_self]
  · exact z6_zmod2_add_self b

theorem z6_cross_add_left (u u' w : Fin 3 → ZMod 2) :
    quasithinCross (u + u') w = quasithinCross u w + quasithinCross u' w := by
  funext i
  fin_cases i <;> simp [quasithinCross] <;> ring

theorem z6_cross_add_right (u w w' : Fin 3 → ZMod 2) :
    quasithinCross u (w + w') = quasithinCross u w + quasithinCross u w' := by
  funext i
  fin_cases i <;> simp [quasithinCross] <;> ring

theorem z6_mul_add_left (x x' y : z6O) :
    quasithinZornMul (x + x') y = quasithinZornMul x y + quasithinZornMul x' y := by
  obtain ⟨a, u, v, b⟩ := x
  obtain ⟨a', u', v', b'⟩ := x'
  obtain ⟨c, w, z, d⟩ := y
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only [quasithinZornMul, Prod.mk_add_mk, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  · funext i
    simp only [quasithinZornMul, Prod.mk_add_mk, Pi.add_apply, z6_cross_add_left]
    ring
  · funext i
    simp only [quasithinZornMul, Prod.mk_add_mk, Pi.add_apply, z6_cross_add_left]
    ring
  · simp only [quasithinZornMul, Prod.mk_add_mk, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring

theorem z6_mul_add_right (x y y' : z6O) :
    quasithinZornMul x (y + y') = quasithinZornMul x y + quasithinZornMul x y' := by
  obtain ⟨a, u, v, b⟩ := x
  obtain ⟨c, w, z, d⟩ := y
  obtain ⟨c', w', z', d'⟩ := y'
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only [quasithinZornMul, Prod.mk_add_mk, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  · funext i
    simp only [quasithinZornMul, Prod.mk_add_mk, Pi.add_apply, z6_cross_add_right]
    ring
  · funext i
    simp only [quasithinZornMul, Prod.mk_add_mk, Pi.add_apply, z6_cross_add_right]
    ring
  · simp only [quasithinZornMul, Prod.mk_add_mk, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring

theorem z6_mul_zero_left (y : z6O) : quasithinZornMul 0 y = 0 := by
  obtain ⟨c, w, z, d⟩ := y
  simp [quasithinZornMul, quasithinCross]

theorem z6_mul_zero_right (x : z6O) : quasithinZornMul x 0 = 0 := by
  obtain ⟨a, u, v, b⟩ := x
  simp [quasithinZornMul, quasithinCross]

theorem z6_mul_one_left (y : z6O) : quasithinZornMul z6One y = y := by
  obtain ⟨c, w, z, d⟩ := y
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp [quasithinZornMul, z6One]
  · funext i
    fin_cases i <;> simp [quasithinZornMul, quasithinCross, z6One]
  · funext i
    fin_cases i <;> simp [quasithinZornMul, quasithinCross, z6One]
  · simp [quasithinZornMul, z6One]

theorem z6_mul_one_right (x : z6O) : quasithinZornMul x z6One = x := by
  obtain ⟨a, u, v, b⟩ := x
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp [quasithinZornMul, z6One]
  · funext i
    fin_cases i <;> simp [quasithinZornMul, quasithinCross, z6One]
  · funext i
    fin_cases i <;> simp [quasithinZornMul, quasithinCross, z6One]
  · simp [quasithinZornMul, z6One]

theorem z6_sq (x : z6O) : quasithinZornMul x x =
    (z6Tr x * x.1 + z6Nrm x, z6Tr x • x.2.1, z6Tr x • x.2.2.1, z6Tr x * x.2.2.2 + z6Nrm x) := by
  obtain ⟨a, u, v, b⟩ := x
  have hs : ∑ i, v i * u i = ∑ i, u i * v i := Finset.sum_congr rfl fun i _ => mul_comm _ _
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only [quasithinZornMul, z6Tr, z6Nrm]
    generalize ∑ i, u i * v i = S
    revert a b S
    decide
  · funext i
    fin_cases i <;> simp [quasithinZornMul, z6Tr, quasithinCross] <;> ring
  · funext i
    fin_cases i <;> simp [quasithinZornMul, z6Tr, quasithinCross] <;> ring
  · simp only [quasithinZornMul, z6Tr, z6Nrm]
    rw [hs]
    generalize ∑ i, u i * v i = S
    revert a b S
    decide

theorem z6_induction (P : z6O → Prop) (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hE : ∀ i, P (z6E i)) (x : z6O) : P x := by
  have hx : x = ∑ i, z6Coord x i • z6E i := by
    obtain ⟨a, u, v, b⟩ := x
    simp only [Fin.sum_univ_eight, z6Coord, z6E]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
    · simp
    · funext i
      fin_cases i <;> simp
    · funext i
      fin_cases i <;> simp
    · simp
  rw [hx]
  refine Finset.sum_induction _ P hadd h0 (fun i _ => ?_)
  rcases z6_zmod2 (z6Coord x i) with h | h
  · rw [h, zero_smul]
    exact h0
  · rw [h, one_smul]
    exact hE i

theorem z6_linear_ext (f g : z6O →ₗ[ZMod 2] z6O) (h : ∀ i, f (z6E i) = g (z6E i)) : f = g :=
  LinearMap.ext fun x => z6_induction (fun x => f x = g x) (by simp)
    (fun x y hx hy => by simp only [map_add, hx, hy]) h x

theorem z6_mul_check (f : z6O →ₗ[ZMod 2] z6O)
    (hb : ∀ i j : Fin 8, f (quasithinZornMul (z6E i) (z6E j)) =
      quasithinZornMul (f (z6E i)) (f (z6E j))) :
    ∀ x y, f (quasithinZornMul x y) = quasithinZornMul (f x) (f y) := by
  have step1 : ∀ i, ∀ y, f (quasithinZornMul (z6E i) y) =
      quasithinZornMul (f (z6E i)) (f y) := by
    intro i
    refine z6_induction (fun y => f (quasithinZornMul (z6E i) y) =
      quasithinZornMul (f (z6E i)) (f y)) ?_ ?_ ?_
    · simp [z6_mul_zero_right]
    · intro x y hx hy
      beta_reduce at hx hy ⊢
      rw [z6_mul_add_right, map_add, hx, hy, map_add, z6_mul_add_right]
    · intro j
      exact hb i j
  refine fun x => z6_induction (fun x => ∀ y, f (quasithinZornMul x y) =
      quasithinZornMul (f x) (f y)) ?_ ?_ ?_ x
  · intro y
    simp [z6_mul_zero_left]
  · intro x x' hx hx' y
    beta_reduce at hx hx' ⊢
    rw [z6_mul_add_left, map_add, hx y, hx' y, map_add, z6_mul_add_left]
  · intro i
    exact step1 i

theorem z6_pol_comm (x y : z6O) : z6Pol x y = z6Pol y x := by
  simp only [z6Pol]
  ring

theorem z6_pol_add_left (x x' y : z6O) : z6Pol (x + x') y = z6Pol x y + z6Pol x' y := by
  obtain ⟨a, u, v, b⟩ := x
  obtain ⟨a', u', v', b'⟩ := x'
  obtain ⟨c, w, z, d⟩ := y
  simp only [z6Pol, Prod.mk_add_mk, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem z6_pol_smul_left (c : ZMod 2) (x y : z6O) : z6Pol (c • x) y = c • z6Pol x y := by
  obtain ⟨a, u, v, b⟩ := x
  obtain ⟨d, w, z, e⟩ := y
  simp only [z6Pol, Prod.smul_mk, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add, mul_assoc]
  ring

@[expose] def z6B : LinearMap.BilinForm (ZMod 2) z6O :=
  LinearMap.mk₂ (ZMod 2) z6Pol z6_pol_add_left z6_pol_smul_left
    (fun x y y' => by rw [z6_pol_comm x, z6_pol_add_left, z6_pol_comm y, z6_pol_comm y'])
    (fun c x y => by rw [z6_pol_comm x (c • y), z6_pol_smul_left, z6_pol_comm y x])

theorem z6B_apply (x y : z6O) : z6B x y = z6Pol x y := rfl

theorem z6_pol_sep : ∀ x : z6O, (∀ j : Fin 8, z6Pol x (z6E j) = 0) → x = 0 := by
  decide +kernel

theorem z6B_nondegenerate : z6B.Nondegenerate := by
  refine ⟨fun x hx => z6_pol_sep x (fun j => ?_), fun y hy => z6_pol_sep y (fun j => ?_)⟩
  · simpa only [z6B_apply] using hx (z6E j)
  · have h := hy (z6E j)
    simp only [z6B_apply] at h
    rw [z6_pol_comm] at h
    exact h

theorem z6B_isRefl : z6B.IsRefl := by
  intro x y h
  rw [z6B_apply] at h ⊢
  rw [z6_pol_comm]
  exact h

theorem z6_finrank : Module.finrank (ZMod 2) z6O = 8 := by
  simp [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]

end CFSG.Quasithin.G112A2
