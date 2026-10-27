module

public import CFSG.Quasithin.Background.JonesParshallG2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open Matrix CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall

namespace C10KH

section Zorn

variable {F : Type} [Field F]

@[expose] def qFun (g : Matrix (Fin 2) (Fin 2) F) (x : quasithinZorn F) : quasithinZorn F :=
  zmk (g 0 0 * g 1 1 * x.1 + g 0 0 * g 1 0 * x.2.1 0 + g 0 1 * g 1 1 * x.2.2.1 0 +
      g 0 1 * g 1 0 * x.2.2.2)
    (g 0 0 * g 0 1 * x.1 + g 0 0 ^ 2 * x.2.1 0 + g 0 1 ^ 2 * x.2.2.1 0 + g 0 0 * g 0 1 * x.2.2.2)
    (g 1 1 * x.2.1 1 + g 1 0 * x.2.2.1 2) (g 1 1 * x.2.1 2 + g 1 0 * x.2.2.1 1)
    (g 1 0 * g 1 1 * x.1 + g 1 0 ^ 2 * x.2.1 0 + g 1 1 ^ 2 * x.2.2.1 0 + g 1 0 * g 1 1 * x.2.2.2)
    (g 0 0 * x.2.2.1 1 + g 0 1 * x.2.1 2) (g 0 0 * x.2.2.1 2 + g 0 1 * x.2.1 1)
    (g 0 1 * g 1 0 * x.1 + g 0 0 * g 1 0 * x.2.1 0 + g 0 1 * g 1 1 * x.2.2.1 0 +
      g 0 0 * g 1 1 * x.2.2.2)

theorem qFun_zmk (g : Matrix (Fin 2) (Fin 2) F) (r u₀ u₁ u₂ v₀ v₁ v₂ s : F) :
    qFun g (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s) =
      zmk (g 0 0 * g 1 1 * r + g 0 0 * g 1 0 * u₀ + g 0 1 * g 1 1 * v₀ + g 0 1 * g 1 0 * s)
        (g 0 0 * g 0 1 * r + g 0 0 ^ 2 * u₀ + g 0 1 ^ 2 * v₀ + g 0 0 * g 0 1 * s)
        (g 1 1 * u₁ + g 1 0 * v₂) (g 1 1 * u₂ + g 1 0 * v₁)
        (g 1 0 * g 1 1 * r + g 1 0 ^ 2 * u₀ + g 1 1 ^ 2 * v₀ + g 1 0 * g 1 1 * s)
        (g 0 0 * v₁ + g 0 1 * u₂) (g 0 0 * v₂ + g 0 1 * u₁)
        (g 0 1 * g 1 0 * r + g 0 0 * g 1 0 * u₀ + g 0 1 * g 1 1 * v₀ + g 0 0 * g 1 1 * s) :=
  rfl

theorem qFun_mul (g h : Matrix (Fin 2) (Fin 2) F) (x : quasithinZorn F) :
    qFun g (qFun h x) = qFun (g * h) x := by
  rw [zorn_eta x, qFun_zmk, qFun_zmk, qFun_zmk]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  apply zmk_congr <;> ring

theorem qFun_one (x : quasithinZorn F) : qFun 1 x = x := by
  rw [zorn_eta x, qFun_zmk]
  apply zmk_congr <;> simp

@[expose] def qLin (g : Matrix (Fin 2) (Fin 2) F) : quasithinZorn F →ₗ[F] quasithinZorn F where
  toFun := qFun g
  map_add' x y := by
    rw [zorn_eta x, zorn_eta y, zmk_add, qFun_zmk, qFun_zmk, qFun_zmk, zmk_add]
    apply zmk_congr <;> ring
  map_smul' c x := by
    rw [zorn_eta x, zmk_smul, qFun_zmk, qFun_zmk, RingHom.id_apply, zmk_smul]
    apply zmk_congr <;> ring

theorem sl2_inv_mul_coe (g : SpecialLinearGroup (Fin 2) F) :
    ((g⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (g : Matrix (Fin 2) (Fin 2) F) = 1 := by
  change ((g⁻¹ * g : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    ((1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  rw [inv_mul_cancel]

theorem sl2_mul_inv_coe (g : SpecialLinearGroup (Fin 2) F) :
    (g : Matrix (Fin 2) (Fin 2) F) *
      ((g⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
  change ((g * g⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    ((1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  rw [mul_inv_cancel]

@[expose] def qEquiv (g : SpecialLinearGroup (Fin 2) F) :
    quasithinZorn F ≃ₗ[F] quasithinZorn F :=
  { qLin (g : Matrix (Fin 2) (Fin 2) F) with
    invFun := qFun ((g⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
    left_inv := fun x => by
      change qFun _ (qFun _ x) = x
      rw [qFun_mul, sl2_inv_mul_coe, qFun_one]
    right_inv := fun x => by
      change qFun _ (qFun _ x) = x
      rw [qFun_mul, sl2_mul_inv_coe, qFun_one] }

@[expose] def qHom : SpecialLinearGroup (Fin 2) F →* (quasithinZorn F ≃ₗ[F] quasithinZorn F) where
  toFun := qEquiv
  map_one' := LinearEquiv.ext fun x => by
    change qFun ((1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) x = x
    exact qFun_one x
  map_mul' g h := LinearEquiv.ext fun x => by
    change qFun ((g * h : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) x =
      qFun (g : Matrix (Fin 2) (Fin 2) F) (qFun (h : Matrix (Fin 2) (Fin 2) F) x)
    exact (qFun_mul _ _ x).symm

end Zorn

section Cayley

variable {F : Type} [Field F] [CharP F 2]

theorem qFun_cayleyOne {g : Matrix (Fin 2) (Fin 2) F} (hg : g.det = 1) :
    qFun g (cayleyOne F) = cayleyOne F := by
  rw [Matrix.det_fin_two] at hg
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [cayleyOne_eq, qFun_zmk]
  generalize g 0 0 = a at hg ⊢
  generalize g 0 1 = b at hg ⊢
  generalize g 1 0 = c at hg ⊢
  generalize g 1 1 = d at hg ⊢
  have hdet : a * d - b * c = 1 := hg
  apply zmk_congr
  · linear_combination (1) * hdet +
      (b * c) * h2
  · linear_combination (a * b) * h2
  · ring
  · ring
  · linear_combination (c * d) * h2
  · ring
  · ring
  · linear_combination (1) * hdet +
      (b * c) * h2

theorem qFun_tr {g : Matrix (Fin 2) (Fin 2) F} (hg : g.det = 1) (x : quasithinZorn F) :
    cayleyTr (qFun g x) = cayleyTr x := by
  rw [Matrix.det_fin_two] at hg
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [zorn_eta x, qFun_zmk, cayleyTr_zmk, cayleyTr_zmk]
  generalize g 0 0 = a at hg ⊢
  generalize g 0 1 = b at hg ⊢
  generalize g 1 0 = c at hg ⊢
  generalize g 1 1 = d at hg ⊢
  generalize x.1 = r
  generalize x.2.1 0 = u₀
  generalize x.2.2.1 0 = v₀
  generalize x.2.2.2 = s
  have hdet : a * d - b * c = 1 := hg
  linear_combination (r + s) * hdet +
    (a * c * u₀ + b * c * r + b * c * s + b * d * v₀) * h2

theorem qFun_norm {g : Matrix (Fin 2) (Fin 2) F} (hg : g.det = 1) (x : quasithinZorn F) :
    cayleyNorm (qFun g x) = cayleyNorm x := by
  rw [Matrix.det_fin_two] at hg
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [zorn_eta x, qFun_zmk, cayleyNorm_zmk, cayleyNorm_zmk]
  generalize g 0 0 = a at hg ⊢
  generalize g 0 1 = b at hg ⊢
  generalize g 1 0 = c at hg ⊢
  generalize g 1 1 = d at hg ⊢
  generalize x.1 = r
  generalize x.2.1 0 = u₀
  generalize x.2.1 1 = u₁
  generalize x.2.1 2 = u₂
  generalize x.2.2.1 0 = v₀
  generalize x.2.2.1 1 = v₁
  generalize x.2.2.1 2 = v₂
  generalize x.2.2.2 = s
  have hdet : a * d - b * c = 1 := hg
  linear_combination (a * d * r * s + a * d * u₀ * v₀ + b * c * r * s + b * c * u₀ * v₀ + r * s +
     u₀ * v₀ + u₁ * v₁ + u₂ * v₂) * hdet +
    (a * b * c * d * r * s + a * b * c * d * r ^ 2 + a * b * c * d * u₀ * v₀ +
     a * b * c * d * s ^ 2 + a * b * c ^ 2 * r * u₀ + a * b * c ^ 2 * u₀ * s +
     a * b * d ^ 2 * r * v₀ + a * b * d ^ 2 * v₀ * s + a * c * v₁ * v₂ + a ^ 2 * c * d * r * u₀ +
     a ^ 2 * c * d * u₀ * s + a ^ 2 * c ^ 2 * u₀ ^ 2 + b * c * r * s + b * c * u₀ * v₀ +
     b * c * u₁ * v₁ + b * c * u₂ * v₂ + b * d * u₁ * u₂ + b ^ 2 * c * d * r * v₀ +
     b ^ 2 * c * d * v₀ * s + b ^ 2 * c ^ 2 * r * s + b ^ 2 * c ^ 2 * u₀ * v₀ +
     b ^ 2 * d ^ 2 * v₀ ^ 2) * h2

theorem qFun_cayleyMul_zmk {g : Matrix (Fin 2) (Fin 2) F} (hg : g.det = 1)
    (r u₀ u₁ u₂ v₀ v₁ v₂ s t x₀ x₁ x₂ y₀ y₁ y₂ z : F) :
    qFun g (cayleyMul (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s) (zmk t x₀ x₁ x₂ y₀ y₁ y₂ z)) =
      cayleyMul (qFun g (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s)) (qFun g (zmk t x₀ x₁ x₂ y₀ y₁ y₂ z)) := by
  rw [Matrix.det_fin_two] at hg
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  simp only [cayleyMul_zmk, qFun_zmk]
  generalize g 0 0 = a at hg ⊢
  generalize g 0 1 = b at hg ⊢
  generalize g 1 0 = c at hg ⊢
  generalize g 1 1 = d at hg ⊢
  have hdet : a * d - b * c = 1 := hg
  apply zmk_congr
  · linear_combination (a * c * r * x₀ + a * c * u₀ * z + a * d * r * t + a * d * u₀ * y₀ +
       b * c * v₀ * x₀ + b * c * s * z + b * d * v₀ * t + b * d * s * y₀) * hdet +
      (-a * b * c * d * r * z - a * b * c * d * v₀ * x₀ - a * b * c * d * s * t -
       a * b * c * d * s * z - a * b * c ^ 2 * s * x₀ - a * b * d ^ 2 * r * y₀ -
       a * b * d ^ 2 * v₀ * t - a * b * d ^ 2 * s * y₀ + a * c * r * x₀ + a * c * u₀ * z -
       a * c * v₂ * y₁ + a * d * r * t + a * d * u₀ * y₀ - a ^ 2 * c * d * r * x₀ -
       a ^ 2 * c * d * u₀ * t - a ^ 2 * c * d * u₀ * z - a ^ 2 * c ^ 2 * u₀ * x₀ -
       a ^ 2 * d ^ 2 * r * t - a ^ 2 * d ^ 2 * u₀ * y₀ + b * c * v₀ * x₀ + b * c * s * z -
       b * d * u₂ * x₁ + b * d * v₀ * t + b * d * s * y₀ - b ^ 2 * c * d * v₀ * z -
       b ^ 2 * d ^ 2 * v₀ * y₀) * h2
  · linear_combination (-a * b * r * t - 2 * a * b * r * z - a * b * u₀ * y₀ - a * b * v₀ * x₀ -
       a * b * s * z - a ^ 2 * r * x₀ - a ^ 2 * u₀ * z - 2 * b ^ 2 * r * y₀ - b ^ 2 * v₀ * t -
       2 * b ^ 2 * v₀ * z - b ^ 2 * s * y₀) * hdet +
      (-a * b * r * z + a * b * u₁ * y₁ + a * b * v₂ * x₂ - a * b ^ 2 * c * r * t -
       a * b ^ 2 * c * r * z - a * b ^ 2 * c * u₀ * y₀ - a * b ^ 2 * c * v₀ * x₀ -
       a * b ^ 2 * c * s * t - a * b ^ 2 * c * s * z - a ^ 2 * b * c * r * x₀ -
       a ^ 2 * b * c * u₀ * t - a ^ 2 * b * c * u₀ * z - a ^ 2 * b * c * s * x₀ -
       a ^ 3 * c * u₀ * x₀ - b ^ 2 * r * y₀ + b ^ 2 * u₁ * x₂ - b ^ 2 * u₂ * x₁ - b ^ 2 * v₀ * z -
       b ^ 3 * c * r * y₀ - b ^ 3 * c * v₀ * t - b ^ 3 * c * v₀ * z - b ^ 3 * c * s * y₀ -
       b ^ 3 * d * v₀ * y₀) * h2
  · linear_combination (-c * u₀ * x₁ - c * u₁ * x₀ - c * v₂ * t - 2 * c * v₂ * z + c * s * y₂ -
       d * r * x₁ - d * u₁ * z + d * v₀ * y₂ - d * v₂ * y₀) * hdet +
      (-a * c ^ 2 * v₂ * x₀ - b * c * d * u₁ * t - b * c * d * u₁ * z - b * c * d * v₂ * y₀ -
       b * c ^ 2 * u₁ * x₀ - b * c ^ 2 * v₂ * t - b * c ^ 2 * v₂ * z - b * d ^ 2 * u₁ * y₀ -
       c * u₁ * x₀ - c * v₂ * z + c * s * y₂) * h2
  · linear_combination (-2 * c * r * y₁ - c * u₀ * x₂ - c * u₂ * x₀ + c * v₁ * t - c * s * y₁ -
       d * r * x₂ - d * u₂ * z - d * v₀ * y₁ + d * v₁ * y₀) * hdet +
      (-a * c ^ 2 * u₀ * y₁ - b * c * d * r * x₂ - b * c * d * v₀ * y₁ - b * c * d * s * x₂ -
       b * c ^ 2 * r * y₁ - b * c ^ 2 * u₀ * x₂ - b * c ^ 2 * s * y₁ - b * d ^ 2 * v₀ * x₂ -
       c * r * y₁ - c * u₀ * x₂ + c * v₁ * t) * h2
  · linear_combination (-c * d * r * t - c * d * u₀ * y₀ - c * d * v₀ * x₀ - 2 * c * d * s * t -
       c * d * s * z - c ^ 2 * r * x₀ - 2 * c ^ 2 * u₀ * t - c ^ 2 * u₀ * z - 2 * c ^ 2 * s * x₀ -
       d ^ 2 * v₀ * t - d ^ 2 * s * y₀) * hdet +
      (-a * c ^ 3 * u₀ * x₀ - b * c * d ^ 2 * r * y₀ - b * c * d ^ 2 * v₀ * t -
       b * c * d ^ 2 * v₀ * z - b * c * d ^ 2 * s * y₀ - b * c ^ 2 * d * r * t -
       b * c ^ 2 * d * r * z - b * c ^ 2 * d * u₀ * y₀ - b * c ^ 2 * d * v₀ * x₀ -
       b * c ^ 2 * d * s * t - b * c ^ 2 * d * s * z - b * c ^ 3 * r * x₀ - b * c ^ 3 * u₀ * t -
       b * c ^ 3 * u₀ * z - b * c ^ 3 * s * x₀ - b * d ^ 3 * v₀ * y₀ + c * d * u₂ * y₂ +
       c * d * v₁ * x₁ - c * d * s * t - c ^ 2 * u₀ * t + c ^ 2 * v₁ * y₂ - c ^ 2 * v₂ * y₁ -
       c ^ 2 * s * x₀) * h2
  · linear_combination (a * u₀ * x₂ - a * u₂ * x₀ - a * v₁ * t - a * s * y₁ + b * r * x₂ -
       2 * b * u₂ * t - b * u₂ * z - b * v₀ * y₁ - b * v₁ * y₀) * hdet +
      (-a * b * c * u₂ * x₀ - a * b * c * v₁ * t - a * b * c * v₁ * z - a ^ 2 * c * v₁ * x₀ +
       b * r * x₂ - b * u₂ * t - b * v₁ * y₀ - b ^ 2 * c * u₂ * t - b ^ 2 * c * u₂ * z -
       b ^ 2 * c * v₁ * y₀ - b ^ 2 * d * u₂ * y₀) * h2
  · linear_combination (-a * u₀ * x₁ + a * u₁ * x₀ - a * v₂ * t - a * s * y₂ - b * r * x₁ +
       b * u₁ * z - b * v₀ * y₂ - b * v₂ * y₀ - 2 * b * s * x₁) * hdet +
      (-a * b * c * r * y₂ - a * b * c * u₀ * x₁ - a * b * c * s * y₂ - a ^ 2 * c * u₀ * y₂ +
       b * u₁ * z - b * v₀ * y₂ - b * s * x₁ - b ^ 2 * c * r * x₁ - b ^ 2 * c * v₀ * y₂ -
       b ^ 2 * c * s * x₁ - b ^ 2 * d * v₀ * x₁) * h2
  · linear_combination (a * c * r * x₀ + a * c * u₀ * z + a * d * v₀ * x₀ + a * d * s * z +
       b * c * r * t + b * c * u₀ * y₀ + b * d * v₀ * t + b * d * s * y₀) * hdet +
      (-a * b * c * d * r * t - a * b * c * d * r * z - a * b * c * d * u₀ * y₀ -
       a * b * c * d * s * t - a * b * c ^ 2 * u₀ * t - a * b * d ^ 2 * v₀ * t -
       a * b * d ^ 2 * v₀ * z - a * b * d ^ 2 * s * y₀ + a * c * r * x₀ + a * c * u₀ * z -
       a * c * v₂ * y₁ + a * d * v₀ * x₀ + a * d * s * z - a ^ 2 * c * d * r * x₀ -
       a ^ 2 * c * d * u₀ * z - a ^ 2 * c * d * s * x₀ - a ^ 2 * c ^ 2 * u₀ * x₀ -
       a ^ 2 * d ^ 2 * v₀ * x₀ - a ^ 2 * d ^ 2 * s * z + b * c * r * t + b * c * u₀ * y₀ -
       b * d * u₂ * x₁ + b * d * v₀ * t + b * d * s * y₀ - b ^ 2 * c * d * r * y₀ -
       b ^ 2 * d ^ 2 * v₀ * y₀) * h2

theorem qFun_cayleyMul {g : Matrix (Fin 2) (Fin 2) F} (hg : g.det = 1)
    (x y : quasithinZorn F) : qFun g (cayleyMul x y) = cayleyMul (qFun g x) (qFun g y) := by
  rw [zorn_eta x, zorn_eta y]
  exact qFun_cayleyMul_zmk hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

@[expose] def zElt (g : SpecialLinearGroup (Fin 2) F) : ↥(cayleyGroup F) :=
  ⟨qEquiv g, qFun_cayleyOne g.2, qFun_cayleyMul g.2, qFun_tr g.2, qFun_norm g.2⟩

@[expose] def zHom : SpecialLinearGroup (Fin 2) F →* ↥(cayleyGroup F) where
  toFun := zElt
  map_one' := Subtype.ext (map_one qHom)
  map_mul' g h := Subtype.ext (map_mul qHom g h)

theorem zHom_apply (g : SpecialLinearGroup (Fin 2) F) (x : quasithinZorn F) :
    (zHom g : quasithinZorn F ≃ₗ[F] quasithinZorn F) x = qFun (g : Matrix (Fin 2) (Fin 2) F) x :=
  rfl

end Cayley

end C10KH

end CFSG.Quasithin.Vol2.Ch11.SecA
