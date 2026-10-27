module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119Sub

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214Even

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.RankThree.PartTwo.Sec21.Hering2119

section Group

variable {L Q : Type} [Group L] [Group Q]

theorem commute_of_lift_relations (Ψ : L →* Q) (hker : ∀ z : L, Ψ z = 1 → ∀ g : L, g * z = z * g)
    {x x' y y' : Q} (hxx' : x * x' = x' * x) (hxy : x * y = y * x) (hxy' : x * y' = y' * x)
    (hx'y : x' * y = y * x') (hx'y' : x' * y' = y' * x') (hyy' : y * y' = y' * y)
    (hx2 : x * x = 1) {s u : L}
    (hs1 : Ψ s * x * (Ψ s)⁻¹ = y) (hs2 : Ψ s * x' * (Ψ s)⁻¹ = y')
    (hs3 : Ψ s * y' * (Ψ s)⁻¹ = x')
    (hu1 : Ψ u * x * (Ψ u)⁻¹ = x * y) (hu2 : Ψ u * x' * (Ψ u)⁻¹ = x' * y')
    {A A' : L} (hA : Ψ A = x) (hA' : Ψ A' = x') : A * A' = A' * A := by
  let com : L → L → L := fun p q => p * q * p⁻¹ * q⁻¹
  have hcom : ∀ p q : L, com p q = p * q * p⁻¹ * q⁻¹ := fun _ _ => rfl
  have hcen : ∀ p q : L, Ψ p * Ψ q = Ψ q * Ψ p → ∀ g : L, g * com p q = com p q * g := by
    intro p q hpq
    apply hker
    rw [hcom, map_mul, map_mul, map_mul, map_inv, map_inv, hpq]
    group
  have hconj : ∀ p q t : L, (∀ g : L, g * com p q = com p q * g) →
      com (t * p * t⁻¹) (t * q * t⁻¹) = com p q := by
    intro p q t hc
    have e : com (t * p * t⁻¹) (t * q * t⁻¹) = t * com p q * t⁻¹ := by
      rw [hcom, hcom]; group
    rw [e, hc t, mul_inv_cancel_right]
  have hzr : ∀ p q z : L, (∀ g : L, g * z = z * g) → com p (q * z) = com p q := by
    intro p q z hz
    rw [hcom, hcom]
    calc p * (q * z) * p⁻¹ * (q * z)⁻¹ = p * q * (z * p⁻¹) * z⁻¹ * q⁻¹ := by group
      _ = p * q * (p⁻¹ * z) * z⁻¹ * q⁻¹ := by rw [hz p⁻¹]
      _ = p * q * p⁻¹ * q⁻¹ := by group
  have hzl : ∀ p q z : L, (∀ g : L, g * z = z * g) → com (p * z) q = com p q := by
    intro p q z hz
    rw [hcom, hcom]
    calc p * z * q * (p * z)⁻¹ * q⁻¹ = p * (z * q) * z⁻¹ * p⁻¹ * q⁻¹ := by group
      _ = p * (q * z) * z⁻¹ * p⁻¹ * q⁻¹ := by rw [hz q]
      _ = p * q * p⁻¹ * q⁻¹ := by group
  have hml : ∀ p q r : L, (∀ g : L, g * com q r = com q r * g) →
      com (p * q) r = com q r * com p r := by
    intro p q r hc
    have e : com (p * q) r = p * com q r * r * p⁻¹ * r⁻¹ := by rw [hcom, hcom]; group
    rw [e, hc p, hcom p r]
    group
  have hmr : ∀ p q r : L, (∀ g : L, g * com p r = com p r * g) →
      com p (q * r) = com p q * com p r := by
    intro p q r hc
    have e : com p (q * r) = com p q * (q * com p r * q⁻¹) := by rw [hcom, hcom, hcom]; group
    rw [e, hc q, mul_inv_cancel_right]
  set B := s * A * s⁻¹ with hB
  set B' := s * A' * s⁻¹ with hB'
  clear_value B B'
  have hΨB : Ψ B = y := by rw [hB, map_mul, map_mul, map_inv, hA, hs1]
  have hΨB' : Ψ B' = y' := by rw [hB', map_mul, map_mul, map_inv, hA', hs2]
  have c1 := hcen A A' (by rw [hA, hA', hxx'])
  have c2 := hcen A B' (by rw [hA, hΨB', hxy'])
  have c3 := hcen B A' (by rw [hΨB, hA', ← hx'y])
  have c4 := hcen B B' (by rw [hΨB, hΨB', hyy'])
  have e14 : com B B' = com A A' := by rw [hB, hB']; exact hconj A A' s c1
  have e23 : com A B' = com B A' := by
    obtain ⟨z, hz⟩ : ∃ z : L, z = A'⁻¹ * (s * B' * s⁻¹) := ⟨_, rfl⟩
    have hsB : Ψ (s * B' * s⁻¹) = x' := by rw [map_mul, map_mul, map_inv, hΨB', hs3]
    have hz1 : Ψ z = 1 := by rw [hz, map_mul, map_inv, hsB, hA', inv_mul_cancel]
    have hsB' : s * B' * s⁻¹ = A' * z := by rw [hz, mul_inv_cancel_left]
    calc com A B' = com (s * A * s⁻¹) (s * B' * s⁻¹) := (hconj A B' s c2).symm
      _ = com B (A' * z) := by rw [← hB, hsB']
      _ = com B A' := hzr B A' z (hker z hz1)
  have hprod : com (A * B) (A' * B') = com A A' := by
    obtain ⟨z₁, hz₁⟩ : ∃ z : L, z = (A * B)⁻¹ * (u * A * u⁻¹) := ⟨_, rfl⟩
    obtain ⟨z₂, hz₂⟩ : ∃ z : L, z = (A' * B')⁻¹ * (u * A' * u⁻¹) := ⟨_, rfl⟩
    have hAB : Ψ (A * B) = x * y := by rw [map_mul, hA, hΨB]
    have hAB' : Ψ (A' * B') = x' * y' := by rw [map_mul, hA', hΨB']
    have huA : Ψ (u * A * u⁻¹) = x * y := by rw [map_mul, map_mul, map_inv, hA, hu1]
    have huA' : Ψ (u * A' * u⁻¹) = x' * y' := by rw [map_mul, map_mul, map_inv, hA', hu2]
    have hz₁1 : Ψ z₁ = 1 := by rw [hz₁, map_mul, map_inv, hAB, huA, inv_mul_cancel]
    have hz₂1 : Ψ z₂ = 1 := by rw [hz₂, map_mul, map_inv, hAB', huA', inv_mul_cancel]
    have h1 : u * A * u⁻¹ = A * B * z₁ := by rw [hz₁, mul_inv_cancel_left]
    have h2 : u * A' * u⁻¹ = A' * B' * z₂ := by rw [hz₂, mul_inv_cancel_left]
    calc com (A * B) (A' * B') = com (A * B * z₁) (A' * B' * z₂) := by
          rw [hzr _ _ z₂ (hker z₂ hz₂1), hzl _ _ z₁ (hker z₁ hz₁1)]
      _ = com (u * A * u⁻¹) (u * A' * u⁻¹) := by rw [h1, h2]
      _ = com A A' := hconj A A' u c1
  have hexp : com (A * B) (A' * B') = com B A' * com B B' * (com A A' * com A B') := by
    have cB : ∀ g : L, g * com B (A' * B') = com B (A' * B') * g :=
      hcen B (A' * B') (by
        rw [hΨB, map_mul, hA', hΨB']
        exact Commute.mul_right (show Commute y x' from hx'y.symm) hyy')
    rw [hml A B (A' * B') cB, hmr B A' B' c4, hmr A A' B' c2]
  have hsq : com A B' * com A B' = 1 := by
    have hA2 : Ψ (A * A) = 1 := by rw [map_mul, hA, hx2]
    have e : com (A * A) B' = com A B' * com A B' := hml A A B' c2
    rw [← e, hcom, ← hker (A * A) hA2 B', mul_inv_cancel_right, mul_inv_cancel]
  have hfin : com A A' = 1 := by
    have h := hprod
    rw [hexp, ← e23, e14] at h
    have h2 : com A A' * com A A' = com A A' := by
      calc com A A' * com A A' = com A B' * com A B' * (com A A' * com A A') := by
            rw [hsq, one_mul]
        _ = com A B' * (com A B' * (com A A' * com A A')) := by group
        _ = com A B' * (com A A' * com A A' * com A B') := by
            rw [c2 (com A A' * com A A')]
        _ = com A B' * com A A' * (com A A' * com A B') := by group
        _ = com A A' := h
    calc com A A' = com A A' * com A A' * (com A A')⁻¹ := by group
      _ = com A A' * (com A A')⁻¹ := by rw [h2]
      _ = 1 := mul_inv_cancel _
  rw [hcom] at hfin
  calc A * A' = A * A' * A⁻¹ * A'⁻¹ * (A' * A) := by group
    _ = A' * A := by rw [hfin, one_mul]

end Group

section Matrices

variable {F : Type} [Field F]

@[expose] def zSL (t : F) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, t; 0, 1, 0; 0, 0, 1], by simp [det_fin_three]⟩

@[expose] def uSL : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by simp [det_fin_three]⟩

@[expose] def pSL [CharP F 2] : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by simp [det_fin_three, CharTwo.neg_eq]⟩

theorem xSL_mul_comm (a a' : F) : xSL a * xSL a' = xSL a' * xSL a := by
  rw [← xSL_add, ← xSL_add, add_comm]

theorem xSL_mul_zSL_comm (a b : F) : xSL a * zSL b = zSL b * xSL a := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_xSL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zSL, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem zSL_mul_comm (b b' : F) : zSL b * zSL b' = zSL b' * zSL b := by
  apply Subtype.ext
  repeat rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zSL, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem xSL_mul_self [CharP F 2] (a : F) : xSL a * xSL a = 1 := by
  rw [← xSL_add, CharTwo.add_self_eq_zero, xSL_zero]

theorem pSL_mul_self [CharP F 2] : (pSL : SpecialLinearGroup (Fin 3) F) * pSL = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pSL, Matrix.mul_apply, Fin.sum_univ_three]

theorem uSL_mul_self [CharP F 2] : (uSL : SpecialLinearGroup (Fin 3) F) * uSL = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uSL, Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

theorem pSL_xSL [CharP F 2] (a : F) : pSL * xSL a * pSL = zSL a := by
  apply Subtype.ext
  repeat rw [Matrix.SpecialLinearGroup.coe_mul]
  rw [coe_xSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pSL, zSL, Matrix.mul_apply, Fin.sum_univ_three]

theorem pSL_zSL [CharP F 2] (b : F) : pSL * zSL b * pSL = xSL b := by
  apply Subtype.ext
  repeat rw [Matrix.SpecialLinearGroup.coe_mul]
  rw [coe_xSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pSL, zSL, Matrix.mul_apply, Fin.sum_univ_three]

theorem uSL_xSL [CharP F 2] (a : F) : uSL * xSL a * uSL = xSL a * zSL a := by
  apply Subtype.ext
  repeat rw [Matrix.SpecialLinearGroup.coe_mul]
  rw [coe_xSL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uSL, zSL, Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

end Matrices

end CFSG.RankThree.PartTwo.Sec21.Hering214Even
