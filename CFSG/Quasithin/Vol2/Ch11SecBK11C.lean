module

public import CFSG.RankThree.SubgroupLists.SL3Involutions

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.BK11

open Matrix

variable {K : Type*} [Field K]

theorem exists_eq_smul_add_of_commute {t A : Matrix (Fin 2) (Fin 2) K}
    (ht : t ≠ Matrix.scalar (Fin 2) (t 0 0)) (hA : A * t = t * A) :
    ∃ α β : K, A = α • (1 : Matrix (Fin 2) (Fin 2) K) + β • t := by
  have e := fun i j => congrFun (congrFun hA i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  by_cases h01 : t 0 1 = 0
  · by_cases h10 : t 1 0 = 0
    · have h00 : t 0 0 - t 1 1 ≠ 0 := by
        intro h
        apply ht
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h01, h10]
        linear_combination -h
      refine ⟨A 0 0 - (A 0 0 - A 1 1) / (t 0 0 - t 1 1) * t 0 0,
        (A 0 0 - A 1 1) / (t 0 0 - t 1 1), ?_⟩
      have hA01 : A 0 1 = 0 := by
        have : A 0 1 * (t 0 0 - t 1 1) = 0 := by
          rw [h01] at e01
          linear_combination -e01
        exact (mul_eq_zero.mp this).resolve_right h00
      have hA10 : A 1 0 = 0 := by
        have : A 1 0 * (t 0 0 - t 1 1) = 0 := by
          rw [h10] at e10
          linear_combination e10
        exact (mul_eq_zero.mp this).resolve_right h00
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h01, h10, hA01, hA10]
      field_simp
      ring
    · refine ⟨A 0 0 - A 1 0 / t 1 0 * t 0 0, A 1 0 / t 1 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;> field_simp
      · linear_combination -e11
      · linear_combination e10
  · refine ⟨A 0 0 - A 0 1 / t 0 1 * t 0 0, A 0 1 / t 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp
    · linear_combination -e00
    · linear_combination -e01

theorem eq_scalar_of_commute {t A A' : Matrix (Fin 2) (Fin 2) K}
    (hA : A * t = t * A) (hA' : A' * t = t * A') (hAA' : A * A' ≠ A' * A) :
    t = Matrix.scalar (Fin 2) (t 0 0) := by
  by_contra ht
  obtain ⟨α, β, rfl⟩ := exists_eq_smul_add_of_commute ht hA
  obtain ⟨α', β', rfl⟩ := exists_eq_smul_add_of_commute ht hA'
  apply hAA'
  have h1 : Commute t (α' • (1 : Matrix (Fin 2) (Fin 2) K) + β' • t) :=
    ((Commute.one_right t).smul_right α').add_right ((Commute.refl t).smul_right β')
  have h2 : Commute (1 : Matrix (Fin 2) (Fin 2) K) (α' • (1 : Matrix (Fin 2) (Fin 2) K) + β' • t) :=
    Commute.one_left _
  exact ((h2.smul_left α).add_left (h1.smul_left β)).eq

open CFSG.RankThree.SubgroupLists (negDiag3 coe_negDiag3 ulBlock ulBlock_mul
  block_eq_zero_of_commute_negDiag exists_injective_gl2_of_commute
  fin_two_eq_of_commute_involution)

theorem eq_of_commute_involutions (h2 : (2 : K) ≠ 0) {a b t : GL (Fin 3) K}
    (ha : a * a = 1) (hb : b * b = 1) (ht : t * t = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (hda : (a : Matrix (Fin 3) (Fin 3) K).det = 1) (hdb : (b : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hdt : (t : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hcab : a * b = b * a) (hcat : a * t = t * a) (hcbt : b * t = t * b) :
    t = 1 ∨ t = a ∨ t = b ∨ t = a * b := by
  let X : Subgroup (GL (Fin 3) K) :=
    { carrier := {g | g * a = a * g ∧ (g : Matrix (Fin 3) (Fin 3) K).det = 1}
      mul_mem' := fun {g h} hg hh => ⟨by rw [mul_assoc, hh.1, ← mul_assoc, hg.1, mul_assoc],
        by rw [Units.val_mul, Matrix.det_mul, hg.2, hh.2, one_mul]⟩
      one_mem' := ⟨by rw [one_mul, mul_one], by rw [Units.val_one, Matrix.det_one]⟩
      inv_mem' := fun {g} hg => ⟨by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hg.1, mul_inv_cancel_right],
        by
          have h1 : (g : Matrix (Fin 3) (Fin 3) K).det * ((g⁻¹ : GL (Fin 3) K) :
              Matrix (Fin 3) (Fin 3) K).det = 1 := by
            rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
              Matrix.det_one]
          rw [hg.2, one_mul] at h1
          exact h1⟩ }
  obtain ⟨ρ, hρ, hρa⟩ := exists_injective_gl2_of_commute h2 ha ha1 hda X (fun x hx => hx.1)
    (fun x hx => hx.2)
  have haX : a ∈ X := ⟨rfl, hda⟩
  have hbX : b ∈ X := ⟨hcab.symm, hdb⟩
  have htX : t ∈ X := ⟨hcat.symm, hdt⟩
  have hρa' : ρ ⟨a, haX⟩ = -1 := hρa _ rfl
  have hval : ∀ g h : X, ((ρ g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((ρ h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) → (g : GL (Fin 3) K) = h := by
    intro g h hgh
    exact congrArg Subtype.val (hρ (Units.ext hgh))
  have hsq : ∀ g : X, (g : GL (Fin 3) K) * g = 1 →
      ((ρ g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (ρ g : GL (Fin 2) K) = 1 := by
    intro g hg
    have : g * g = 1 := Subtype.ext hg
    rw [← Units.val_mul, ← map_mul, this, map_one, Units.val_one]
  have hs := hsq ⟨b, hbX⟩ hb
  have hx := hsq ⟨t, htX⟩ ht
  have hs1 : ((ρ ⟨b, hbX⟩ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ≠ 1 := fun h =>
    hb1 (hval ⟨b, hbX⟩ 1 (by rw [h, map_one, Units.val_one]))
  have hsn : ((ρ ⟨b, hbX⟩ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ≠ -1 := fun h =>
    hab (hval ⟨a, haX⟩ ⟨b, hbX⟩ (by rw [h, hρa', Units.val_neg, Units.val_one]))
  have hxs : ((ρ ⟨t, htX⟩ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      (ρ ⟨b, hbX⟩ : GL (Fin 2) K) = (ρ ⟨b, hbX⟩ : GL (Fin 2) K) * (ρ ⟨t, htX⟩ : GL (Fin 2) K) := by
    have hbt : (⟨t, htX⟩ : X) * ⟨b, hbX⟩ = ⟨b, hbX⟩ * ⟨t, htX⟩ := Subtype.ext hcbt.symm
    rw [← Units.val_mul, ← map_mul, hbt, map_mul, Units.val_mul]
  rcases fin_two_eq_of_commute_involution h2 hs hs1 hsn hx hxs with h | h | h | h
  · exact Or.inl (hval ⟨t, htX⟩ 1 (by rw [h, map_one, Units.val_one]))
  · exact Or.inr (Or.inl (hval ⟨t, htX⟩ ⟨a, haX⟩ (by rw [h, hρa', Units.val_neg, Units.val_one])))
  · exact Or.inr (Or.inr (Or.inl (hval ⟨t, htX⟩ ⟨b, hbX⟩ h)))
  · refine Or.inr (Or.inr (Or.inr (hval ⟨t, htX⟩ (⟨a, haX⟩ * ⟨b, hbX⟩) ?_)))
    rw [h, map_mul, hρa', Units.val_mul, Units.val_neg, Units.val_one, neg_one_mul]

theorem commute_of_ulBlock {E E' : Matrix (Fin 3) (Fin 3) K}
    (hE : E 0 2 = 0 ∧ E 1 2 = 0 ∧ E 2 0 = 0 ∧ E 2 1 = 0)
    (hE' : E' 0 2 = 0 ∧ E' 1 2 = 0 ∧ E' 2 0 = 0 ∧ E' 2 1 = 0)
    (h : ulBlock E * ulBlock E' = ulBlock E' * ulBlock E) : E * E' = E' * E := by
  obtain ⟨e02, e12, e20, e21⟩ := hE
  obtain ⟨f02, f12, f20, f21⟩ := hE'
  have g := fun i j => congrFun (congrFun h i) j
  have g00 := g 0 0
  have g01 := g 0 1
  have g10 := g 1 0
  have g11 := g 1 1
  simp [ulBlock, Matrix.mul_apply, Fin.sum_univ_two] at g00 g01 g10 g11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, e02, e12, e20, e21, f02, f12, f20, f21]
  · exact g00
  · exact g01
  · exact g10
  · exact g11
  · ring

theorem exists_diagonal_of_commute (h2 : (2 : K) ≠ 0) {z t y₁ y₂ P : GL (Fin 3) K}
    (hP : P⁻¹ * z * P = negDiag3 K) (hzt : t * z = z * t) (hz1 : y₁ * z = z * y₁)
    (hz2 : y₂ * z = z * y₂) (ht1 : t * y₁ = y₁ * t) (ht2 : t * y₂ = y₂ * t)
    (hy : y₁ * y₂ ≠ y₂ * y₁) :
    ∃ l m : K, ((P⁻¹ * t * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![l, l, m] := by
  have hconj : ∀ g : GL (Fin 3) K, g * z = z * g →
      ((P⁻¹ * g * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal ![-1, -1, 1] =
        diagonal ![-1, -1, 1] * ((P⁻¹ * g * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro g hg
    rw [← coe_negDiag3, ← Units.val_mul, ← Units.val_mul, ← hP]
    congr 1
    calc P⁻¹ * g * P * (P⁻¹ * z * P) = P⁻¹ * (g * z) * P := by group
      _ = P⁻¹ * (z * g) * P := by rw [hg]
      _ = P⁻¹ * z * P * (P⁻¹ * g * P) := by group
  have hc : ∀ g h : GL (Fin 3) K, g * h = h * g →
      ((P⁻¹ * g * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((P⁻¹ * h * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((P⁻¹ * h * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((P⁻¹ * g * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro g h hgh
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    calc P⁻¹ * g * P * (P⁻¹ * h * P) = P⁻¹ * (g * h) * P := by group
      _ = P⁻¹ * (h * g) * P := by rw [hgh]
      _ = P⁻¹ * h * P * (P⁻¹ * g * P) := by group
  have hne : ((P⁻¹ * y₁ * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((P⁻¹ * y₂ * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠
        ((P⁻¹ * y₂ * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((P⁻¹ * y₁ * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro h
    apply hy
    have h' : P⁻¹ * y₁ * P * (P⁻¹ * y₂ * P) = P⁻¹ * y₂ * P * (P⁻¹ * y₁ * P) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      exact h
    calc y₁ * y₂ = P * (P⁻¹ * y₁ * P * (P⁻¹ * y₂ * P)) * P⁻¹ := by group
      _ = P * (P⁻¹ * y₂ * P * (P⁻¹ * y₁ * P)) * P⁻¹ := by rw [h']
      _ = y₂ * y₁ := by group
  have hbD := block_eq_zero_of_commute_negDiag h2 (hconj t hzt)
  have hb1 := block_eq_zero_of_commute_negDiag h2 (hconj y₁ hz1)
  have hb2 := block_eq_zero_of_commute_negDiag h2 (hconj y₂ hz2)
  have hc1 := hc y₁ t ht1.symm
  have hc2 := hc y₂ t ht2.symm
  generalize ((P⁻¹ * t * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = D at *
  generalize ((P⁻¹ * y₁ * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = E₁ at *
  generalize ((P⁻¹ * y₂ * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = E₂ at *
  have hDE₁ : ulBlock E₁ * ulBlock D = ulBlock D * ulBlock E₁ := by
    rw [← ulBlock_mul ⟨hb1.1, hb1.2.1⟩, ← ulBlock_mul ⟨hbD.1, hbD.2.1⟩, hc1]
  have hDE₂ : ulBlock E₂ * ulBlock D = ulBlock D * ulBlock E₂ := by
    rw [← ulBlock_mul ⟨hb2.1, hb2.2.1⟩, ← ulBlock_mul ⟨hbD.1, hbD.2.1⟩, hc2]
  have hE : ulBlock E₁ * ulBlock E₂ ≠ ulBlock E₂ * ulBlock E₁ := fun h =>
    hne (commute_of_ulBlock hb1 hb2 h)
  have hsc := eq_scalar_of_commute hDE₁ hDE₂ hE
  have e := fun i j => congrFun (congrFun hsc i) j
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp [ulBlock] at e01 e10 e11
  refine ⟨D 0 0, D 2 2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e01, e10, e11, hbD.1, hbD.2.1, hbD.2.2.1, hbD.2.2.2]

end CFSG.Quasithin.Vol2.Ch11.SecA.BK11
