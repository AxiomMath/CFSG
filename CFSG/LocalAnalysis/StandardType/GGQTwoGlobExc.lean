module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.ZS.AbsIrred
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType.ZS

theorem qTwo_family_imprimitive_excl
    {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    {A : Subgroup (U ≃ₗ[ZMod 3] U)} {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) U) (i₀ i₁ : Fin n) (ζ : (ZMod 3)ˣ) (m : ℕ)
    (hi : i₀ ≠ i₁)
    (hcase : (3 ≤ m ∧ orderOf ζ = m ∧ A = ZS.gmmn 3 f i₀ i₁ ζ) ∨
             (2 ≤ m ∧ orderOf ζ = 2 * m ∧ A = ZS.g2mmn 3 f i₀ i₁ ζ)) : False := by
  have hζ : ζ ^ 2 = 1 := by
    have hall : ∀ x : (ZMod 3)ˣ, x ^ 2 = 1 := by decide
    exact hall ζ
  have hord : orderOf ζ ≤ 2 := by
    have hdvd := orderOf_dvd_of_pow_eq_one hζ
    exact Nat.le_of_dvd (by norm_num) hdvd
  rcases hcase with ⟨hm, horder, -⟩ | ⟨hm, horder, -⟩
  · omega
  · omega

theorem qTwo_family_exc_excl
    {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    {A : Subgroup (U ≃ₗ[ZMod 3] U)} (k : ZS.ExcRow)
    (hadm : k.admissible 3) (hAI : ZS.AbsIrred 3 A)
    (hdeg : Module.finrank (ZMod 3) U = k.deg) (hd4 : 4 ≤ Module.finrank (ZMod 3) U)
    (hcen : Nat.card (Subgroup.center A) = k.cen) :
    k = .H4 := by
  have hdiv := ZS.card_center_dvd_sub_one (p := 3) hAI
  cases k
  case N4 =>
    simp only [ZS.ExcRow.cen] at hcen
    rw [hcen] at hdiv
    norm_num at hdiv
  case EN4 =>
    simp only [ZS.ExcRow.cen] at hcen
    rw [hcen] at hdiv
    norm_num at hdiv
  case K5 =>
    simp only [ZS.ExcRow.admissible] at hadm
    exact absurd rfl hadm
  case K6 =>
    simp only [ZS.ExcRow.admissible] at hadm
    exact absurd rfl hadm
  case H4 =>
    rfl
  case H3 =>
    simp only [ZS.ExcRow.deg] at hdeg
    omega
  case J34 =>
    simp only [ZS.ExcRow.deg] at hdeg
    omega
  case J35 =>
    simp only [ZS.ExcRow.admissible] at hadm
    exact absurd rfl hadm
  case EJ35 =>
    simp only [ZS.ExcRow.admissible] at hadm
    omega
  case J44 =>
    simp only [ZS.ExcRow.cen] at hcen
    rw [hcen] at hdiv
    norm_num at hdiv

theorem qTwo_family_H4_excl
    {U : Type} [AddCommGroup U] [Module (ZMod 3) U] [Module.Finite (ZMod 3) U]
    {A : Subgroup (U ≃ₗ[ZMod 3] U)}
    (hdeg : Module.finrank (ZMod 3) U = ZS.ExcRow.deg .H4) (hord : Nat.card A = ZS.ExcRow.ord .H4) :
    False := by
  have hcard : Nat.card (U ≃ₗ[ZMod 3] U) = 24261120 := by
    let b : Module.Basis (Fin 4) (ZMod 3) U := Module.finBasisOfFinrankEq (ZMod 3) U hdeg
    let e : Matrix.GeneralLinearGroup (Fin 4) (ZMod 3) ≃* (U ≃ₗ[ZMod 3] U) :=
      (Matrix.GeneralLinearGroup.toLin' b).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) U)
    rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
    norm_num
  have hdvd := Subgroup.card_subgroup_dvd_card A
  rw [hord, hcard] at hdvd
  have h25 : (25 : ℕ) ∣ ZS.ExcRow.ord .H4 := by norm_num [ZS.ExcRow.ord]
  exact absurd (h25.trans hdvd) (by norm_num)

end CFSG.StandardType.QTwo
