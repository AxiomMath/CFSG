module

public import CFSG.RepresentationTheory.GF2.FiveSquaredOrderThree

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.RepresentationTheory.GF2

open Module

theorem twelve_le_of_generalLinearGroup {Γ : Type*} [Group Γ] {n : ℕ}
    (ρ : Γ →* Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) {a b g : Γ}
    (ha : a ^ 5 = 1) (ha1 : a ≠ 1) (hb : b ^ 5 = 1) (hab : a * b = b * a)
    (hb' : ∀ i : ℕ, b ≠ a ^ i) (hg : g ^ 3 = 1)
    (hga : ∃ i j : ℕ, g * a * g⁻¹ = a ^ i * b ^ j)
    (hgb : ∃ i j : ℕ, g * b * g⁻¹ = a ^ i * b ^ j)
    (hgnc : g * a * g⁻¹ ≠ a ∨ g * b * g⁻¹ ≠ b) (hρ : ρ a ≠ 1 ∨ ρ b ≠ 1) :
    12 ≤ n := by
  classical
  let ρ' : Representation (ZMod 2) Γ (Fin n → ZMod 2) :=
    (Units.coeHom ((Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))).comp
      ((Matrix.GeneralLinearGroup.toLin).toMonoidHom.comp ρ)
  have hρ' : ρ' a ≠ 1 ∨ ρ' b ≠ 1 := by
    rcases hρ with h | h
    · left
      intro hcontra
      apply h
      have h1 : Matrix.GeneralLinearGroup.toLin (ρ a) = 1 := by
        apply Units.ext
        simpa [ρ'] using hcontra
      exact (Matrix.GeneralLinearGroup.toLin).injective (by simpa using h1)
    · right
      intro hcontra
      apply h
      have h1 : Matrix.GeneralLinearGroup.toLin (ρ b) = 1 := by
        apply Units.ext
        simpa [ρ'] using hcontra
      exact (Matrix.GeneralLinearGroup.toLin).injective (by simpa using h1)
  have h := twelve_le_finrank_of_fiveSq_orderThree (U := Fin n → ZMod 2) (ρ := ρ')
    ha ha1 hb hab hb' hg hga hgb hgnc hρ'
  simpa [Module.finrank_fin_fun (R := ZMod 2)] using h

theorem twelve_le_of_injective {Γ : Type*} [Group Γ] {n : ℕ}
    (ρ : Γ →* Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) (hρ : Function.Injective ρ)
    {a b g : Γ} (ha : a ^ 5 = 1) (ha1 : a ≠ 1) (hb : b ^ 5 = 1) (hab : a * b = b * a)
    (hb' : ∀ i : ℕ, b ≠ a ^ i) (hg : g ^ 3 = 1)
    (hga : ∃ i j : ℕ, g * a * g⁻¹ = a ^ i * b ^ j)
    (hgb : ∃ i j : ℕ, g * b * g⁻¹ = a ^ i * b ^ j)
    (hgnc : g * a * g⁻¹ ≠ a ∨ g * b * g⁻¹ ≠ b) : 12 ≤ n := by
  apply twelve_le_of_generalLinearGroup ρ ha ha1 hb hab hb' hg hga hgb hgnc
  left
  intro h
  exact ha1 (hρ (by simpa using h))

end CFSG.RepresentationTheory.GF2
