module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Sigma

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem rho_u_pos {p : ℕ} (_hp : p.Prime) (hp5 : 5 ≤ p)
    {α₁ β₁ α₂ β₂ α₃ β₃ : Fin Tag.E6.rank → ℤ} (fr : E6Frame α₁ β₁ α₂ β₂ α₃ β₃)
    {W : Set (Fin Tag.E6.rank → ℤ)} {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)}
    (hρroot : ∀ γ, IsRoot .E6 (ρ γ) ↔ IsRoot .E6 γ)
    (hρc : ∀ w ∈ W, ∀ γ, IsRoot .E6 γ → (p : ℤ) ∣ (∑ j, (ρ γ) j * w j) - ∑ j, γ j * w j)
    (hfull : ∀ s t : ℤ, ∃ w ∈ W, ∀ γ : Fin Tag.E6.rank → ℤ,
      (p : ℤ) ∣ (∑ j, γ j * w j) - (s * iform γ α₃ + t * iform γ β₃)) :
    ∀ γ, IsRoot .E6 γ → iform (ρ γ) α₃ = iform γ α₃ ∧ iform (ρ γ) β₃ = iform γ β₃ := by
  intro γ hγ
  have hργ : IsRoot .E6 (ρ γ) := (hρroot γ).2 hγ
  obtain ⟨w₁, hw₁, hd₁⟩ := hfull 1 0
  obtain ⟨w₂, hw₂, hd₂⟩ := hfull 0 1
  have e : ∀ a b c d : ℤ, a - b - (a - c) + (b - d) = c - d := fun a b c d => by ring
  have k₁ : (p : ℤ) ∣ iform (ρ γ) α₃ - iform γ α₃ := by
    have h := dvd_add (dvd_sub (hρc w₁ hw₁ γ hγ) (hd₁ (ρ γ))) (hd₁ γ)
    rw [e] at h
    simpa using h
  have k₂ : (p : ℤ) ∣ iform (ρ γ) β₃ - iform γ β₃ := by
    have h := dvd_add (dvd_sub (hρc w₂ hw₂ γ hγ) (hd₂ (ρ γ))) (hd₂ γ)
    rw [e] at h
    simpa using h
  obtain ⟨a₁, a₂⟩ := frame_u_abs_le fr hργ
  obtain ⟨c₁, c₂⟩ := frame_u_abs_le fr hγ
  obtain ⟨a₁l, a₁u⟩ := abs_le.1 a₁
  obtain ⟨a₂l, a₂u⟩ := abs_le.1 a₂
  obtain ⟨c₁l, c₁u⟩ := abs_le.1 c₁
  obtain ⟨c₂l, c₂u⟩ := abs_le.1 c₂
  have z₁ : iform (ρ γ) α₃ - iform γ α₃ = 0 :=
    Int.eq_zero_of_abs_lt_dvd k₁ (abs_lt.2 ⟨by omega, by omega⟩)
  have z₂ : iform (ρ γ) β₃ - iform γ β₃ = 0 :=
    Int.eq_zero_of_abs_lt_dvd k₂ (abs_lt.2 ⟨by omega, by omega⟩)
  constructor <;> omega

end CFSG.StandardType.TableCRes

end
