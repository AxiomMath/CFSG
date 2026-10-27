module

public import CFSG.Quasithin.EmptyFaithful.SzF53MTab

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.F53Mod Equiv

namespace F53.Stellmacher.S43

namespace Odd

namespace Twelve

@[expose] def zD : Perm (Fin 5) := swap 0 2 * swap 1 3

theorem mem_S5ThatF_of_commute : ∀ t ∈ S5SylF, t ≠ 1 → t ^ 2 = 1 → Perm.sign t ≠ 1 →
    ∀ σ ∈ S5SylF, σ * t = t * σ → σ ∈ S5ThatF := by
  decide +kernel

private theorem S5ThatF_cases : ∀ σ ∈ S5ThatF, σ ≠ 1 →
    σ ^ 2 = 1 ∧ (Perm.sign σ ≠ 1 ∨ σ = zD) := by
  unfold zD
  decide +kernel

theorem eq_z_of_mem_S5ThatF {σ : Perm (Fin 5)} (hσ : σ ∈ S5ThatF) (h1 : σ ≠ 1)
    (hsw : ¬ σ.IsSwap) : σ = zD := by
  obtain ⟨h2, h3 | h3⟩ := S5ThatF_cases σ hσ h1
  · exact absurd ((isSwap_iff σ).mpr ⟨h1, h2, h3⟩) hsw
  · exact h3

theorem z_commute : ∀ σ ∈ S5SylF, σ * zD = zD * σ := by
  unfold zD
  decide +kernel

theorem act_comm_eq : ∀ t ∈ S5SylF, t ≠ 1 → t ^ 2 = 1 → Perm.sign t ≠ 1 →
    ∀ w : orth.W, orth.act t w = w → ∀ σ ∈ S5ThatF, ∀ ρ ∈ S5ThatF,
      orth.act σ w * w⁻¹ = 1 ∨ orth.act ρ w * w⁻¹ = 1 ∨
        orth.act σ w * w⁻¹ = orth.act ρ w * w⁻¹ := by
  decide +kernel

theorem act_comm_eq_one : ∀ t ∈ S5SylF, t ≠ 1 → t ^ 2 = 1 → Perm.sign t ≠ 1 →
    ∀ w : orth.W, orth.act t w = w → ∀ σ ∈ S5ThatF, ∀ v : orth.W,
      orth.act σ w * w⁻¹ = v * (orth.act t v)⁻¹ → orth.act σ w * w⁻¹ = 1 := by
  decide +kernel

end Twelve

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
