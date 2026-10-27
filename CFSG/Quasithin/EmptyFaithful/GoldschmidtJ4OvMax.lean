
module


public import Certificates.Certificate4204
public import CFSG.Sporadic.J4.QT2LocProof

public section

namespace CFSG.Quasithin.J4Ov

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 Matrix

theorem hj_maximal
    (hF : J4Facts) : ∀ D : Subgroup J, Hj ≤ D → D ≠ Hj → D = ⊤ := by
  obtain ⟨hto, hfrom⟩ := Certificates.certificate4204
  intro D hD hne
  obtain ⟨d, hdD, hdH⟩ : ∃ d ∈ D, d ∉ Hj := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact hne (le_antisymm (fun x hx => hcon x hx) hD)
  obtain ⟨ℓ, hℓ, h, hh, h', hh', rfl⟩ := exists_rep hF d
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    apply hdH
    have : (pathElt (repPaths.getD 0 [])) = 1 := by simp [repPaths, pathElt]
    rw [this, inv_one, mul_one]
    exact Hj.mul_mem hh hh'
  have huℓ : uEl ℓ ∈ D := by
    have e : uEl ℓ = h⁻¹ * (h * (pathElt (repPaths.getD ℓ []))⁻¹ * h') * h'⁻¹ := by
      unfold uEl; group
    rw [e]
    exact D.mul_mem (D.mul_mem (D.inv_mem (hD hh)) hdD) (D.inv_mem (hD hh'))
  have h2 : uEl 2 ∈ D := by
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2; exact huℓ
    · exact sup_le hD ((Subgroup.zpowers_le).2 huℓ) (hto ℓ hℓ hℓ0 hℓ2)
  have hall : ∀ k < 7, uEl k ∈ D := by
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0; rw [uEl_zero]; exact D.one_mem
    · by_cases hk2 : k = 2
      · subst hk2; exact h2
      · exact sup_le hD ((Subgroup.zpowers_le).2 h2) (hfrom k hk hk0 hk2)
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨k, hk, a, ha, a', ha', rfl⟩ := exists_rep hF g
  exact D.mul_mem (D.mul_mem (hD ha) (hall k hk)) (hD ha')

end CFSG.Quasithin.J4Ov
