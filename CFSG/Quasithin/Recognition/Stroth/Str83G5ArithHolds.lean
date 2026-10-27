module

public import Certificates.Certificate733020
public import Certificates.Certificate733021
public import CFSG.Quasithin.Recognition.Stroth.Str83G5ArithType
public import CFSG.Quasithin.Recognition.Stroth.Str83G5ArithUnits
public import CFSG.Quasithin.Recognition.Stroth.Str83G5ArithSurvivors

public section

namespace CFSG.Quasithin.Stroth.G5


theorem str83G5ArithGoal_holds : Str83G5ArithGoal := by
  intro n hn h3 k₀ m₀ hk hm p hp hpass μT h₁ h₂ hsize ha hb hc
  have pairs30_pos : ∀ x ∈ pairs30, 0 < x.1 ∧ 0 < x.2 := by decide
  have hmem := Pattern.mem_admissibleList hp
  have hsurv : ¬ (((p = .p16 ∨ p = .p17 ∨ p = .p18 ∨ p = .p73) ∧ 4 * k₀ * m₀ - 2 = 0) ∨
      (p = .p20 ∧ 4 * k₀ * m₀ - 2 = 1)) := by
    rintro (⟨hp', hT⟩ | ⟨rfl, hT⟩)
    · exact false_of_T_eq_zero hn h3 hk hm hT hp' h₁ h₂ hb hc
    · exact false_of_T_eq_one hn h3 hk hm hT h₁ h₂ hsize ha hb
  rcases (show n = 3 ∨ 5 ≤ n by obtain ⟨a, rfl⟩ := hn; omega) with rfl | h5
  · obtain ⟨k, hk6, rfl⟩ := exists_natCast_of_isUnit_three hk
    obtain ⟨m, hm6, rfl⟩ := exists_natCast_of_isUnit_three hm
    have h' : (!passAllConc (n := 3) p ((k + 1 : ℕ) : ZMod (2 ^ 3 - 1))
        ((m + 1 : ℕ) : ZMod (2 ^ 3 - 1)) ||
        okThree p ((k + 1 : ℕ) : ZMod (2 ^ 3 - 1)) ((m + 1 : ℕ) : ZMod (2 ^ 3 - 1))) = true :=
      List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
        Certificates.certificate733021 p hmem) k (List.mem_range.mpr hk6)) m
        (List.mem_range.mpr hm6)
    rw [Pattern.passAllConc_of_pass hpass, Bool.not_true, Bool.false_or] at h'
    simp only [okThree, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h'
    rcases h' with (⟨hp', hT⟩ | ⟨hp', hT⟩) | hp'
    · exact (hsurv (Or.inl ⟨hp', hT⟩)).elim
    · exact (hsurv (Or.inr ⟨hp', hT⟩)).elim
    · exact hp'
  · obtain ⟨τ, hτ, hcanon, hneg⟩ := exists_type hn h5 k₀ m₀ (p.J + 2)
    have h' : (!τ.passAll p || okType p τ) = true :=
      List.all_eq_true.mp (List.all_eq_true.mp Certificates.certificate733020 p hmem) τ hτ
    rw [Pattern.passAll_of_pass (by omega) hcanon hpass, Bool.not_true, Bool.false_or] at h'
    obtain ⟨r, r', rfl⟩ : ∃ r r', τ = .unlinked r true r' true := by
      rcases τ with ⟨r, e, r', e'⟩ | ⟨r, ε₀, δ₀⟩
      · cases e <;> cases e' <;> first | exact ⟨r, r', rfl⟩ | exact absurd h' Bool.false_ne_true
      · exact absurd h' Bool.false_ne_true
    simp only [okType, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_true_eq, decide_eq_false_iff_not] at h'
    obtain ⟨⟨⟨hrr, h22⟩, h33⟩, h44⟩ := h'
    obtain ⟨hr, hr'⟩ := pairs30_pos _ hrr
    obtain ⟨hψ, hχ⟩ := hneg r r' rfl hr hr'
    rcases pairs30_cases hn h3 hk hm hrr hψ hχ with ⟨hrr', hT⟩ | ⟨hrr', hT⟩ | hrr'
    · refine (hsurv (Or.inl ⟨?_, hT⟩)).elim
      rcases h22.resolve_left (not_not.mpr hrr') with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact (hsurv (Or.inr ⟨h33.resolve_left (not_not.mpr hrr'), hT⟩)).elim
    · exact h44.resolve_left (not_not.mpr hrr')

end CFSG.Quasithin.Stroth.G5

end
