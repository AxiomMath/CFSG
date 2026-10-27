module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel LargeEvenInLambda2 LargeEvenLieTag)

section Kind

theorem twistKindOf_eq_inner_of_twistInner {τ : Tag}
    (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (Ψ : Set (Fin τ.rank → ℤ))
    (h : twistInner Ψ ((ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength ρ Ψ])) :
    twistKindOf ρ Ψ = .inner := by
  unfold twistKindOf
  rw [if_pos h]

theorem twistKindOf_eq_inner_of_compRank_eq_one
    {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (Ψ : Set (Fin τ.rank → ℤ))
    (h1 : compRank Ψ = 1) : twistKindOf ρ Ψ = .inner := by
  classical
  by_cases hin : twistInner Ψ
      ((ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength ρ Ψ])
  · unfold twistKindOf
    rw [if_pos hin]
  · unfold twistKindOf
    rw [if_neg hin, if_neg (by rintro (⟨h, _⟩ | ⟨h, _, _⟩) <;> omega),
      if_neg (fun h => by omega), if_neg (fun h => by omega)]

theorem twistKindOf_eq_suN {τ : Tag}
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (Ψ : Set (Fin τ.rank → ℤ))
    (hni : ¬ twistInner Ψ ((ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength ρ Ψ]))
    (h2 : 2 ≤ compRank Ψ) (hn : Ψ.ncard = compRank Ψ * (compRank Ψ + 1)) :
    twistKindOf ρ Ψ = .suN := by
  unfold twistKindOf
  rw [if_neg hni]
  have hnexc : ¬ ((compRank Ψ = 6 ∧ Ψ.ncard = 72) ∨ (compRank Ψ = 4 ∧ Ψ.ncard = 24 ∧
      ¬ twistInner Ψ
        ((ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[2 * componentOrbitLength ρ Ψ]))) := by
    rintro (⟨h6, h72⟩ | ⟨h4, h24, -⟩)
    · rw [h6] at hn; omega
    · rw [h4] at hn; omega
  have hntwoD : ¬ (4 ≤ compRank Ψ ∧ Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1)) := by
    rintro ⟨h4, htwo⟩
    have hcpos : 0 < compRank Ψ := by omega
    have h1 : compRank Ψ * (compRank Ψ + 1) = compRank Ψ * (2 * (compRank Ψ - 1)) := by
      calc compRank Ψ * (compRank Ψ + 1) = Ψ.ncard := hn.symm
        _ = 2 * compRank Ψ * (compRank Ψ - 1) := htwo
        _ = compRank Ψ * (2 * (compRank Ψ - 1)) := by ring
    have h1' : compRank Ψ + 1 = 2 * (compRank Ψ - 1) := Nat.eq_of_mul_eq_mul_left hcpos h1
    omega
  rw [if_neg hnexc, if_neg hntwoD, if_pos ⟨h2, hn⟩]

theorem twistKindOf_eq_twoD_of_five {τ : Tag}
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (Ψ : Set (Fin τ.rank → ℤ))
    (hni : ¬ twistInner Ψ ((ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength ρ Ψ]))
    (h5 : 5 ≤ compRank Ψ) (hn : Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1)) :
    twistKindOf ρ Ψ = .twoD := by
  unfold twistKindOf
  rw [if_neg hni]
  have hnexc : ¬ ((compRank Ψ = 6 ∧ Ψ.ncard = 72) ∨ (compRank Ψ = 4 ∧ Ψ.ncard = 24 ∧
      ¬ twistInner Ψ
        ((ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[2 * componentOrbitLength ρ Ψ]))) := by
    rintro (⟨h6, h72⟩ | ⟨h4, -, -⟩)
    · rw [hn, h6] at h72; omega
    · omega
  rw [if_neg hnexc, if_pos ⟨by omega, hn⟩]

theorem twistKindOf_eq_exc_of_E6 {τ : Tag}
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (Ψ : Set (Fin τ.rank → ℤ))
    (hni : ¬ twistInner Ψ ((ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength ρ Ψ]))
    (h6 : compRank Ψ = 6) (hn : Ψ.ncard = 72) : twistKindOf ρ Ψ = .exc := by
  unfold twistKindOf
  rw [if_neg hni, if_pos (Or.inl ⟨h6, hn⟩)]

theorem twistKindOf_eq_exc_of_D4 {τ : Tag}
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (Ψ : Set (Fin τ.rank → ℤ))
    (hni : ¬ twistInner Ψ ((ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength ρ Ψ]))
    (h4 : compRank Ψ = 4) (hn : Ψ.ncard = 24)
    (hni2 : ¬ twistInner Ψ
      ((ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[2 * componentOrbitLength ρ Ψ])) :
    twistKindOf ρ Ψ = .exc := by
  unfold twistKindOf
  rw [if_neg hni, if_pos (Or.inr ⟨h4, hn, hni2⟩)]

theorem twistKindOf_eq_twoD_of_D4 {τ : Tag}
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (Ψ : Set (Fin τ.rank → ℤ))
    (hni : ¬ twistInner Ψ ((ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[componentOrbitLength ρ Ψ]))
    (h4 : compRank Ψ = 4) (hn : Ψ.ncard = 24)
    (hin2 : twistInner Ψ
      ((ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[2 * componentOrbitLength ρ Ψ])) :
    twistKindOf ρ Ψ = .twoD := by
  unfold twistKindOf
  have hnexc : ¬ ((compRank Ψ = 6 ∧ Ψ.ncard = 72) ∨ (compRank Ψ = 4 ∧ Ψ.ncard = 24 ∧
      ¬ twistInner Ψ
        ((ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[2 * componentOrbitLength ρ Ψ]))) := by
    rintro (⟨h6, -⟩ | ⟨-, -, h⟩)
    · omega
    · exact h hin2
  rw [if_neg hni, if_neg hnexc, if_pos ⟨by omega, by rw [hn, h4]⟩]

end Kind

section LabelEval

theorem componentLabel_suN (r N n : ℕ) :
    componentLabel r N .suN n = ⟨LargeEvenLieTag.twA, r, n⟩ := rfl

theorem componentLabel_twoD (r N n : ℕ) :
    componentLabel r N .twoD n = ⟨LargeEvenLieTag.twD, r, n⟩ := rfl

theorem componentLabel_exc_E6 {r : ℕ} (N n : ℕ) (hr : r = 6) :
    componentLabel r N .exc n = ⟨LargeEvenLieTag.twE6, 0, n⟩ := by
  simp [componentLabel, hr]

theorem componentLabel_exc_D4 {r : ℕ} (N n : ℕ) (hr : r = 4) :
    componentLabel r N .exc n = ⟨LargeEvenLieTag.triD4, 0, n⟩ := by
  simp [componentLabel, hr]

theorem componentLabel_inner_A {r N : ℕ} (n : ℕ) (hN : N = r * (r + 1)) :
    componentLabel r N .inner n = ⟨LargeEvenLieTag.A, r, n⟩ := by
  simp [componentLabel, hN]

theorem componentLabel_inner_D {r N : ℕ} (n : ℕ) (h4 : 4 ≤ r) (hN : N = 2 * r * (r - 1)) :
    componentLabel r N .inner n = ⟨LargeEvenLieTag.D, r, n⟩ := by
  subst hN
  have hne : 2 * r * (r - 1) ≠ r * (r + 1) := by
    intro h
    have hcpos : 0 < r := by omega
    have h1 : r * (2 * (r - 1)) = r * (r + 1) := by rw [← h]; ring
    have h1' : 2 * (r - 1) = r + 1 := Nat.eq_of_mul_eq_mul_left hcpos h1
    omega
  simp [componentLabel, hne]

theorem componentLabel_inner_E6 {N : ℕ} (n : ℕ) (hN : N = 72) :
    componentLabel 6 N .inner n = ⟨LargeEvenLieTag.E6, 0, n⟩ := by
  simp [componentLabel, hN]

theorem componentLabel_inner_E7 {N : ℕ} (n : ℕ) (hN : N = 126) :
    componentLabel 7 N .inner n = ⟨LargeEvenLieTag.E7, 0, n⟩ := by
  simp [componentLabel, hN]

theorem componentLabel_inner_E8 {N : ℕ} (n : ℕ) (hN : N = 240) :
    componentLabel 8 N .inner n = ⟨LargeEvenLieTag.E8, 0, n⟩ := by
  simp [componentLabel, hN]

end LabelEval


end CFSG.StandardType.TableCRes

end
