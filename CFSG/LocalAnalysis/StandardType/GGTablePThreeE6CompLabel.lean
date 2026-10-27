module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def E6CompLabel (q : ℕ) (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .D ∨ lab.tag = .twD ∨ lab.tag = .A ∨ lab.tag = .twA) ∧ lab.rank = 5 ∧ 2 ^ lab.n = q) ∨
  ((lab.tag = .D ∨ lab.tag = .twD) ∧ lab.rank = 4 ∧ 2 ^ lab.n = q) ∨
  (lab.tag = .triD4 ∧ 2 ^ lab.n = q) ∨
  (lab.rank = 2 ∧ 2 ^ lab.n = q ^ 3 ∧
    (((q : ZMod 3) = 1 ∧ lab.tag = .A) ∨ ((q : ZMod 3) = 2 ∧ lab.tag = .twA)))

section Glue

variable {τ : Tag} {L : Type} [Field L]

theorem twistKind_outerD (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ) (i : KernelComponent χ)
    (hshape : 4 ≤ compRank (componentRoots χ i) ∧ (componentRoots χ i).ncard =
      2 * compRank (componentRoots χ i) * (compRank (componentRoots χ i) - 1))
    (hout : ¬ twistInner (componentRoots χ i)
      ((ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength ρ (componentRoots χ i)])) :
    twistKind ρ χ i = .twoD ∨ (twistKind ρ χ i = .exc ∧ compRank (componentRoots χ i) = 4) := by
  classical
  unfold twistKind
  rw [if_neg hout]
  by_cases hex : (compRank (componentRoots χ i) = 6 ∧ (componentRoots χ i).ncard = 72) ∨
      (compRank (componentRoots χ i) = 4 ∧ (componentRoots χ i).ncard = 24 ∧
        ¬ twistInner (componentRoots χ i)
          ((ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength ρ (componentRoots χ i)]))
  · rw [if_pos hex]
    right
    refine ⟨rfl, ?_⟩
    rcases hex with ⟨h6, h72⟩ | ⟨h4, -⟩
    · exfalso
      have := hshape.2
      rw [h72, h6] at this
      omega
    · exact h4
  · rw [if_neg hex, if_pos hshape]
    left; rfl

theorem twistKind_A2_of_not_inner (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ) (i : KernelComponent χ)
    (hr : compRank (componentRoots χ i) = 2) (hn : (componentRoots χ i).ncard = 6)
    (hout : ¬ twistInner (componentRoots χ i)
      ((ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength ρ (componentRoots χ i)])) :
    twistKind ρ χ i = .suN := by
  classical
  unfold twistKind
  rw [if_neg hout]
  have hex : ¬ ((compRank (componentRoots χ i) = 6 ∧ (componentRoots χ i).ncard = 72) ∨
      (compRank (componentRoots χ i) = 4 ∧ (componentRoots χ i).ncard = 24 ∧
        ¬ twistInner (componentRoots χ i)
          ((ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength ρ (componentRoots χ i)]))) := by
    rintro (⟨h6, -⟩ | ⟨h4, -⟩) <;> omega
  have htw : ¬ (4 ≤ compRank (componentRoots χ i) ∧ (componentRoots χ i).ncard =
      2 * compRank (componentRoots χ i) * (compRank (componentRoots χ i) - 1)) := by
    rintro ⟨h4, -⟩; omega
  rw [if_neg hex, if_neg htw, if_pos]
  exact ⟨by omega, by rw [hn, hr]⟩

theorem e6CompLabel_of_outerD {q m : ℕ} {lab : LargeEvenLabel} {r : ℕ} (k : TwistKind)
    (hk : k = .twoD ∨ (k = .exc ∧ r = 4)) (hr : r = 4 ∨ r = 5) (hm : m = 1)
    (hn : 2 ^ lab.n = q ^ m)
    (h1 : k = .twoD → r ≠ 4 → lab.tag = .twD ∧ lab.rank = r)
    (h2 : k = .twoD → r = 4 → (lab.tag = .twD ∧ lab.rank = 4) ∨ lab.tag = .triD4)
    (h3 : k = .exc → r = 4 → (lab.tag = .twD ∧ lab.rank = 4) ∨ lab.tag = .triD4) : E6CompLabel q lab := by
  subst hm
  rw [pow_one] at hn
  rcases hk with hk | ⟨hk, hr4⟩
  · by_cases h4 : r = 4
    · rcases h2 hk h4 with ⟨ht, hrk⟩ | ht
      · exact Or.inr (Or.inl ⟨Or.inr ht, hrk, hn⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨ht, hn⟩))
    · obtain ⟨ht, hrk⟩ := h1 hk h4
      have h5 : r = 5 := by omega
      exact Or.inl ⟨Or.inr (Or.inl ht), by omega, hn⟩
  · rcases h3 hk hr4 with ⟨ht, hrk⟩ | ht
    · exact Or.inr (Or.inl ⟨Or.inr ht, hrk, hn⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨ht, hn⟩))

theorem e6CompLabel_of_innerD {q m : ℕ} {lab : LargeEvenLabel} {r : ℕ}
    (hr : r = 4 ∨ r = 5) (hm : m = 1) (hn : 2 ^ lab.n = q ^ m) (ht : lab.tag = .D)
    (hrk : lab.rank = r) : E6CompLabel q lab := by
  subst hm
  rw [pow_one] at hn
  rcases hr with rfl | rfl
  · exact Or.inr (Or.inl ⟨Or.inl ht, hrk, hn⟩)
  · exact Or.inl ⟨Or.inl ht, hrk, hn⟩

theorem e6CompLabel_of_A5 {q m : ℕ} {lab : LargeEvenLabel}
    (hm : m = 1) (hn : 2 ^ lab.n = q ^ m) (hrk : lab.rank = 5) (h : lab.tag = .A ∨ lab.tag = .twA) :
    E6CompLabel q lab := by
  subst hm
  rw [pow_one] at hn
  rcases h with h | h
  · exact Or.inl ⟨Or.inr (Or.inr (Or.inl h)), hrk, hn⟩
  · exact Or.inl ⟨Or.inr (Or.inr (Or.inr h)), hrk, hn⟩

theorem e6CompLabel_of_A2 {q m : ℕ} {lab : LargeEvenLabel} {k : TwistKind}
    (hm : m = 3) (hn : 2 ^ lab.n = q ^ m) (hrk : lab.rank = 2)
    (hinn : k = .inner → lab.tag = .A) (hsu : k = .suN → lab.tag = .twA)
    (hr1 : (q : ZMod 3) = 1 → k = .inner) (hr2 : (q : ZMod 3) = 2 → k = .suN)
    (hq : (q : ZMod 3) = 1 ∨ (q : ZMod 3) = 2) : E6CompLabel q lab := by
  subst hm
  refine Or.inr (Or.inr (Or.inr ⟨hrk, hn, ?_⟩))
  rcases hq with h | h
  · exact Or.inl ⟨h, hinn (hr1 h)⟩
  · exact Or.inr ⟨h, hsu (hr2 h)⟩

end Glue

end CFSG.StandardType.TablePThreeKG

end
