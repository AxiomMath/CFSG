module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeRow
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGTBJRestLabels : ℕ → LargeEvenLabel → Prop :=
  let S₀ := fun p lab => GGLabQFour p lab ∧
    ¬ (((lab.tag = .A ∧ (lab.rank = 1 ∨ lab.rank = 2)) ∨
      ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2) ∨ (lab.tag = .twA ∧ lab.rank = 2) ∨
      (lab.tag = .twD ∧ lab.rank = 2) ∨ lab.tag = .B2der ∨ lab.tag = .twB2) ∨
      (lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twF4))
  let S₃ := fun p lab => S₀ p lab ∧ ¬ lab.tag = .F4
  let S₆ := fun p lab => S₃ p lab ∧
    ¬ (lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1)
  let S₇ := fun p lab => S₆ p lab ∧
    ¬ ((lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank)
  let S₈ := fun p lab => S₇ p lab ∧
    ¬ (((lab.tag = .twA ∧ 3 ≤ lab.rank ∧ ¬ p ∣ lab.rank + 1) ∨
      (lab.tag = .twD ∧ lab.rank = 3)) ∧ p ∣ 2 ^ lab.n + 1)
  let S₉ := fun p lab => S₈ p lab ∧
    ¬ (lab.tag = .twE6 ∧ p ≠ 3)
  let S₁₀ := fun p lab => S₉ p lab ∧
    ¬ (lab.tag = .twD ∧ 4 ≤ lab.rank ∧
      (p ∣ 2 ^ lab.n - 1 ∨ (Even lab.rank ∧ p ∣ 2 ^ lab.n + 1)))
  let S₁₁ := fun p lab => S₁₀ p lab ∧
    ¬ (lab.tag = .twA ∧ 3 ≤ lab.rank ∧ p ∣ lab.rank + 1 ∧ p ∣ 2 ^ lab.n + 1)
  let S₁₃ := fun p lab => S₁₁ p lab ∧
    ¬ (lab.tag = .twD ∧ 4 ≤ lab.rank ∧ Odd lab.rank ∧ p ∣ 2 ^ lab.n + 1)
  let S₁₅ := fun p lab => S₁₃ p lab ∧
    ¬ ((lab.tag = .twA ∨ lab.tag = .twD) ∧ 3 ≤ lab.rank)
  let S₂₁ := fun p lab => S₁₅ p lab ∧
    ¬ (lab.tag = .E7 ∨ lab.tag = .E8 ∨ (lab.tag = .E6 ∧ p ≠ 3))
  let S₂₃ := fun p lab => S₂₁ p lab ∧ ¬ (lab.tag = .E6 ∧ p = 3)
  fun p lab => S₂₃ p lab ∧
    ¬ ((lab.tag = .A ∧ 3 ≤ lab.rank) ∨ lab.tag = .D)

theorem ggTBJRest_rowR2_of_inLambda2 {p : ℕ} {lab : LargeEvenLabel}
    (h : GGTBJRestLabels p lab) (hΛ : LargeEvenInLambda2 lab) :
    GGLabQFour p lab ∧ GGTBRowR2 p lab := by
  obtain ⟨t, r, n⟩ := lab
  unfold GGTBJRestLabels GGLabQFour at h
  unfold LargeEvenInLambda2 at hΛ
  unfold GGLabQFour GGTBRowR2
  by_cases hp3 : p = 3 <;> cases t <;>
    simp (config := { failIfUnchanged := false }) [hp3] at h hΛ ⊢ <;> omega

theorem ggTBJNoncommReflOn_rest
    (hRig : GGLabelRigidInput) : GGTBJNoncommReflOn GGTBJRestLabels := by
  intro G _ _ p B Bs x L D J hHyp hq hN hL
  exact ggTBJNoncommReflOn_rowR2 hRig G p B Bs x L D J hHyp hq hN
    (hL.mono_label_of_hasLabel fun _ hΛ _ h => ggTBJRest_rowR2_of_inLambda2 h hΛ)

end CFSG.StandardType

end
