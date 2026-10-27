module

public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Defs
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGTBDatumRestLabels : ℕ → LargeEvenLabel → Prop :=
  let S₀ := fun p lab => GGLabQFour p lab ∧
    ¬ (((lab.tag = .A ∧ (lab.rank = 1 ∨ lab.rank = 2)) ∨
      ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2) ∨ (lab.tag = .twA ∧ lab.rank = 2) ∨
      (lab.tag = .twD ∧ lab.rank = 2) ∨ lab.tag = .B2der ∨ lab.tag = .twB2) ∨
      (lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twF4))
  let S₁ := fun p lab => S₀ p lab ∧ ¬ (lab.tag = .twE6 ∧ p = 3)
  let S₂ := fun p lab => S₁ p lab ∧ ¬ lab.tag = .F4
  let S₄ := fun p lab => S₂ p lab ∧
    ¬ ((lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank) ∧ ¬ (lab.tag = .twE6 ∧ p ≠ 3) ∧
    ¬ (((lab.tag = .twA ∧ 3 ≤ lab.rank ∧ ¬ p ∣ lab.rank + 1) ∨
      (lab.tag = .twD ∧ lab.rank = 3)) ∧ p ∣ 2 ^ lab.n + 1)
  let S₅ := fun p lab => S₄ p lab ∧
    ¬ (lab.tag = .twD ∧ 4 ≤ lab.rank ∧
      (p ∣ 2 ^ lab.n - 1 ∨ (Even lab.rank ∧ p ∣ 2 ^ lab.n + 1))) ∧
    ¬ (lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1)
  let S₁₂ := fun p lab => S₅ p lab ∧
    ¬ (lab.tag = .twD ∧ 4 ≤ lab.rank ∧ Odd lab.rank ∧ p ∣ 2 ^ lab.n + 1)
  let S₁₄ := fun p lab => S₁₂ p lab ∧
    ¬ (lab.tag = .twA ∧ 3 ≤ lab.rank ∧ p ∣ lab.rank + 1 ∧ p ∣ 2 ^ lab.n + 1)
  let S₁₆ := fun p lab => S₁₄ p lab ∧
    ¬ ((lab.tag = .twA ∨ lab.tag = .twD) ∧ 3 ≤ lab.rank)
  let S₁₇ := fun p lab => S₁₆ p lab ∧
    ¬ lab.tag = .E8
  let S₁₈ := fun p lab => S₁₇ p lab ∧
    ¬ lab.tag = .E7
  let S₁₉ := fun p lab => S₁₈ p lab ∧
    ¬ (lab.tag = .E6 ∧ p ≠ 3)
  let S₂₀ := fun p lab => S₁₉ p lab ∧
    ¬ (((lab.tag = .A ∧ 3 ≤ lab.rank) ∧ ¬ p ∣ lab.rank + 1) ∨ lab.tag = .D)
  let S₂₁ := fun p lab => S₂₀ p lab ∧
    ¬ (lab.tag = .E6 ∧ p = 3)
  fun p lab => S₂₁ p lab ∧
    ¬ ((lab.tag = .A ∧ 3 ≤ lab.rank) ∧ p ∣ lab.rank + 1)

theorem ggTBDatumRest_not_inLambda2 {p : ℕ} {lab : LargeEvenLabel}
    (h : GGTBDatumRestLabels p lab) : ¬ LargeEvenInLambda2 lab := by
  obtain ⟨t, r, n⟩ := lab
  intro hΛ
  unfold GGTBDatumRestLabels GGLabQFour at h
  unfold LargeEvenInLambda2 at hΛ
  by_cases hd : p ∣ r + 1 <;> by_cases hp3 : p = 3 <;> cases t <;>
    simp (config := { failIfUnchanged := false }) [hd, hp3] at h hΛ <;> omega

theorem ggExcReflTBWeylDatumQFourOn_rest : GGExcReflTBWeylDatumQFourOn GGTBDatumRestLabels := by
  intro G _ _ p B Bs x L D J _ _ _ hL
  obtain ⟨lab, hΛ, _, _, _, _, _, _, hP⟩ := largeEvenMarking_exists_hasLabel hL
  exact absurd hΛ (ggTBDatumRest_not_inLambda2 hP.1)

end CFSG.StandardType

end
