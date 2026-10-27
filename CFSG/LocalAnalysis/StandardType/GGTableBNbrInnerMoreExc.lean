module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreCl
public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotCatTypeDet

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def GGNbrNsE7Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E7 ∧ ¬ p ∣ 2 ^ lab.n - 1 ∧ ¬ p ∣ 2 ^ lab.n + 1

namespace NbrInnerMore

theorem halfSplit_E7_cases {p l n : ℕ} {c : Prop} (h : LargeEvenHalfSplit p ⟨.E7, l, n⟩ c) :
    p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1 ∨ (n = 1 ∧ p = 3) := by
  rcases h with (⟨-, h⟩ | ⟨hu, -⟩ | ⟨ht, -⟩ | h) | ⟨-, h⟩ | ⟨ht, -⟩ | h | h | h
  · exact Or.inl h
  · exact absurd trivial hu
  · simp at ht
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)
  · simp at ht
  · simp at h
  · simp at h
  · simp at h

theorem largeEvenLabelAll_outdiagPrime_E7
    (p : ℕ) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .E7) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagPrime p R I) :=
  (largeEvenLabelAll_subset_inn hlab (Or.inr (Or.inr (Or.inr (Or.inl ht))))).mono
    fun _ _ _ _ hI hs hna _ hφ _ => hI hs hna hφ

theorem not_halfSplit_of_markedModel_E7
    {p : ℕ} {lab : LargeEvenLabel}
    (h : GGNbrNsE7Label p lab) {X : Type} [Group X] (hX : MarkedModel lab X)
    {lab' : LargeEvenLabel} (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) (c : Prop) :
    ¬ LargeEvenHalfSplit p lab' c := by
  obtain ⟨ht, hq1, hq2⟩ := h
  have hp3 : p ≠ 3 := LinNonsplit.ne_three_of_not_dvd hq1 hq2
  have hL : LieModel X .E7 0 2 lab.n := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact hX
  obtain ⟨hT, -, hD⟩ := CFSG.SeitzReduction.E8Pilot.lieModel_E7_two_unique hL
    (lieModel_of_markedModel_two hc' hX')
  intro hHS
  obtain ⟨t', l', n'⟩ := lab'
  cases t' <;> simp only [markTag, reduceCtorEq] at hT
  all_goals try (split_ifs at hT)
  have hn' : n' = lab.n := hD
  subst hn'
  rcases halfSplit_E7_cases hHS with h1 | h1 | ⟨-, h1⟩
  · exact hq1 h1
  · exact hq2 h1
  · exact hp3 h1

end NbrInnerMore

section Labels

theorem ggTableBNbrInnerInputOn_nsE7 : GGTableBNbrInnerInputOn GGNbrNsE7Label :=
  ggTableBNbrInnerInputOn_of_clauseFive
    (fun _ _ h => Or.inl (LinNonsplit.ne_three_of_not_dvd h.2.1 h.2.2))
    (fun p _ _ _ hlab h => NbrInnerMore.largeEvenLabelAll_outdiagPrime_E7 p hlab h.1)
    (fun _ _ _ _ _ h _ _ hX _ _ hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_E7 h hX hc' hX' c)

end Labels

end CFSG.StandardType

end
