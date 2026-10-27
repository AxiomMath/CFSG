module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylClauseFive
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylCompDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint

@[expose] def GGNbrNsTriD4ThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .triD4 ∧ p = 3 ∧ 2 ≤ lab.n ∧ ¬ 3 ∣ 2 ^ lab.n - 1

@[expose] def GGNbrWeylResidualOpenLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrWeylResidualLabel p lab ∧ ¬ GGNbrNsTriD4ThreeLabel p lab

namespace NbrInnerMore

section TypeDet

theorem not_markedModel_char_ne_two_triD4 {lab : LargeEvenLabel} (ht : lab.tag = .triD4)
    {X : Type} [Group X] (hX : MarkedModel lab X) {lab' : LargeEvenLabel}
    (hc : markChar lab' ≠ 2) : ¬ MarkedModel lab' X := by
  have hL : LieModel X .trialityD4 0 2 lab.n := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact hX
  exact not_markedModel_of_char_ne_two hL (fun h => absurd h.1 (by decide))
    (fun h => absurd h.1 (by decide)) (fun h => absurd h.1 (by decide)) hc

theorem not_halfSplit_of_markedModel_triD4Three {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGNbrNsTriD4ThreeLabel p lab) {X : Type} [Group X]
    (hX : MarkedModel lab X) {lab' : LargeEvenLabel} (hlab' : LargeEvenInLambda2 lab')
    (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) (c : Prop) :
    ¬ LargeEvenHalfSplit p lab' c := by
  obtain ⟨ht, rfl, hn2, hq1⟩ := h
  have hL : LieModel X .trialityD4 0 2 lab.n := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact hX
  obtain ⟨ht', hn'⟩ := eq_of_markedModel_triD4 hlab.1 hL hlab' hc' hX'
  intro hHS
  obtain ⟨t', l', n'⟩ := lab'
  dsimp only at ht' hn'
  subst ht' hn'
  rcases halfSplit_triD4_cases hHS with h1 | ⟨h1, -⟩
  · exact hq1 h1
  · omega

end TypeDet

end NbrInnerMore

section Main

theorem ggNbrInnerWeylOn_nsTriD4Three : GGNbrInnerWeylOn GGNbrNsTriD4ThreeLabel :=
  ggNbrInnerWeylOn_of_clauseFive
    (fun _ _ h => Or.inr fun _ _ hX _ hc =>
      NbrInnerMore.not_markedModel_char_ne_two_triD4 h.1 hX hc)
    (fun _ _ _ _ hlab h => NbrInnerMore.largeEvenLabelAll_outdiagPrime_of_subset_inn
      (TableBExcSmallRest.largeEvenLabelAll_subset_inn_triD4 hlab h.1))
    (fun _ _ _ _ hlab h _ _ hX _ hlab' hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_triD4Three hlab h hX hlab' hc' hX' c)

theorem ggNbrInnerWeylOn_residual_of_open (h : GGNbrInnerWeylOn GGNbrWeylResidualOpenLabel) :
    GGNbrInnerWeylOn GGNbrWeylResidualLabel :=
  (h.or ggNbrInnerWeylOn_nsTriD4Three).mono fun p lab hr => by
    by_cases hT : GGNbrNsTriD4ThreeLabel p lab
    · exact Or.inr hT
    · exact Or.inl ⟨hr, hT⟩

end Main

end CFSG.StandardType

end
