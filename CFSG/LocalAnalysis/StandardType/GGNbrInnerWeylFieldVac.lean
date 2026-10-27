module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylOpenLabels
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylClauseFive

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrWeylFieldVacA2Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrWeylFieldLabel p lab ∧ lab.tag = .A ∧ lab.rank = 2 ∧ p ≠ 3 ∧
    ¬ p ∣ 2 ^ lab.n - 1 ∧ ¬ p ∣ 2 ^ lab.n + 1

section Main

theorem not_halfSplit_of_markedModel_linTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (ht : lab.tag = .A) (hl : lab.rank = 2)
    (h13 : ¬ (lab.n = 1 ∧ p = 3)) (hq1 : ¬ p ∣ 2 ^ lab.n - 1)
    {X : Type} [Group X] (hX : MarkedModel lab X) {lab' : LargeEvenLabel}
    (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) (c : Prop) :
    ¬ LargeEvenHalfSplit p lab' c := by
  have hL : CFSG.Blueprint.LieModel X .PSL (lab.rank + 1) 2 lab.n := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact hX
  obtain ⟨hT, hR, hD⟩ := CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique (by omega) hL
    (NbrInnerMore.lieModel_of_markedModel_two hc' hX')
  intro hHS
  obtain ⟨t', l', n'⟩ := lab'
  rcases LinNonsplit.markPSL_cases hT hc' hD with ⟨ht', hn'⟩ | ⟨ht', -⟩ | ⟨ht', -⟩ <;>
    dsimp only at ht' <;> subst ht'
  · dsimp only at hn'
    subst hn'
    have hl' : l' = lab.rank := by
      simp only [markRank] at hR
      omega
    subst hl'
    rcases NbrInnerMore.halfSplit_A_cases hHS with h1 | h1 | h1 | h1
    · exact hq1 h1
    · exact h13 h1
    · omega
    · omega
  · by_cases hl3 : l' = 3
    · simp only [markRank, hl3, ↓reduceIte] at hR
      omega
    · simp [markTag, hl3] at hT
  · by_cases hl2 : l' = 2
    · simp only [markRank, hl2, ↓reduceIte] at hR
      omega
    · by_cases hl3 : l' = 3 <;> simp [markTag, hl2, hl3] at hT

theorem ggNbrInnerWeylOn_fieldVacA2 : GGNbrInnerWeylOn GGNbrWeylFieldVacA2Label :=
  ggNbrInnerWeylOn_of_clauseFive
    (fun _ _ hS => Or.inl hS.2.2.2.1)
    (fun _ _ hp _ hlab hS =>
      (NbrInnerMore.largeEvenLabelAll_outdiagPrime_linear hp hlab hS.2.1 hS.2.2.2.2.1).mono
        fun _ _ _ _ h _ _ => h)
    (fun _ _ hp hp2 _ hS _ _ hX _ _ hc' hX' c =>
      not_halfSplit_of_markedModel_linTwo hp hp2 hS.2.1 hS.2.2.1
        (fun h => hS.2.2.2.1 h.2) hS.2.2.2.2.1 hX hc' hX' c)

end Main

end CFSG.StandardType

end
