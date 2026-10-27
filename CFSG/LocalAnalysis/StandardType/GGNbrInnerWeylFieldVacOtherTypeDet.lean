module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreExcB
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreU
public import CFSG.LocalAnalysis.EvenBN.GMSK.TypeDetBender
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.G2EvenOuterTypeDet

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint

namespace NbrInnerMore

theorem halfSplit_D_cases {p l n : ℕ} {c : Prop} (h : LargeEvenHalfSplit p ⟨.D, l, n⟩ c) :
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

theorem halfSplit_twD_cases {p l n : ℕ} {c : Prop} (h : LargeEvenHalfSplit p ⟨.twD, l, n⟩ c) :
    p ∣ 2 ^ n + 1 ∨ p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3) := by
  rcases h with (⟨hu, -⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | h) | ⟨ht, -⟩ | ⟨ht, -⟩ | h | h | h
  · exact absurd hu id
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · simp at ht
  · simp at ht
  · simp at h
  · simp at h
  · simp at h

theorem halfSplit_G2_cases {p l n : ℕ} {c : Prop} (h : LargeEvenHalfSplit p ⟨.G2, l, n⟩ c) :
    p ∣ 2 ^ n - 1 ∨ (n = 1 ∧ p = 3) := by
  rcases h with (⟨-, h⟩ | ⟨hu, -⟩ | ⟨ht, -⟩ | h) | ⟨ht, -⟩ | ⟨ht, -⟩ | h | h | h
  · exact Or.inl h
  · exact absurd trivial hu
  · simp at ht
  · exact Or.inr h
  · simp at ht
  · simp at ht
  · simp at h
  · simp at h
  · simp at h

section TypeDet

theorem not_halfSplit_of_markedModel_twA2 {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twA) (hl : lab.rank = 2)
    (hq : ¬ p ∣ 2 ^ lab.n + 1) {X : Type} [Group X] (hX : MarkedModel lab X)
    {lab' : LargeEvenLabel} (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) (c : Prop) :
    ¬ LargeEvenHalfSplit p lab' c := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hl hq
  subst ht hl
  obtain ⟨-, -, hn2⟩ := hlab
  have hn2' : 2 ≤ n := hn2 rfl
  have hL : LieModel X .PSU 3 2 n := hX
  have hL' := lieModel_of_markedModel_two hc' hX'
  obtain ⟨hT, hR, hD⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.su3EvenTypeDet X n _ _ _ hL
    (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hL') hL'
  obtain ⟨hU, hDn⟩ := ClNonsplit.unitaryLabel_of_markTag_PSU hT hc'
  intro hHS
  obtain ⟨t', l', n'⟩ := lab'
  rcases hU with ht' | ⟨ht', hl3⟩ <;> dsimp only at ht' <;> subst ht'
  · have hn' : n' = n := hDn.symm.trans hD
    have hl' : l' = 2 := by
      simp only [markRank] at hR
      omega
    subst hn' hl'
    rcases halfSplit_twA_cases hHS with h1 | ⟨hn1, -⟩ | ⟨hl5, -⟩
    · exact hq h1
    · omega
    · omega
  · dsimp only at hl3
    subst hl3
    simp [markRank] at hR

theorem not_markedModel_char_ne_two_twA2 {lab : LargeEvenLabel} (ht : lab.tag = .twA)
    (hl : lab.rank = 2) {X : Type} [Group X] (hX : MarkedModel lab X) {lab' : LargeEvenLabel}
    (hc : markChar lab' ≠ 2) : ¬ MarkedModel lab' X := by
  have hL : LieModel X .PSU 3 2 lab.n := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht hl
    subst ht hl
    exact hX
  exact not_markedModel_of_char_ne_two hL (fun h => absurd h.1 (by decide))
    (fun h => absurd h.1 (by decide)) (fun h => absurd h.2.1 (by decide)) hc

theorem not_halfSplit_of_markedModel_linThree {p : ℕ} {lab : LargeEvenLabel}
    (ht : lab.tag = .A ∨ lab.tag = .D) (hl : lab.rank = 3) (hq1 : ¬ p ∣ 2 ^ lab.n - 1)
    (hq2 : ¬ p ∣ 2 ^ lab.n + 1) {X : Type} [Group X] (hX : MarkedModel lab X)
    {lab' : LargeEvenLabel} (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) (c : Prop) :
    ¬ LargeEvenHalfSplit p lab' c := by
  have hp3 : p ≠ 3 := LinNonsplit.ne_three_of_not_dvd hq1 hq2
  have hL : LieModel X .PSL 4 2 lab.n := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht hl
    subst hl
    rcases ht with rfl | rfl <;> exact hX
  obtain ⟨hT, hR, hD⟩ := CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique (by omega) hL
    (lieModel_of_markedModel_two hc' hX')
  intro hHS
  obtain ⟨t', l', n'⟩ := lab'
  rcases LinNonsplit.markPSL_cases hT hc' hD with ⟨ht', hn'⟩ | ⟨ht', hn'⟩ | ⟨ht', -⟩ <;>
    dsimp only at ht' <;> subst ht'
  · dsimp only at hn'
    subst hn'
    have hl' : l' = 3 := by
      simp only [markRank] at hR
      omega
    subst hl'
    rcases halfSplit_A_cases hHS with h1 | ⟨-, h1⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hq1 h1
    · exact hp3 h1
    · omega
    · omega
  · dsimp only at hn'
    subst hn'
    rcases halfSplit_D_cases hHS with h1 | h1 | ⟨-, h1⟩
    · exact hq1 h1
    · exact hq2 h1
    · exact hp3 h1
  · by_cases hl2 : l' = 2
    · simp only [markRank, hl2, ↓reduceIte] at hR <;> omega
    · by_cases hl3 : l' = 3 <;> simp [markTag, hl2, hl3] at hT

theorem not_halfSplit_of_markedModel_unitThree {p : ℕ} {lab : LargeEvenLabel}
    (ht : lab.tag = .twA ∨ lab.tag = .twD) (hl : lab.rank = 3) (hq1 : ¬ p ∣ 2 ^ lab.n - 1)
    (hq2 : ¬ p ∣ 2 ^ lab.n + 1) {X : Type} [Group X] (hX : MarkedModel lab X)
    {lab' : LargeEvenLabel} (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) (c : Prop) :
    ¬ LargeEvenHalfSplit p lab' c := by
  have hp3 : p ≠ 3 := LinNonsplit.ne_three_of_not_dvd hq1 hq2
  have hL : LieModel X .PSU 4 2 lab.n := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht hl
    subst hl
    rcases ht with rfl | rfl <;> exact hX
  have hL' := lieModel_of_markedModel_two hc' hX'
  obtain ⟨hT, hR, hD⟩ := CFSG.SeitzReduction.UnitaryPilot.sumEvenTypeDetAt (by omega) X lab.n
    _ _ _ hL (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hL') hL'
  obtain ⟨hU, hDn⟩ := ClNonsplit.unitaryLabel_of_markTag_PSU hT hc'
  intro hHS
  obtain ⟨t', l', n'⟩ := lab'
  rcases hU with ht' | ⟨ht', hl3⟩ <;> dsimp only at ht' <;> subst ht'
  · have hn' : n' = lab.n := hDn.symm.trans hD
    have hl' : l' = 3 := by
      simp only [markRank] at hR
      omega
    subst hn' hl'
    rcases halfSplit_twA_cases hHS with h1 | ⟨-, h1⟩ | ⟨h1, -⟩
    · exact hq2 h1
    · exact hp3 h1
    · omega
  · have hn' : n' = lab.n := hDn.symm.trans hD
    dsimp only at hl3
    subst hn' hl3
    rcases halfSplit_twD_cases hHS with h1 | h1 | ⟨-, h1⟩
    · exact hq2 h1
    · exact hq1 h1
    · exact hp3 h1

theorem eq_of_markedModel_G2 {X : Type} [Group X] {n : ℕ} (hX : LieModel X .G2 0 2 n)
    {lab' : LargeEvenLabel} (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) :
    lab'.tag = .G2 ∧ lab'.n = n := by
  obtain ⟨hT, hD⟩ := CFSG.EvenSporadicStandard.Induction.lieModel_G2_two_unique hX
    (lieModel_of_markedModel_two hc' hX')
  obtain ⟨t, l, k⟩ := lab'
  cases t
  case G2 => exact ⟨rfl, hD⟩
  all_goals exfalso
  all_goals first
    | (simp only [markTag] at hT <;> contradiction)
    | (simp only [markTag] at hT
       split_ifs at hT <;> contradiction)

theorem not_halfSplit_of_markedModel_G2 {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .G2) (hq : ¬ p ∣ 2 ^ lab.n - 1)
    {X : Type} [Group X] (hX : MarkedModel lab X) {lab' : LargeEvenLabel}
    (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) (c : Prop) :
    ¬ LargeEvenHalfSplit p lab' c := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hq
  subst ht
  obtain ⟨-, -, hn2⟩ := hlab
  have hn2' : 2 ≤ n := hn2
  obtain ⟨ht', hn'⟩ := eq_of_markedModel_G2 hX hc' hX'
  intro hHS
  obtain ⟨t', l', n'⟩ := lab'
  dsimp only at ht' hn'
  subst ht' hn'
  rcases halfSplit_G2_cases hHS with h1 | ⟨h1, -⟩
  · exact hq h1
  · omega

theorem not_markedModel_char_ne_two_G2 {lab : LargeEvenLabel} (ht : lab.tag = .G2)
    {X : Type} [Group X] (hX : MarkedModel lab X) {lab' : LargeEvenLabel}
    (hc : markChar lab' ≠ 2) : ¬ MarkedModel lab' X := by
  have hL : LieModel X .G2 0 2 lab.n := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact hX
  exact not_markedModel_of_char_ne_two hL (fun h => absurd h.1 (by decide))
    (fun h => absurd h.1 (by decide)) (fun h => absurd h.1 (by decide)) hc

theorem not_halfSplit_of_markedModel_twF4Plus {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twF4) (hq : ¬ p ∣ 2 ^ lab.n + 1)
    {X : Type} [Group X] (hX : MarkedModel lab X) {lab' : LargeEvenLabel}
    (hlab' : LargeEvenInLambda2 lab') (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X)
    (c : Prop) : ¬ LargeEvenHalfSplit p lab' c := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hq
  subst ht
  obtain ⟨-, -, -, hn3⟩ := hlab
  have hn3' : 3 ≤ n := hn3
  obtain ⟨ht', hn'⟩ := eq_of_markedModel_twF4 hn3' hX hlab' hc' hX'
  intro hHS
  obtain ⟨t', l', n'⟩ := lab'
  dsimp only at ht' hn'
  subst ht' hn'
  rcases halfSplit_twF4_cases hHS with h1 | ⟨h1, -⟩
  · exact hq h1
  · omega

theorem not_markedModel_char_ne_two_twF4 {lab : LargeEvenLabel} (ht : lab.tag = .twF4)
    {X : Type} [Group X] (hX : MarkedModel lab X) {lab' : LargeEvenLabel}
    (hc : markChar lab' ≠ 2) : ¬ MarkedModel lab' X := by
  have hL : LieModel X .twistedF4 0 2 lab.n := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact hX
  exact not_markedModel_of_char_ne_two hL (fun h => absurd h.1 (by decide))
    (fun h => absurd h.1 (by decide)) (fun h => absurd h.1 (by decide)) hc

end TypeDet

theorem largeEvenLabelAll_outdiagPrime_twD3 {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twD) (hl : lab.rank = 3)
    (hq : ¬ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagPrime p R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hl hq
  subst ht hl
  obtain ⟨hn, -⟩ := hlab
  intro Q hQ
  obtain ⟨K, _, _, hK, hq''⟩ := hQ
  exact ⟨K, inferInstance, inferInstance, hK, hq'',
    ggOutdiagPrime_unitary_of_not_dvd hK hn (by omega) (by omega) hp hq⟩

end NbrInnerMore

end CFSG.StandardType

end
