module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreCl
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryOutdiag
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClHerm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

@[expose] def GGNbrNsUnitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ 4 ≤ lab.rank ∧ ¬ p ∣ 2 ^ lab.n + 1 ∧ (lab.rank = 5 → ¬ p ∣ 2 ^ lab.n - 1)

namespace NbrInnerMore

theorem mem_range_conj_of_pow_of_coprime {R : Type} [Group R] {D : Subgroup (MulAut R)} {p : ℕ}
    (hcop : Nat.Coprime ((MulAut.conj : R →* MulAut R).range.relIndex D) p) {φ : MulAut R}
    (hφ : φ ∈ D) (hφp : φ ^ p = 1) : φ ∈ (MulAut.conj : R →* MulAut R).range := by
  set N := (MulAut.conj : R →* MulAut R).range with hN
  have h1 : (⟨φ, hφ⟩ : D) ^ (N.subgroupOf D).index ∈ N.subgroupOf D :=
    Subgroup.pow_index_mem _ _
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow] at h1
  have hcop' : Nat.Coprime (N.relIndex D) (orderOf φ) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hφp) hcop
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop'
  rw [← hm]
  exact Subgroup.pow_mem _ h1 m

theorem ggOutdiagPrime_unitary_of_not_dvd {d n p : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hq : ¬(d = 3 ∧ 2 ^ n = 2))
    (hp : p.Prime) (hpq : ¬ p ∣ 2 ^ n + 1) :
    GGOutdiagPrime p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  have h : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK hn
  have hd1 : 1 ≤ d := by omega
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcard⟩ :=
    unitary_prime_form_full_semilinear_realization h (isPrimeFormGram_one (K := K) (n := d)) hd hq
  intro φ hφ hφp
  have hidx : (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →* _).range.relIndex
      (InndiagSU.inndiagU h hd1) ∣ 2 ^ n + 1 := by
    rw [InndiagSU.range_conj_eq_comap_inner h hd1, InndiagSU.inndiagU, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective
        (MulAut.congr (InndiagSU.projEquiv h hd1)).surjective]
    exact hcard
  exact mem_range_conj_of_pow_of_coprime
    (Nat.Coprime.coprime_dvd_left hidx ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq).symm)
    (InndiagSU.congr_mem_primeFormD h hd1 hK hφ) hφp

theorem largeEvenLabelAll_outdiagPrime_unitary {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twA) (hq : ¬ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagPrime p R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hq
  subst ht
  obtain ⟨hn, hl, hl2⟩ := hlab
  dsimp only at hl hl2
  have hq' : ¬(l + 1 = 3 ∧ 2 ^ n = 2) := by
    rintro ⟨h3, h2⟩
    have h4 : 4 ≤ 2 ^ n := by
      have := hl2 (by omega)
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) this
    omega
  intro Q hQ
  obtain ⟨K, _, _, hK, hq''⟩ := hQ
  exact ⟨K, inferInstance, inferInstance, hK, hq'',
    ggOutdiagPrime_unitary_of_not_dvd hK hn (show 3 ≤ l + 1 by omega) hq' hp hq⟩

theorem halfSplit_twA_cases {p l n : ℕ} {c : Prop} (h : LargeEvenHalfSplit p ⟨.twA, l, n⟩ c) :
    p ∣ 2 ^ n + 1 ∨ (n = 1 ∧ p = 3) ∨ (l = 5 ∧ p ∣ 2 ^ n - 1) := by
  rcases h with (⟨hu, -⟩ | ⟨-, -, h⟩ | ⟨ht, -⟩ | h) | ⟨ht, -⟩ | ⟨ht, h⟩ | h | h | h
  · exact absurd hu id
  · exact Or.inl h
  · simp at ht
  · exact Or.inr (Or.inl h)
  · simp at ht
  · rcases ht with ⟨-, hl⟩ | ht
    · exact Or.inr (Or.inr ⟨hl, h⟩)
    · simp at ht
  · simp at h
  · simp at h
  · simp at h

section TypeDet

theorem not_halfSplit_of_markedModel_unit {p : ℕ} {lab : LargeEvenLabel}
    (h : GGNbrNsUnitLabel p lab) {X : Type} [Group X] (hX : MarkedModel lab X)
    {lab' : LargeEvenLabel} (hc' : markChar lab' = 2) (hX' : MarkedModel lab' X) (c : Prop) :
    ¬ LargeEvenHalfSplit p lab' c := by
  obtain ⟨ht, hl, hq2, h5⟩ := h
  have hL : LieModel X .PSU (lab.rank + 1) 2 lab.n := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact hX
  have hL' := lieModel_of_markedModel_two hc' hX'
  obtain ⟨hT, hR, hD⟩ := CFSG.SeitzReduction.UnitaryPilot.sumEvenTypeDetAt (by omega) X lab.n
    _ _ _ hL (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hL') hL'
  obtain ⟨hU, hDn⟩ := ClNonsplit.unitaryLabel_of_markTag_PSU hT hc'
  intro hHS
  obtain ⟨t', l', n'⟩ := lab'
  rcases hU with ht' | ⟨ht', hl3⟩ <;> dsimp only at ht' <;> subst ht'
  · have hn' : n' = lab.n := hDn.symm.trans hD
    have hl' : l' = lab.rank := by
      simp only [markRank] at hR
      omega
    subst hn' hl'
    rcases halfSplit_twA_cases hHS with h1 | ⟨hn1, hp3⟩ | ⟨hl5, h1⟩
    · exact hq2 h1
    · rw [hn1, hp3] at hq2
      exact hq2 (by norm_num)
    · exact h5 hl5 h1
  · dsimp only at hl3
    subst hl3
    simp [markRank] at hR
    omega

theorem not_markedModel_char_ne_two_unit {lab : LargeEvenLabel} (ht : lab.tag = .twA)
    (hl : 4 ≤ lab.rank) {X : Type} [Group X] (hX : MarkedModel lab X) {lab' : LargeEvenLabel}
    (hc : markChar lab' ≠ 2) : ¬ MarkedModel lab' X := by
  have hL : LieModel X .PSU (lab.rank + 1) 2 lab.n := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact hX
  exact not_markedModel_of_char_ne_two hL (fun h => absurd h.1 (by decide))
    (fun h => absurd h.1 (by decide)) (fun h => by omega) hc

end TypeDet

end NbrInnerMore

section Labels

theorem ggTableBNbrInnerInputOn_nsUnit : GGTableBNbrInnerInputOn GGNbrNsUnitLabel :=
  ggTableBNbrInnerInputOn_of_clauseFive
    (fun _ _ h => Or.inr fun _ _ hX _ hc =>
      NbrInnerMore.not_markedModel_char_ne_two_unit h.1 h.2.1 hX hc)
    (fun _ _ hp _ hlab h =>
      (NbrInnerMore.largeEvenLabelAll_outdiagPrime_unitary hp hlab h.1 h.2.2.1).mono
        fun _ _ _ _ h _ _ => h)
    (fun _ _ _ _ _ h _ _ hX _ _ hc' hX' c =>
      NbrInnerMore.not_halfSplit_of_markedModel_unit h hX hc' hX' c)

end Labels

end CFSG.StandardType

end
