
module

public import CFSG.Quasithin.Background.A3StructureFacts

public section

namespace CFSG.Quasithin.A36B

open CFSG.Open

variable {X : Type} [Group X]

theorem isPerfect_of_hyp (h : A36BHyp X) : Group.IsPerfect X :=
  ⟨by rw [_root_.commutator_def]; exact h.perfect⟩

theorem normal_le_radical (h : A36BHyp X) {N : Subgroup X} [N.Normal] (hN : N ≠ ⊤) :
    N ≤ CFSG.solvableRadical X := by
  have := h.finite
  have := isPerfect_of_hyp h
  have := h.simple
  set O := CFSG.solvableRadical X with hO
  have hmapN : (N.map (QuotientGroup.mk' O)).Normal :=
    Subgroup.Normal.map ‹N.Normal› _ (QuotientGroup.mk'_surjective O)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' O)) with hb | ht
  · intro x hx
    have hx' : QuotientGroup.mk' O x ∈ N.map (QuotientGroup.mk' O) := ⟨x, hx, rfl⟩
    rw [hb, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
    exact hx'
  · exfalso
    have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp O.subtype) := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
      have hx : QuotientGroup.mk' O x ∈ N.map (QuotientGroup.mk' O) := by
        rw [ht]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hnx⟩ := hx
      have hmem : n⁻¹ * x ∈ O := QuotientGroup.eq.1 hnx
      refine ⟨⟨n⁻¹ * x, hmem⟩, ?_⟩
      change QuotientGroup.mk' N (n⁻¹ * x) = QuotientGroup.mk' N x
      have h1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).2 hn
      rw [map_mul, map_inv, h1, inv_one, one_mul]
    have : Group.IsSolvable O := A3.solvableRadical_isSolvable
    have : Group.IsSolvable (X ⧸ N) := Group.isSolvable_of_surjective hsurj
    have : Nontrivial (X ⧸ N) :=
      Finite.one_lt_card_iff_nontrivial.1 (Subgroup.one_lt_index_of_ne_top hN)
    exact Group.IsPerfect.not_isSolvable (X ⧸ N) inferInstance

theorem radical_ne_top (h : A36BHyp X) : CFSG.solvableRadical X ≠ ⊤ := by
  intro htop
  have := h.simple
  have : Subsingleton (X ⧸ CFSG.solvableRadical X) := by
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  exact (not_nontrivial_iff_subsingleton.2 this) IsSimpleGroup.toNontrivial

theorem fitting_le_radical [Finite X] : CFSG.fittingSubgroup X ≤ CFSG.solvableRadical X :=
  A3.le_solvableRadical inferInstance inferInstance

theorem odd_card_fitting (h : A36BHyp X) : Odd (Nat.card (CFSG.fittingSubgroup X)) := by
  have := h.finite
  rw [Nat.odd_iff]
  by_contra hne
  have hdvd : 2 ∣ Nat.card (CFSG.fittingSubgroup X) := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent (CFSG.fittingSubgroup X) := inferInstance
  obtain ⟨S⟩ : Nonempty (Sylow 2 (CFSG.fittingSubgroup X)) := inferInstance
  have hS : S.map (CFSG.fittingSubgroup X).subtype ≤ CFSG.pCore 2 X :=
    Sylow.map_le_pCore inferInstance hnil 2 S
  rw [h.o2, le_bot_iff] at hS
  have hS1 : (S : Subgroup (CFSG.fittingSubgroup X)) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (CFSG.fittingSubgroup X).subtype_injective).1 hS
  have hcard : Nat.card S = 1 := by rw [hS1]; exact Subgroup.card_bot
  have hS2 : 2 ∣ Nat.card S := by
    have := Sylow.dvd_card_of_dvd_card S hdvd
    exact this
  rw [hcard] at hS2
  omega

@[expose] def IsPi (X : Type) [Group X] (q : ℕ) : Prop :=
  ¬ CFSG.pCore q X ≤ Subgroup.center X

theorem fitting_eq_iSup_primes [Finite X] :
    CFSG.fittingSubgroup X = ⨆ q : Nat.Primes, CFSG.pCore (q : ℕ) X := by
  apply le_antisymm
  · rw [CFSG.fitting_eq_sup_pCore X]
    exact iSup_le fun r =>
      le_iSup_of_le ⟨r.1.1, Nat.prime_of_mem_primeFactors r.1.2⟩ le_rfl
  · refine iSup_le fun q => ?_
    have := Fact.mk q.2
    exact CFSG.pCore_le_fitting X q

theorem exists_isPi (h : A36BHyp X) : ∃ q : ℕ, q.Prime ∧ IsPi X q := by
  have := h.finite
  by_contra hcon
  push Not at hcon
  apply h.noncentral
  rw [fitting_eq_iSup_primes]
  refine iSup_le fun q => ?_
  by_contra hq
  exact hcon q q.2 hq

theorem IsPi.ne_two (h : A36BHyp X) {q : ℕ} (hq : IsPi X q) : q ≠ 2 := by
  rintro rfl
  apply hq
  rw [h.o2]
  exact bot_le

end CFSG.Quasithin.A36B
