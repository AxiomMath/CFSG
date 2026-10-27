module

public import CFSG.RankThree.PartOne.S11c.CentralWitness

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.Classical CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.RankThreeEven (localRank)

section Unitary

theorem unitary_model_cover {Y : Type} [Group Y] {n ℓ f : ℕ} (hℓ : ℓ.Prime) (hn : 1 ≤ n)
    (hmod : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSU n ℓ f) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData ℓ f K) (φ : Y →* unitaryPSU h n),
      Function.Surjective φ ∧ φ.ker ≤ Subgroup.center Y := by
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hmod
  have h : UnitaryFieldData ℓ f K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  let e' : (Y ⧸ Subgroup.center Y) ≃* unitaryPSU h n := e.trans (unitaryPSUEquiv h hn).symm
  refine ⟨K, inferInstance, h, e'.toMonoidHom.comp (QuotientGroup.mk' _),
    e'.surjective.comp (QuotientGroup.mk'_surjective _), fun x hx => ?_⟩
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
  exact hx

theorem two_ne_zero_of_ne_two {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  have : CharP K p := h.charP
  intro h0
  have h1 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h0)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp h1)

theorem unitary_even_witness_absurd {X : Type} [Group X] [Finite X] {Y : Subgroup X}
    {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    (φ : Y →* unitaryPSU h n) (hφ : Function.Surjective φ) (hZ : φ.ker ≤ Subgroup.center Y)
    (hrank : localRank p X ≤ 3) {r : ℕ} (hr : 1 ≤ r) (hn : 2 * r < n)
    (h6 : 6 ≤ f * r ^ 2) : False := by
  have : Fact p.Prime := ⟨h.prime⟩
  have h2 := two_ne_zero_of_ne_two h hp2
  obtain ⟨P, hP⟩ := exists_evenFrame h h2 (n := n) (r := r) hn.le
  have hP' : hadj h P * P = frameGram r (n - 2 * r) K := hP
  have hnm : 2 * r + (n - 2 * r) = n := by omega
  obtain ⟨hU, hUcard⟩ := unitary_even_summand_unipotent h hn P hP
  obtain ⟨z, hz2, hz1, V, hV, hVel, r', hr', hVcard⟩ :=
    exists_rank_four_of_central_witness φ hφ hZ h.prime hp2
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).2 hU) hUcard h6
      (evenInvolution_ne_one h hP' hnm h2 hr (by omega))
      (evenInvolution_sq h hP' hnm) (fun _ hu => evenInvolution_comm h hP' hnm hu)
  have := le_localRank_of_rank_four_witness (G := X) (Y := Y) h.prime.one_lt
    ⟨z, hz2, hz1, V, hV, hVel, r', hr', hVcard⟩
  omega

theorem unitary_four_witness_absurd {X : Type} [Group X] [Finite X] {Y : Subgroup X}
    {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    (φ : Y →* unitaryPSU h 4) (hφ : Function.Surjective φ) (hZ : φ.ker ≤ Subgroup.center Y)
    (hrank : localRank p X ≤ 3) (h6 : 6 ≤ 2 * f) : False := by
  have : Fact p.Prime := ⟨h.prime⟩
  have h2 := two_ne_zero_of_ne_two h hp2
  obtain ⟨P, hP⟩ := exists_fourFrame h h2
  have hP' : hadj h P * P = hypGram2 2 K := hP
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have hη0 : c - h.bar c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have hη : h.bar (c - h.bar c) = -(c - h.bar c) := by rw [map_sub, h.bar_bar, neg_sub]
  obtain ⟨hU, hUcard⟩ := unitary_four_paired_root h P hP hη0 hη
  obtain ⟨z, hz2, hz1, V, hV, hVel, r', hr', hVcard⟩ :=
    exists_rank_four_of_central_witness φ hφ hZ h.prime hp2
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).2 hU) hUcard h6
      (fourInvolution_ne_one h hP' h2) (fourInvolution_sq h hP')
      (fun _ hu => fourInvolution_comm h hP' hη hu)
  have := le_localRank_of_rank_four_witness (G := X) (Y := Y) h.prime.one_lt
    ⟨z, hz2, hz1, V, hV, hVel, r', hr', hVcard⟩
  omega

theorem unitary_small_parameters {X : Type} [Group X] [Finite X] {Y : Subgroup X} {n ℓ f : ℕ}
    (hn : 3 ≤ n) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hmod : StatedClassicalModel (↥Y ⧸ Subgroup.center ↥Y) .PSU n ℓ f)
    (hrank : localRank ℓ X ≤ 3) :
    (n ≤ 4 ∨ (ℓ = 3 ∧ f = 1 ∧ (n = 5 ∨ n = 6))) ∧
      (f ≤ 3 ∨ (ℓ = 3 ∧ n = 3 ∧ (f = 4 ∨ f = 5))) := by
  obtain ⟨K, _, h, φ, hφ, hZ⟩ := unitary_model_cover hℓ (by omega) hmod
  have hf : 1 ≤ f := h.one_le
  rcases Nat.lt_or_ge 3 ℓ with h3 | h3
  ·
    obtain ⟨-, -, hr, -⟩ := unitary_defining_prime_central_cover_two_local_rank_witness (G := X) Y
      h h3 hn φ hφ hZ
    refine ⟨Or.inl ?_, Or.inl ?_⟩
    · by_contra hn4
      have h1 := (hr 2 (by norm_num) (by omega)).trans hrank
      have h4 : 4 ≤ f * 2 ^ 2 := by omega
      omega
    · by_contra hf3
      have h1 := (hr 1 le_rfl (by omega)).trans hrank
      omega
  ·
    have hℓ3 : ℓ = 3 := by
      have := hℓ.two_le
      omega
    subst hℓ3
    have h7 : 7 ≤ n → False := fun h7 =>
      unitary_even_witness_absurd h hℓ2 φ hφ hZ hrank (r := 3) (by norm_num) (by omega)
        (by omega)
    have h56 : 5 ≤ n → 2 ≤ f → False := fun h5 hf2 =>
      unitary_even_witness_absurd h hℓ2 φ hφ hZ hrank (r := 2) (by norm_num) (by omega)
        (by omega)
    have h4f : n = 4 → 3 ≤ f → False := fun h4 hf3 => by
      subst h4
      exact unitary_four_witness_absurd h hℓ2 φ hφ hZ hrank (by omega)
    have hf6 : 6 ≤ f → False := fun hf6 =>
      unitary_even_witness_absurd h hℓ2 φ hφ hZ hrank (r := 1) le_rfl (by omega) (by omega)
    refine ⟨?_, ?_⟩
    · by_cases hn4 : n ≤ 4
      · exact Or.inl hn4
      · refine Or.inr ⟨rfl, ?_, ?_⟩
        · by_contra hne
          exact h56 (by omega) (by omega)
        · by_contra hne
          exact h7 (by omega)
    · by_cases hf3 : f ≤ 3
      · exact Or.inl hf3
      · refine Or.inr ⟨rfl, ?_, ?_⟩
        · by_contra hne
          have h5 : f ≤ 5 := by
            by_contra h
            exact hf6 (by omega)
          by_cases hn4 : n = 4
          · exact h4f hn4 (by omega)
          · have : 5 ≤ n := by omega
            exact h56 this (by omega)
        · by_contra hne
          have h5 : f ≤ 5 := by
            by_contra h
            exact hf6 (by omega)
          omega

end Unitary

end CFSG.RankThree.PartOne
