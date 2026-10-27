module

public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer

public section

open Matrix QuadraticMap Polynomial CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

namespace CFSG.RankThree.PartOne.KCOrthogonalSubfield

section Forms

variable {K : Type} [Field K] (k : Subfield K) (n : ℕ)

theorem coordinateQuadOdd_isExtension :
    IsExtension k (coordinateQuadOdd n k) (coordinateQuadOdd n K) := by
  intro v
  rw [coordinateQuadOdd_apply, coordinateQuadOdd_apply]
  simp [vecIncl]

theorem coordinateQuadPlus_isExtension :
    IsExtension k (coordinateQuadPlus n k) (coordinateQuadPlus n K) := by
  intro v
  rw [coordinateQuadPlus_apply, coordinateQuadPlus_apply]
  simp [vecIncl]

theorem coordinateQuadMinus_isExtension (hn : 1 ≤ n) (b c : k) :
    IsExtension k (coordinateQuadMinus n k hn b c)
      (coordinateQuadMinus n K hn (b : K) (c : K)) := by
  intro v
  rw [coordinateQuadMinus_apply, coordinateQuadMinus_apply]
  simp [vecIncl]

theorem coordinateQuadOdd_fieldAut (σ : K ≃+* K) (v : Fin (2 * n + 1) → K) :
    coordinateQuadOdd n K (coordinateFieldMap (2 * n + 1) σ v) = σ (coordinateQuadOdd n K v) := by
  rw [coordinateQuadOdd_apply, coordinateQuadOdd_apply]
  simp [coordinateFieldMap_apply, map_sum, map_mul, map_add, map_pow]

theorem coordinateQuadPlus_fieldAut (σ : K ≃+* K) (v : Fin (2 * n) → K) :
    coordinateQuadPlus n K (coordinateFieldMap (2 * n) σ v) = σ (coordinateQuadPlus n K v) := by
  rw [coordinateQuadPlus_apply, coordinateQuadPlus_apply]
  simp [coordinateFieldMap_apply, map_sum, map_mul]

theorem coordinateQuadMinus_fieldAut (hn : 1 ≤ n) {σ : K ≃+* K} (hσk : ∀ x, x ∈ k ↔ σ x = x)
    (b c : k) (v : Fin (2 * n) → K) :
    coordinateQuadMinus n K hn (b : K) (c : K) (coordinateFieldMap (2 * n) σ v) =
      σ (coordinateQuadMinus n K hn (b : K) (c : K) v) := by
  have hb : σ (b : K) = b := (hσk _).mp b.2
  have hc : σ (c : K) = c := (hσk _).mp c.2
  rw [coordinateQuadMinus_apply, coordinateQuadMinus_apply]
  simp [coordinateFieldMap_apply, map_sum, map_mul, map_add, map_pow, hb, hc]

end Forms

section Degree

theorem rootFree_of_odd_degree {K : Type} [Field K] [Finite K] (k : Subfield K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdeg : Module.finrank k K = p) (b c : k)
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) (s : K) :
    s ^ 2 + (b : K) * s + (c : K) ≠ 0 := by
  intro hs
  have hfd : FiniteDimensional k K := Module.finite_of_finrank_pos (by rw [hdeg]; exact hp.pos)
  have hint : IsIntegral k s := Algebra.IsIntegral.isIntegral s
  have h1 := minpoly.degree_dvd hint
  rw [hdeg] at h1
  have hmon : (X ^ 2 + C b * X + C c : k[X]).Monic := by monicity!
  have hdvd : minpoly k s ∣ (X ^ 2 + C b * X + C c : k[X]) := by
    apply minpoly.dvd
    rw [aeval_def]
    simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
    exact hs
  have h2 : (minpoly k s).natDegree ≤ 2 :=
    (Polynomial.natDegree_le_of_dvd hdvd hmon.ne_zero).trans (by compute_degree!)
  have h3 := (Nat.dvd_prime hp).mp h1
  have hp3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have h4 : (minpoly k s).natDegree = 1 := by
    rcases h3 with h | h
    · exact h
    · omega
  obtain ⟨s₀, hs₀⟩ := minpoly.natDegree_eq_one_iff.mp h4
  apply hirr s₀
  apply Subtype.ext
  have : ((s₀ : K)) = s := hs₀
  push_cast
  rw [this]
  exact hs

theorem finrank_subfield_eq {K : Type} [Field K] [Finite K] (k : Subfield K) {ℓ e p : ℕ}
    (hℓ : ℓ.Prime) (he : 1 ≤ e) (hk : Nat.card k = ℓ ^ e) (hK : Nat.card K = ℓ ^ (e * p)) :
    Module.finrank k K = p := by
  have := Fintype.ofFinite K
  have := Fintype.ofFinite k
  have h1 : Fintype.card K = Fintype.card k ^ Module.finrank k K := Module.card_eq_pow_finrank
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hk, ← pow_mul] at h1
  have h2 := Nat.pow_right_injective hℓ.two_le h1
  exact (Nat.eq_of_mul_eq_mul_left he h2).symm

end Degree

section Setup

variable {K : Type} [Field K] (k : Subfield K) {σ : K ≃+* K}
  (hσk : ∀ x, x ∈ k ↔ σ x = x) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hσ : orderOf σ = p)

theorem two_ne_zero_of_subfield (h2 : (2 : K) ≠ 0) : (2 : k) ≠ 0 := fun h => h2 (by
  have h' : ((2 : k) : K) = ((0 : k) : K) := by rw [h]
  push_cast at h'
  exact h')

include hσk hp hp2 hσ in
theorem subfieldSetup_odd {n : ℕ} (hn : 3 ≤ n) (h2 : (2 : K) ≠ 0) :
    SubfieldSetup k (coordinateQuadOdd n k) (coordinateQuadOdd n K) σ p where
  hext := coordinateQuadOdd_isExtension k n
  hσk := hσk
  hp := hp
  hp2 := hp2
  hσ := hσ
  hQσ := coordinateQuadOdd_fieldAut n σ
  hnd₀ := (regular_coordinateQuadOdd n k (two_ne_zero_of_subfield k h2) hn).1
  hT₀ := (regular_coordinateQuadOdd n k (two_ne_zero_of_subfield k h2) hn).2
  hnd := (regular_coordinateQuadOdd n K h2 hn).1
  hT := (regular_coordinateQuadOdd n K h2 hn).2
  hAP := coordinate_odd_point_action_properties n K h2 hn

include hσk hp hp2 hσ in
theorem subfieldSetup_plus {n : ℕ} (hn : 3 ≤ n) :
    SubfieldSetup k (coordinateQuadPlus n k) (coordinateQuadPlus n K) σ p where
  hext := coordinateQuadPlus_isExtension k n
  hσk := hσk
  hp := hp
  hp2 := hp2
  hσ := hσ
  hQσ := coordinateQuadPlus_fieldAut n σ
  hnd₀ := (regular_coordinateQuadPlus n k hn).1
  hT₀ := (regular_coordinateQuadPlus n k hn).2
  hnd := (regular_coordinateQuadPlus n K hn).1
  hT := (regular_coordinateQuadPlus n K hn).2
  hAP := coordinate_plus_point_action_properties n K hn

include hσk hp hp2 hσ in
theorem subfieldSetup_minus [Finite K] {n : ℕ} (hn : 4 ≤ n)
    (hdeg : Module.finrank k K = p) (b c : k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    SubfieldSetup k (coordinateQuadMinus n k (by omega) b c)
      (coordinateQuadMinus n K (by omega) (b : K) (c : K)) σ p where
  hext := coordinateQuadMinus_isExtension k n (by omega) b c
  hσk := hσk
  hp := hp
  hp2 := hp2
  hσ := hσ
  hQσ := coordinateQuadMinus_fieldAut k n (by omega) hσk b c
  hnd₀ := (regular_coordinateQuadMinus n k b c hn hirr).1
  hT₀ := (regular_coordinateQuadMinus n k b c hn hirr).2
  hnd := (regular_coordinateQuadMinus n K (b : K) (c : K) hn
    (rootFree_of_odd_degree k hp hp2 hdeg b c hirr)).1
  hT := (regular_coordinateQuadMinus n K (b : K) (c : K) hn
    (rootFree_of_odd_degree k hp hp2 hdeg b c hirr)).2
  hAP := coordinate_minus_point_action_properties n K (b : K) (c : K) hn
    (rootFree_of_odd_degree k hp hp2 hdeg b c hirr)

end Setup

end CFSG.RankThree.PartOne.KCOrthogonalSubfield
