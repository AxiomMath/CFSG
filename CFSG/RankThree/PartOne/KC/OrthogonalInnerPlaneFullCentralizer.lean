module

public import CFSG.RankThree.PartOne.KC.OrthogonalSplitPrimeModel
public import CFSG.RankThree.PartOne.KC.OrthogonalNonbinaryModel

public section

open CFSG CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

namespace CFSG.RankThree.PartOne

theorem not_dvd_sq_sub_one {p q : ℕ} (hp : p.Prime) (h1 : ¬ p ∣ q - 1) (h2 : ¬ p ∣ q + 1) :
    ¬ p ∣ q ^ 2 - 1 := by
  intro h
  have h' : p ∣ (q + 1) * (q - 1) := by
    have := Nat.sq_sub_sq q 1
    rw [one_pow] at this
    rw [← this]
    exact h
  rcases hp.dvd_mul.mp h' with h3 | h3
  · exact h2 h3
  · exact h1 h3

@[expose] def ModelOrthogonalFullCentralizer (G : Type) [Group G] (t : StatedLieTag)
    (n ℓ f p : ℕ) : Prop :=
  p.Prime → 3 < p → p ≠ ℓ →
  match t with
  | .POmegaOdd => ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
      G ≃* StatedProj (StatedOmega (StatedQuadOdd n K)) →
        CommonLayerCentralizerTrivial (matrixProjectiveDerived (coordinateQuadOdd n K)) p
  | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
      G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)) →
        CommonLayerCentralizerTrivial (matrixProjectiveDerived (coordinateQuadPlus n K)) p
  | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
      ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)) →
        CommonLayerCentralizerTrivial
          (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) p
  | _ => False

theorem orthogonal_inner_plane_local_components_full_automorphism_centralizer (G : Type) [Group G]
    (t : StatedLieTag) (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (n ℓ f p : ℕ) (h : StatedClassicalModel G t n ℓ f) :
    ModelOrthogonalFullCentralizer G t n ℓ f p := by
  intro hp hp3 hpℓ
  have hsplit := orthogonal_split_prime_common_centralizer G t ht n ℓ f p h hp hp3 hpℓ
  have hqp := orthogonal_inner_plane_common_centralizer_q_plus_one G t ht n ℓ f p h hp hp3 hpℓ
  have hnb := orthogonal_inner_plane_common_centralizer_nonbinary_primes G t ht n ℓ f p h hp hp3 hpℓ
  by_cases h1 : p ∣ ℓ ^ f - 1
  · rcases ht with rfl | rfl | rfl
    · exact hsplit h1
    · exact hsplit h1
    · exact hsplit h1
  by_cases h2 : p ∣ ℓ ^ f + 1
  · rcases ht with rfl | rfl | rfl
    · exact hqp h2
    · exact hqp h2
    · exact hqp h2
  have h3 : ¬ p ∣ ℓ ^ (2 * f) - 1 := by
    rw [pow_mul']
    exact not_dvd_sq_sub_one hp h1 h2
  rcases ht with rfl | rfl | rfl
  · exact hnb h3
  · exact hnb h3
  · exact hnb h3

end CFSG.RankThree.PartOne
