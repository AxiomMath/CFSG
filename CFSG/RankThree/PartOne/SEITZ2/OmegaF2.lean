module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaPair
public import CFSG.Timmesfeld.Orders.ClassicalOmega

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix QuadraticMap CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.PartOne.CTP
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

@[expose] def SubfieldPairOmega8mSmall : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (k : Subfield K) (σ : K ≃+* K) (p : ℕ) (b c : k)
    (h : OmegaSetup K k σ p 1 b c), (p = 5 ∨ p = 7 ∨ p = 17) →
    ∀ d ∈ (linearConjugationHom (omegaQuad K (b : K) (c : K))).range,
      (fixedSubgroup (fieldAutT (omegaQuad K (b : K) (c : K)) σ
        (h.quad_invariant (by norm_num) h.order))).map d.toMonoidHom ≠
          fixedSubgroup (fieldAutT (omegaQuad K (b : K) (c : K)) σ
            (h.quad_invariant (by norm_num) h.order)) →
      Subgroup.closure ((fixedSubgroup (fieldAutT (omegaQuad K (b : K) (c : K)) σ
          (h.quad_invariant (by norm_num) h.order)) :
          Set (matrixProjectiveDerived (omegaQuad K (b : K) (c : K)))) ∪
        ((fixedSubgroup (fieldAutT (omegaQuad K (b : K) (c : K)) σ
          (h.quad_invariant (by norm_num) h.order))).map d.toMonoidHom :
          Set (matrixProjectiveDerived (omegaQuad K (b : K) (c : K))))) = ⊤

theorem prime_dvd_card_omega {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hd : p ∣ 197406720) :
    p = 5 ∨ p = 7 ∨ p = 17 := by
  have h : (197406720 : ℕ) = 2 ^ 12 * 3 ^ 4 * 5 * 7 * 17 := by norm_num
  rw [h] at hd
  have key : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hpq =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 hpq
  rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
  · rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
    · rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
      · rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
        · have := key 2 Nat.prime_two (hp.dvd_of_dvd_pow hd)
          omega
        · have := key 3 Nat.prime_three (hp.dvd_of_dvd_pow hd)
          omega
      · have := key 5 Nat.prime_five hd
        omega
    · have := key 7 (by norm_num) hd
      omega
  · have := key 17 (by norm_num) hd
    omega

section Order

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {σ : K ≃+* K} {p : ℕ} {b c : k}

theorem card_fixed_omega_two (h : OmegaSetup K k σ p 1 b c) :
    Nat.card (fixedSubgroup (fieldAutT (omegaQuad K (b : K) (c : K)) σ
      (h.quad_invariant (by norm_num) h.order))) = 197406720 := by
  have : CharP K 2 := h.charP
  have : Finite k := Finite.of_injective (algebraMap k K) (algebraMap k K).injective
  rw [fixed_eq_derivedImage h]
  have e1 : Nat.card ↥(subfieldDerivedImage k (omega_isExtension (k := k) (b := b) (c := c))) =
      Nat.card (matrixProjectiveDerived (omegaQuad k b c)) :=
    (Nat.card_congr (inclEquiv k (omega_isExtension (k := k) (b := b) (c := c))
      (by norm_num)).toEquiv).symm
  have e2 : Nat.card (matrixProjectiveDerived (omegaQuad k b c)) =
      Nat.card (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedOmega
        (CFSG.Assembly.LowTwoRank.StatedQuadMinus 4 k b c))) :=
    (Nat.card_congr (omegaModel (K := k) b c).toEquiv).symm
  have e3 := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus (K := k)
    (n := 4) (le_refl 4) (b := b) (c := c) h.irr
  have hk : Nat.card k = 2 := by
    rw [h.card_k]
    norm_num
  rw [hk] at e3
  rw [e1, e2]
  have e4 : (Nat.card (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedOmega
      (CFSG.Assembly.LowTwoRank.StatedQuadMinus 4 k b c))) : ℤ) = 197406720 := by
    rw [e3]
    decide +kernel
  exact_mod_cast e4

end Order

theorem subfieldPairOmega8mF2_of_small (h : SubfieldPairOmega8mSmall) : SubfieldPairOmega8mF2 := by
  intro K _ _ k σ p f₀ b c hs hf d hd hne
  have hf1 : f₀ = 1 := hf
  subst hf1
  by_cases hp : p = 5 ∨ p = 7 ∨ p = 17
  · left
    exact h K k σ p b c hs hp d hd hne
  · right
    intro hdvd
    rw [card_fixed_omega_two hs] at hdvd
    exact hp (prime_dvd_card_omega hs.prime hs.five_le hdvd)

theorem subfieldPairOmega8m_of_small (h : SubfieldPairOmega8mSmall) :
    SubfieldPairOmega8m :=
  subfieldPairOmega8m_of_f2 (subfieldPairOmega8mF2_of_small h)

end CFSG.RankThree.PartOne.SEITZ2
