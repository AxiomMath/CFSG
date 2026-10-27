module

import CFSG.LocalAnalysis.SignalizerFunctor.AmbientFixedCommutators
public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.Coprime

variable {G : Type*} [Group G]

@[expose] def hyperplanes (p : ℕ) (A : Subgroup G) : Set (Subgroup G) :=
  {B | B ≤ A ∧ Nat.card A = p * Nat.card B}

theorem commutator_eq_iSup_hyperplanes [Finite G] {p : ℕ} (hp : p.Prime) {A X : Subgroup G}
    (hA : IsElemAbelian p A) (hA2 : p ^ 2 ≤ Nat.card A)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hcop : Nat.Coprime p (Nat.card X))
    (hX : Group.IsSolvable X) {t : G} (ht : t ∈ A) :
    ⁅X, Subgroup.zpowers t⁆ = ⨆ B ∈ hyperplanes p A,
      ⁅X ⊓ Subgroup.centralizer (B : Set G), Subgroup.zpowers t⁆ := by
  have : Fact p.Prime := ⟨hp⟩
  have := hA.1
  obtain ⟨r, hr⟩ :=
    (CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p A hA).exists_card_eq
  have hr1 : r ≠ 0 := by
    rintro rfl
    rw [hr] at hA2
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    simp only [pow_zero] at hA2
    omega
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hset : hyperplanes p A = signalizerFunctorEk p s A := by
    ext B
    refine and_congr_right fun _ => ?_
    rw [hr, pow_succ, mul_comm]
    exact (Nat.mul_right_inj hp.ne_zero).trans eq_comm
  have hzA : Subgroup.zpowers t ≤ A := (Subgroup.zpowers_le).mpr ht
  rw [hset]
  refine CFSG.SignalizerFunctor.Helpers.solvable_normalized_order_fixed_commutator_generation p s p
    hp hp A (Subgroup.zpowers t) X hA (by rw [hr, pow_succ]) ?_ hX hAX (hzA.trans hAX) ?_ hcop hcop
  · exact CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p _
      (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p hA hzA)
  · intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (mul_comm' (⟨b, hzA hb⟩ : A) (⟨a, ha⟩ : A))

end CFSG.SignalizerFunctorTheorem.Coprime
