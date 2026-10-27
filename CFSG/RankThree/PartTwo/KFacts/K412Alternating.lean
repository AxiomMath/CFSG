module

public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating10

public section

namespace CFSG.RankThree.PartTwo.KFacts.K412

open Equiv Subgroup CFSG.RankThree.PartTwo.KFacts.KP2

@[expose] def normSevenAlt : Subgroup (Perm (Fin 7)) :=
  normalizer (eNine : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)

theorem centralizer_eNine : centralizer (eNine : Set (Perm (Fin 7))) = eNine := by
  apply le_antisymm
  · intro x hx
    rw [mem_centralizer_iff] at hx
    by_contra hne
    exact forall_not_of_card_filter_eq_zero card_filter_centralizer_eNine x
      ⟨(hx _ cOne_mem_eNine).symm, (hx _ cTwo_mem_eNine).symm, fun ⟨i, j, h⟩ => hne ⟨i, j, h⟩⟩
  · rintro _ ⟨i, j, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨k, l, rfl⟩
    exact eNineF_comm k l i j

theorem conj_eNineF : ∀ i j : Fin 3, ∃ i' j' : Fin 3,
    rFour * eNineF i j * rFour⁻¹ = eNineF i' j' := by
  decide +kernel

theorem conj_inv_eNineF : ∀ i j : Fin 3, ∃ i' j' : Fin 3,
    rFour⁻¹ * eNineF i j * rFour = eNineF i' j' := by
  decide +kernel

theorem rFour_mem_normSevenAlt : rFour ∈ normSevenAlt := by
  refine mem_inf.2 ⟨mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩, rFour_spec.1⟩
  · obtain ⟨i, j, rfl⟩ := hx
    exact conj_eNineF i j
  · obtain ⟨i, j, hij⟩ := hx
    obtain ⟨i', j', h⟩ := conj_inv_eNineF i j
    refine ⟨i', j', ?_⟩
    rw [show x = rFour⁻¹ * (rFour * x * rFour⁻¹) * rFour by group, hij, h]

@[expose] def GoodElt (x : Perm (Fin 10)) : Prop :=
  x ≠ 1 ∧ (x.support.card = 3 ∨ x.support.card = 9)

instance : DecidablePred GoodElt := fun x =>
  inferInstanceAs (Decidable (x ≠ 1 ∧ (x.support.card = 3 ∨ x.support.card = 9)))

@[expose] def PairGood (x y : Perm (Fin 10)) : Prop :=
  ∃ a b : Fin 3, GoodElt (x ^ (a : ℕ) * y ^ (b : ℕ))

instance (x y : Perm (Fin 10)) : Decidable (PairGood x y) :=
  inferInstanceAs (Decidable (∃ a b : Fin 3, GoodElt (x ^ (a : ℕ) * y ^ (b : ℕ))))

theorem hyperplane_check : ∀ p q : Fin 3 × Fin 3 × Fin 3,
    (eTwentySevenF p.1 p.2.1 p.2.2).support.card = 6 → eTwentySevenF q.1 q.2.1 q.2.2 ≠ 1 →
    eTwentySevenF q.1 q.2.1 q.2.2 ≠ eTwentySevenF p.1 p.2.1 p.2.2 →
    eTwentySevenF q.1 q.2.1 q.2.2 ≠ eTwentySevenF p.1 p.2.1 p.2.2 ^ 2 →
    PairGood (eTwentySevenF p.1 p.2.1 p.2.2) (eTwentySevenF q.1 q.2.1 q.2.2) := by
  decide +kernel

theorem support_card_cases : ∀ i j k : Fin 3, eTwentySevenF i j k ≠ 1 →
    (eTwentySevenF i j k).support.card = 3 ∨ (eTwentySevenF i j k).support.card = 6 ∨
      (eTwentySevenF i j k).support.card = 9 := by
  decide +kernel

theorem exists_support_card_of_card_nine {B : Subgroup (Perm (Fin 10))} (hB : B ≤ eTwentySeven)
    (h9 : Nat.card B = 9) : ∃ b ∈ B, b ≠ 1 ∧ (b.support.card = 3 ∨ b.support.card = 9) := by
  obtain ⟨x, hxB, hx1⟩ : ∃ x ∈ B, x ≠ 1 := by
    rcases B.bot_or_exists_ne_one with h | h
    · rw [h] at h9
      simp at h9
    · exact h
  obtain ⟨i, j, k, rfl⟩ := hB hxB
  rcases support_card_cases i j k hx1 with h | h | h
  · exact ⟨_, hxB, hx1, Or.inl h⟩
  swap
  · exact ⟨_, hxB, hx1, Or.inr h⟩
  obtain ⟨y, hyB, hy1, hy2, hy3⟩ : ∃ y ∈ B, y ≠ 1 ∧ y ≠ eTwentySevenF i j k ∧
      y ≠ eTwentySevenF i j k ^ 2 := by
    by_contra hne
    push Not at hne
    have hle : B ≤ zpowers (eTwentySevenF i j k) := fun y hy => by
      by_cases h1 : y = 1
      · rw [h1]
        exact one_mem _
      by_cases h2 : y = eTwentySevenF i j k
      · rw [h2]
        exact mem_zpowers _
      · rw [hne y hy h1 h2]
        exact pow_mem (mem_zpowers _) 2
    have hcard := Subgroup.card_le_of_le hle
    rw [h9, Nat.card_zpowers, orderOf_eq_prime (eTwentySevenF_pow_three i j k) hx1] at hcard
    omega
  obtain ⟨i', j', k', rfl⟩ := hB hyB
  obtain ⟨a, b, hab1, hab⟩ := hyperplane_check (i, j, k) (i', j', k') h hy1 hy2 hy3
  exact ⟨_, mul_mem (pow_mem hxB _) (pow_mem hyB _), hab1, hab⟩

end CFSG.RankThree.PartTwo.KFacts.K412
