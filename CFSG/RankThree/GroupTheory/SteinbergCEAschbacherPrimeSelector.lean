module

public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.GroupTheory

open CFSG.Assembly.RankThreeEven

theorem aschbacher_prime_selector (G : Type*) [Group G] [Finite G] :
    let S₁ := {p : ℕ | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ 3 < localRank p G}
    let S₂ := {p : ℕ | p.Prime ∧ 5 < p ∧ p ∣ Nat.card G ∧ localRank p G = 3}
    let S₃ := {p : ℕ | p.Prime ∧ 3 < p ∧ p ∣ Nat.card G ∧ localRank p G = 3}
    let S₄ := {p : ℕ | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ localRank p G = 3}
    (S₁.Nonempty → sigmaA G = S₁) ∧
    (S₁ = ∅ → S₂.Nonempty → sigmaA G = S₂) ∧
    (S₁ = ∅ → S₂ = ∅ → S₃.Nonempty → sigmaA G = S₃) ∧
    (S₁ = ∅ → S₂ = ∅ → S₃ = ∅ → S₄.Nonempty → sigmaA G = S₄) ∧
    (S₁ = ∅ → S₂ = ∅ → S₃ = ∅ → S₄ = ∅ → sigmaA G = ∅) ∧
    S₁.Finite ∧ S₂.Finite ∧ S₃.Finite ∧ S₄.Finite ∧
    ∀ p ∈ sigmaA G, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G := by
  intro S₁ S₂ S₃ S₄
  classical
  have hsig : sigmaA G =
      if S₁.Nonempty then S₁ else if S₂.Nonempty then S₂ else if S₃.Nonempty then S₃ else S₄ :=
    rfl
  have hfin : ∀ S : Set ℕ, (∀ p ∈ S, p ∣ Nat.card G) → S.Finite := fun S hS =>
    (Set.finite_Iic (Nat.card G)).subset fun p hp => Nat.le_of_dvd Nat.card_pos (hS p hp)
  have hne : ∀ S : Set ℕ, S = ∅ → ¬ S.Nonempty := fun S hS => by
    rw [hS]
    exact Set.not_nonempty_empty
  refine ⟨fun h => ?_, fun h1 h => ?_, fun h1 h2 h => ?_, fun h1 h2 h3 _ => ?_,
    fun h1 h2 h3 h4 => ?_, hfin _ fun p hp => hp.2.2.1, hfin _ fun p hp => hp.2.2.1,
    hfin _ fun p hp => hp.2.2.1, hfin _ fun p hp => hp.2.2.1, fun p hp => ?_⟩
  · rw [hsig, ite_eq_left h]
  · rw [hsig, ite_eq_right (hne _ h1), ite_eq_left h]
  · rw [hsig, ite_eq_right (hne _ h1), ite_eq_right (hne _ h2), ite_eq_left h]
  · rw [hsig, ite_eq_right (hne _ h1), ite_eq_right (hne _ h2), ite_eq_right (hne _ h3)]
  · rw [hsig, ite_eq_right (hne _ h1), ite_eq_right (hne _ h2), ite_eq_right (hne _ h3), h4]
  · rw [hsig] at hp
    split_ifs at hp
    · exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
    · exact ⟨hp.1, by have := hp.2.1; omega, hp.2.2.1⟩
    · exact ⟨hp.1, by have := hp.2.1; omega, hp.2.2.1⟩
    · exact ⟨hp.1, hp.2.1, hp.2.2.1⟩

end CFSG.RankThree.GroupTheory
