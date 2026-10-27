module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ContextFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem commutator_barImage_bot (D : Data G) :
    ⁅barImage D.M (⊥ : Subgroup G), CFSG.fittingSubgroup (Bar2 D.M)⁆ = ⊥ := by
  simp [barImage]

private theorem n_eq_pRank_of_ne_bot (D : Data G) (Ch : Choice2011 G)
    (h52 : S23_5_2 D Ch) (hPS : S23_9_PointStab D Ch) (h1930 : H1930 D)
    (c : Ctx23L D Ch) (hKne : Hinf (D.M ⊓ c.L) ≠ ⊥) :
    c.n = CFSG.Open.pRank 2 D.Z := by
  rcases h52 h1930 c with h | ⟨-, hOm, -⟩
  · exact h
  · exact absurd ((hPS h1930 c).2.2 _ hOm) (by simpa using hKne)

private theorem eq_three_of_a1_disj_of_two_pow {n r : ℕ}
    (hcase : (∃ s : ℕ, s ∣ n ∧ Odd s ∧ 1 < s ∧ r ∣ 2 ^ s - 1) ∨
      (∃ k : ℕ, n = 2 ^ k ∧ r = 3))
    (hpow : ∃ k : ℕ, n = 2 ^ k) : r = 3 := by
  rcases hcase with ⟨s, hsdvd, hsodd, hs1, -⟩ | ⟨k, -, hr3⟩
  · exfalso
    obtain ⟨k, hk⟩ := hpow
    have hs2 : s = 1 := by
      obtain ⟨j, -, hj⟩ :=
        (Nat.dvd_prime_pow Nat.prime_two).mp (by simpa [hk] using hsdvd)
      rw [hj] at hsodd
      have hj0 : j = 0 := by
        rwa [Nat.odd_iff, Nat.two_pow_mod_two_eq_one] at hsodd
      rw [hj, hj0, pow_zero]
    omega
  · exact hr3

private theorem exists_odd_dvd_of_a1_disj_of_not_two_pow {n r : ℕ}
    (hcase : (∃ s : ℕ, s ∣ n ∧ Odd s ∧ 1 < s ∧ r ∣ 2 ^ s - 1) ∨
      (∃ k : ℕ, n = 2 ^ k ∧ r = 3))
    (hpow : ¬ ∃ k : ℕ, n = 2 ^ k) :
    ∃ s : ℕ, s ∣ n ∧ Odd s ∧ 1 < s ∧ r ∣ 2 ^ s - 1 := by
  rcases hcase with h | ⟨k, hk, -⟩
  · exact h
  · exact absurd ⟨k, hk⟩ hpow

theorem s23_9_StepA_of (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h52 : S23_5_2 D Ch) (hPS : S23_9_PointStab D Ch)
    (hA0 : S23_9_A0 D Ch) (hA1 : S23_9_A1 D Ch) (hASem : S23_9_ASem D Ch)
    (hAdj : S23_9_Adj D Ch) (hA3 : S23_9_A3 D Ch) (hA4 : S23_9_A4 D Ch)
    (hA5 : S23_9_A5 D Ch) (hK462 : CFSG.LocalAnalysis.UniquenessCase.UCK.K462)
    (hKSU44 : KSU44) (hKAdj : KAdj) (hSem : S23_9_Semireg D Ch) :
    S23_9_StepA D Ch := by
  intro h1930 c h3
  let K : Subgroup G := Hinf (D.M ⊓ c.L)
  change ⁅barImage D.M K, CFSG.fittingSubgroup (Bar2 D.M)⁆ = ⊥
  by_cases hKbot : K = ⊥
  · rw [hKbot]
    exact commutator_barImage_bot D
  · have hKne : K ≠ ⊥ := hKbot
    by_contra hne
    have hV : IsElemAbelian 2 c.V := c.isElemAbelian_V h4 h1930
    have hn : c.n = CFSG.Open.pRank 2 D.Z :=
      n_eq_pRank_of_ne_bot D Ch h52 hPS h1930 c (by simpa [K] using hKne)
    obtain ⟨b, hbB0, r, hrp, hr2, hborder, hbZ, hcase⟩ := hA1 h1930 c h3 hKne hn
    obtain ⟨d, hKact⟩ := hA0 h1930 c h3 hKne hne
    have hfix := hASem h1930 c d b hbB0 r hrp hr2 hborder hbZ
    obtain ⟨a⟩ := hAdj hKAdj h1930 c h3 hV d hKact b hbB0 r hrp hr2 hborder hbZ hcase
    by_cases hpow : ∃ k : ℕ, c.n = 2 ^ k
    · have hr3 : r = 3 := eq_three_of_a1_disj_of_two_pow hcase hpow
      have hq3 : d.q ≠ 3 := fun h3q => hfix.2 (by rw [hr3, h3q])
      by_cases hSU : S23_9_SU44 D Ch c hV
      · exact hA5 h1930 c hV d hSU hKSU44 hSem hq3 hKact
      · exact hA4 h1930 c h3 hV d b hbB0 r hrp hr2 hborder hr3 hfix.1 hfix.2
          hpow hSU a hK462
    · exact hA3 h1930 c hV d b hbB0 r hrp hr2 hborder
        (exists_odd_dvd_of_a1_disj_of_not_two_pow hcase hpow) hfix.1 hfix.2 a hpow

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
