module

public import CFSG.Quasithin.SteinbergUnitaryOuterPrimeControl
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime
public import CFSG.LocalAnalysis.SectionRank.OddCover.ScalarCover
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyEvenOrthogonal

public section

namespace CFSG.Quasithin.H13.NQTerm

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  (perfect_symplectic_central_quotient_outer_prime_control)

noncomputable def statedProjSLEquivProjectiveSL (n : ℕ) (K : Type) [Field K] :
    StatedProj (StatedSL n K) ≃* LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K :=
  (projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
    (LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)

theorem sqt_classical_central_quotient_outer_prime_control (J : Type) [Group J] [Finite J]
    [Group.IsPerfect J] (hSQT : CFSG.IsStronglyQuasithin (J ⧸ Subgroup.center J))
    (hrep : CFSG.Milestones.ClassicalRep (J ⧸ Subgroup.center J)) :
    ∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ →
      (∀ P : Sylow ℓ (Outer J), IsCyclic P) ∧ CFSG.pRank ℓ (Outer J) ≤ 1 := by
  intro ℓ hℓ hℓ5
  have hS : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (⊤ : Subgroup (J ⧸ Subgroup.center J)) ≤ 2 :=
    SectionRank.isStronglyQuasithin_iff.1 hSQT
  obtain ⟨t, n, p, f, hm⟩ := hrep
  have hp : p.Prime := hm.1.1
  have hf : 1 ≤ f := hm.1.2.1
  have hodd : p ≠ 2 → t = .PSL ∨ t = .PSU := fun hp2 => by
    rcases SectionRank.sqt_odd_classical_restriction hS hp2 hm with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩
    · exact .inl ht
    · exact .inl ht
    · exact .inr ht
  cases t with
  | PSL =>
    obtain ⟨⟨-, -, hn, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
    have hnd : ¬ ℓ ∣ Nat.gcd n (Nat.card K - 1) := by
      intro hdvd
      have hℓn : ℓ ∣ n := hdvd.trans (Nat.gcd_dvd_left _ _)
      have hℓq : ℓ ∣ p ^ f - 1 := hK ▸ hdvd.trans (Nat.gcd_dvd_right _ _)
      have hn5 : 5 ≤ n := hℓ5.trans (Nat.le_of_dvd (by omega) hℓn)
      have : Fact ℓ.Prime := ⟨hℓ⟩
      have hrank := (SectionRank.OddCover.scalar_quotient_diagonal_torus_rank (K := K) hp hn
        (r := ℓ) (by omega) (H := StatedSL n K) (.inl ⟨hK, rfl, hℓq⟩)
        ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) le_rfl).1
      have h2 := hS ℓ hℓ (by omega)
      rw [SectionRank.pRank_top_eq_of_mulEquiv hℓ.one_lt e] at h2
      omega
    exact (OuterPrimeControl.perfect_projective_linear_central_quotient_outer_prime_control J K
      hn (e.trans (statedProjSLEquivProjectiveSL n K))).1 ℓ hℓ (by omega) hnd
  | PSU =>
    obtain ⟨⟨-, -, hn, hq⟩, K, _, _, hK, ⟨e⟩⟩ := hm
    have hu : LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
      ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    have hnd : ¬ ℓ ∣ Nat.gcd n (p ^ f + 1) := by
      intro hdvd
      have hℓn : ℓ ∣ n := hdvd.trans (Nat.gcd_dvd_left _ _)
      have hℓq : ℓ ∣ p ^ f + 1 := hdvd.trans (Nat.gcd_dvd_right _ _)
      have hn5 : 5 ≤ n := hℓ5.trans (Nat.le_of_dvd (by omega) hℓn)
      have : Fact ℓ.Prime := ⟨hℓ⟩
      have hrank := (SectionRank.OddCover.scalar_quotient_diagonal_torus_rank (K := K) hp
        (by omega : 2 ≤ n) (r := ℓ) (by omega) (H := StatedSU n (p ^ f) K) (.inr ⟨hK, rfl, hℓq⟩)
        ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K)) le_rfl).1
      have h2 := hS ℓ hℓ (by omega)
      rw [SectionRank.pRank_top_eq_of_mulEquiv hℓ.one_lt e] at h2
      omega
    exact (OuterPrimeControl.perfect_unitary_central_quotient_outer_prime_control hu hn
      (fun h => hq (by rw [h.1, h.2])) J
      (e.trans (ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hu (by omega)).symm)).2.1 ℓ hℓ hnd
  | PSp =>
    obtain ⟨⟨-, -, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
    have h := perfect_symplectic_central_quotient_outer_prime_control hp hf hn hK J ⟨e⟩
    exact ⟨h.1 ℓ hℓ (by omega), h.2.1 ℓ hℓ (by omega)⟩
  | POmegaOdd =>
    have hp2 : p ≠ 2 := hm.1.2.2.2
    rcases hodd hp2 with h | h <;> exact absurd h (by decide)
  | POmegaPlus =>
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨⟨-, -, hn⟩, K, _, _, hK, ⟨e⟩⟩ := hm
      have : Finite (StatedProj (StatedOmega (StatedQuadPlus n K))) :=
        Finite.of_equiv _ e.toEquiv
      exact (QuasithinUnique.Setup.Family.even_orthogonal_plus_not_sqt hK hn
        (SectionRank.isStronglyQuasithin_of_mulEquiv e.symm hSQT)).elim
    · rcases hodd hp2 with h | h <;> exact absurd h (by decide)
  | POmegaMinus =>
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨⟨-, -, hn⟩, K, _, _, hK, b, c, hbc, ⟨e⟩⟩ := hm
      have : Finite (StatedProj (StatedOmega (StatedQuadMinus n K b c))) :=
        Finite.of_equiv _ e.toEquiv
      exact (QuasithinUnique.Setup.Family.even_orthogonal_minus_not_sqt hK hn b c hbc
        (SectionRank.isStronglyQuasithin_of_mulEquiv e.symm hSQT)).elim
    · rcases hodd hp2 with h | h <;> exact absurd h (by decide)
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
    exact hm.2.elim

end CFSG.Quasithin.H13.NQTerm
