module

public import CFSG.RankThree.PartTwo.Sec8.Hering418FMinus
public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofCases
public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofCrossLin
public import CFSG.RankThree.PartTwo.Sec8.Hering418R47

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSU)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def IsLThreeSixOdd (X : Type) [Group X] : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ 3 ∣ k ∧ Odd k ∧ Nonempty (X ≃* projSL 3 (GaloisField 2 k))

@[expose] def IsLThreeSixEven (X : Type) [Group X] : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ 3 ∣ k ∧ Even k ∧ Nonempty (X ≃* projSL 3 (GaloisField 2 k))

@[expose] def IsUThreeSixEven (X : Type) [Group X] : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ 3 ∣ k ∧ Even k ∧ Nonempty (X ≃* projSU 3 2 k)

@[expose] def IsUThreeSixOdd (X : Type) [Group X] : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ 3 ∣ k ∧ Odd k ∧ Nonempty (X ≃* projSU 3 2 k)

@[expose] def IsSLThreeSixOdd (X : Type) [Group X] : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ 3 ∣ k ∧ Odd k ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
    Nat.card K = 2 ^ k ∧ Nonempty (X ≃* StatedSL 3 K)

@[expose] def IsSLThreeSixEven (X : Type) [Group X] : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ 3 ∣ k ∧ Even k ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
    Nat.card K = 2 ^ k ∧ Nonempty (X ≃* StatedSL 3 K)

@[expose] def IsSUThreeSixEven (X : Type) [Group X] : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ 3 ∣ k ∧ Even k ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
    Nat.card K = (2 ^ k) ^ 2 ∧ Nonempty (X ≃* StatedSU 3 (2 ^ k) K)

@[expose] def IsSUThreeSixOdd (X : Type) [Group X] : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ 3 ∣ k ∧ Odd k ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
    Nat.card K = (2 ^ k) ^ 2 ∧ Nonempty (X ≃* StatedSU 3 (2 ^ k) K)

theorem isLThreeSix_iff {X : Type} [Group X] :
    IsLThreeSix X ↔ IsLThreeSixOdd X ∨ IsLThreeSixEven X := by
  constructor
  · rintro ⟨k, hk, h3, h⟩
    rcases Nat.even_or_odd k with he | ho
    · exact Or.inr ⟨k, hk, h3, he, h⟩
    · exact Or.inl ⟨k, hk, h3, ho, h⟩
  · rintro (⟨k, hk, h3, -, h⟩ | ⟨k, hk, h3, -, h⟩)
    · exact ⟨k, hk, h3, h⟩
    · exact ⟨k, hk, h3, h⟩

theorem isUThreeSix_iff {X : Type} [Group X] :
    IsUThreeSix X ↔ IsUThreeSixEven X ∨ IsUThreeSixOdd X := by
  constructor
  · rintro ⟨k, hk, h3, h⟩
    rcases Nat.even_or_odd k with he | ho
    · exact Or.inl ⟨k, hk, h3, he, h⟩
    · exact Or.inr ⟨k, hk, h3, ho, h⟩
  · rintro (⟨k, hk, h3, -, h⟩ | ⟨k, hk, h3, -, h⟩)
    · exact ⟨k, hk, h3, h⟩
    · exact ⟨k, hk, h3, h⟩

theorem isSLThreeSix_iff {X : Type} [Group X] :
    IsSLThreeSix X ↔ IsSLThreeSixOdd X ∨ IsSLThreeSixEven X := by
  constructor
  · rintro ⟨k, hk, h3, K, hKf, hKfin, hK, h⟩
    rcases Nat.even_or_odd k with he | ho
    · exact Or.inr ⟨k, hk, h3, he, K, hKf, hKfin, hK, h⟩
    · exact Or.inl ⟨k, hk, h3, ho, K, hKf, hKfin, hK, h⟩
  · rintro (⟨k, hk, h3, -, K, hKf, hKfin, hK, h⟩ | ⟨k, hk, h3, -, K, hKf, hKfin, hK, h⟩)
    · exact ⟨k, hk, h3, K, hKf, hKfin, hK, h⟩
    · exact ⟨k, hk, h3, K, hKf, hKfin, hK, h⟩

theorem isSUThreeSix_iff {X : Type} [Group X] :
    IsSUThreeSix X ↔ IsSUThreeSixEven X ∨ IsSUThreeSixOdd X := by
  constructor
  · rintro ⟨k, hk, h3, K, hKf, hKfin, hK, h⟩
    rcases Nat.even_or_odd k with he | ho
    · exact Or.inl ⟨k, hk, h3, he, K, hKf, hKfin, hK, h⟩
    · exact Or.inr ⟨k, hk, h3, ho, K, hKf, hKfin, hK, h⟩
  · rintro (⟨k, hk, h3, -, K, hKf, hKfin, hK, h⟩ | ⟨k, hk, h3, -, K, hKf, hKfin, hK, h⟩)
    · exact ⟨k, hk, h3, K, hKf, hKfin, hK, h⟩
    · exact ⟨k, hk, h3, K, hKf, hKfin, hK, h⟩

theorem two_pow_mod_three_of_odd' {k : ℕ} (hk : Odd k) : 2 ^ k % 3 = 2 := by
  obtain ⟨m, rfl⟩ := hk
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem two_pow_mod_three_of_even' {k : ℕ} (hk : Even k) : 2 ^ k % 3 = 1 := by
  obtain ⟨m, rfl⟩ := hk
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem nonempty_statedSL_mulEquiv_projSL {k : ℕ} (hk : 1 ≤ k) (hq : 2 ^ k % 3 = 2) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ k) :
    Nonempty (StatedSL 3 K ≃* projSL 3 (GaloisField 2 k)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKmod : Nat.card K % 3 = 2 := by rw [hK]; exact hq
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (GaloisField 2 k) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 k) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 k (by omega)]
  let ψ : K ≃+* GaloisField 2 k := FiniteField.ringEquivOfCardEq hcard
  let e2 : Matrix.SpecialLinearGroup (Fin 3) K ≃* projectiveSL 3 K :=
    MulEquiv.ofBijective (proj 3 K) ⟨KFacts.proj_three_injective hKmod, proj_surjective 3 K⟩
  exact ⟨(CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm.trans
    (e2.trans ((Sec21.Item223CensusResProof.psOfSL (Sec21.Item223CensusResProof.slEquiv ψ 3)).trans
      (Sec4.projSLEquivProjectiveSL 3 (GaloisField 2 k)).symm))⟩

theorem IsLThreeSixOdd.isMinusPiSix {X : Type} [Group X] (h : IsLThreeSixOdd X) :
    IsMinusPiSix X := by
  obtain ⟨k, hk, ⟨n, rfl⟩, ho, ⟨φ⟩⟩ := h
  exact ⟨n, by omega, Or.inr ⟨two_pow_mod_three_of_odd' ho, ⟨φ⟩⟩⟩

theorem IsUThreeSixEven.isMinusPiSix {X : Type} [Group X] (h : IsUThreeSixEven X) :
    IsMinusPiSix X := by
  obtain ⟨k, hk, ⟨n, rfl⟩, he, ⟨φ⟩⟩ := h
  exact ⟨n, by omega, Or.inl ⟨two_pow_mod_three_of_even' he, ⟨φ⟩⟩⟩

theorem IsSLThreeSixOdd.isMinusPiSix {X : Type} [Group X] (h : IsSLThreeSixOdd X) :
    IsMinusPiSix X := by
  obtain ⟨k, hk, ⟨n, rfl⟩, ho, K, _, _, hK, ⟨φ⟩⟩ := h
  obtain ⟨ψ⟩ := nonempty_statedSL_mulEquiv_projSL hk (two_pow_mod_three_of_odd' ho) hK
  exact ⟨n, by omega, Or.inr ⟨two_pow_mod_three_of_odd' ho, ⟨φ.trans ψ⟩⟩⟩

theorem IsSUThreeSixEven.isMinusPiSix {X : Type} [Group X] (h : IsSUThreeSixEven X) :
    IsMinusPiSix X := by
  obtain ⟨k, hk, ⟨n, rfl⟩, he, K, _, _, hK, ⟨φ⟩⟩ := h
  obtain ⟨ψ⟩ := Item82OneProof.nonempty_statedSU_mulEquiv_projSU hk
    (two_pow_mod_three_of_even' he) hK
  exact ⟨n, by omega, Or.inl ⟨two_pow_mod_three_of_even' he, ⟨φ.trans ψ⟩⟩⟩

section Reduction

theorem kF418ModelOn_lThreeSix_of_even (h : KF418ModelOn (fun X _ => IsLThreeSixEven X)) :
    KF418ModelOn (fun X _ => IsLThreeSix X) := by
  intro G _ _ L hL hl
  rcases isLThreeSix_iff.mp hl with h1 | h1
  · exact kF418ModelOn_minusPiSix G L hL h1.isMinusPiSix
  · exact h G L hL h1

theorem kF418ModelOn_uThreeSix_of_odd (h : KF418ModelOn (fun X _ => IsUThreeSixOdd X)) :
    KF418ModelOn (fun X _ => IsUThreeSix X) := by
  intro G _ _ L hL hl
  rcases isUThreeSix_iff.mp hl with h1 | h1
  · exact kF418ModelOn_minusPiSix G L hL h1.isMinusPiSix
  · exact h G L hL h1

theorem kF418ModelOn_slThreeSix_of_even (h : KF418ModelOn (fun X _ => IsSLThreeSixEven X)) :
    KF418ModelOn (fun X _ => IsSLThreeSix X) := by
  intro G _ _ L hL hl
  rcases isSLThreeSix_iff.mp hl with h1 | h1
  · exact kF418ModelOn_minusPiSix G L hL h1.isMinusPiSix
  · exact h G L hL h1

theorem kF418ModelOn_suThreeSix_of_odd (h : KF418ModelOn (fun X _ => IsSUThreeSixOdd X)) :
    KF418ModelOn (fun X _ => IsSUThreeSix X) := by
  intro G _ _ L hL hl
  rcases isSUThreeSix_iff.mp hl with h1 | h1
  · exact kF418ModelOn_minusPiSix G L hL h1.isMinusPiSix
  · exact h G L hL h1

section Full

theorem kF418Faithful_of_families47' (h46 : Sec4.Item4_6) (h47 : Sec4.Item4_7)
    (hAS : CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418.KF418ModelAltSpor)
    (hL3 : KF418ModelOn (fun X _ => IsLThreeSixEven X))
    (hU3 : KF418ModelOn (fun X _ => IsUThreeSixOdd X))
    (hSL : KF418ModelOn (fun X _ => IsSLThreeSixEven X))
    (hSU : KF418ModelOn (fun X _ => IsSUThreeSixOdd X))
    (hD4 : KF418ModelOn (fun X _ => IsTrialityD4Six X))
    (hrank : Sec21.TwistedF4EvenThreeRankTwo)
    (hU4 : KF418ModelOn47 (fun X _ => IsUFourSix X)) : KF418Faithful :=
  kF418Faithful_of_families47 h46 h47 hAS (kF418ModelOn_lThreeSix_of_even hL3)
    (kF418ModelOn_uThreeSix_of_odd hU3) (kF418ModelOn_slThreeSix_of_even hSL)
    (kF418ModelOn_suThreeSix_of_odd hSU) hD4 hrank hU4

end Full

end Reduction

end CFSG.RankThree.PartTwo.Sec8.Hering418
