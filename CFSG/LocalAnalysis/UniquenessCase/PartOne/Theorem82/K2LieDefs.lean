module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def K2Simple : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (fam : LieFam811) (r f : ℕ), IsLieFam811 X fam r f →
    Subgroup.center X = ⊥ →
    ∀ R : Subgroup (MulAut X), IsPGroup 3 R →
      CFSG.ABGLocalTools.IsSylowOf 3 (R ⊓ innAut X) (innAut X) → ¬ R ≤ innAut X →
      4 ≤ pRank 3 R

@[expose] def Exists3 (X : Type) [Group X] : Prop :=
  (∃ φ : MulAut X, φ ∉ innAut X ∧ ∃ k : ℕ, φ ^ 3 ^ k = 1) →
    ∃ ψ : MulAut X, ψ ^ 3 = 1 ∧ ψ ∉ innAut X

@[expose] def OuterFixed3 (X : Type) [Group X] [Finite X] : Prop :=
  ∀ ψ : MulAut X, ψ ^ 3 = 1 → ψ ∉ innAut X → 3 ≤ CFSG.Open.pRank 3 (fixedSubgroup ψ)

theorem exists3_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : Exists3 X') : Exists3 X := by
  rintro ⟨φ, hφ, k, hφk⟩
  have hinner : (innAut X).map (MulAut.congr e).toMonoidHom = innAut X' :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e
  have hφ' : MulAut.congr e φ ∉ innAut X' := by
    rw [← hinner]
    rintro ⟨η, hη, hηφ⟩
    exact hφ ((MulAut.congr e).injective hηφ ▸ hη)
  obtain ⟨ψ', hψ'3, hψ'notin⟩ :=
    h ⟨MulAut.congr e φ, hφ', k, by rw [← map_pow, hφk, map_one]⟩
  refine ⟨(MulAut.congr e).symm ψ', ?_, ?_⟩
  · rw [← map_pow, hψ'3, map_one]
  · intro hmem
    exact hψ'notin (by
      rw [← hinner]
      exact ⟨(MulAut.congr e).symm ψ', hmem, MulEquiv.apply_symm_apply _ _⟩)

theorem exists_pow_three_eq_one_of_pow_three_pow_eq_one {G : Type*} [Group G] {x : G} {k : ℕ}
    (hx : x ≠ 1) (h : x ^ 3 ^ k = 1) : ∃ y : G, y ^ 3 = 1 ∧ y ≠ 1 := by
  have hdvd : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hjpos : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0, pow_zero] at hj
      exact absurd (orderOf_eq_one_iff.mp hj) hx
    · exact hpos
  refine ⟨x ^ 3 ^ (j - 1), ?_, ?_⟩
  · rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hjpos, ← hj]
    exact pow_orderOf_eq_one x
  · intro h1
    have hd : orderOf x ∣ 3 ^ (j - 1) := orderOf_dvd_of_pow_eq_one h1
    rw [hj] at hd
    have hlt : 3 ^ (j - 1) < 3 ^ j := by
      rw [← Nat.sub_add_cancel hjpos]
      exact Nat.pow_lt_pow_succ (by norm_num : 1 < 3)
    exact absurd (Nat.le_of_dvd (pow_pos (by norm_num) _) hd) (not_le.mpr hlt)

theorem mem_of_pow_three_pow_mem_of_relIndex_two_pow {G : Type*} [Group G] {I D : Subgroup G}
    [I.Normal] {j n : ℕ} (hj : I.relIndex D = 2 ^ j) {δ : G} (hδD : δ ∈ D)
    (hδn : δ ^ 3 ^ n ∈ I) : δ ∈ I := by
  set y : D := ⟨δ, hδD⟩
  have h1 : orderOf (y : D ⧸ I.subgroupOf D) ∣ 3 ^ n :=
    orderOf_dvd_of_pow_eq_one (by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hδn)
  have h2 : orderOf (y : D ⧸ I.subgroupOf D) ∣ 2 ^ j := by
    rw [← hj, Subgroup.relIndex, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (y : D ⧸ I.subgroupOf D) = 1 :=
    Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow n j ((Nat.coprime_primes Nat.prime_three Nat.prime_two).mpr (by norm_num)))
      h1 h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h3
  exact h3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
