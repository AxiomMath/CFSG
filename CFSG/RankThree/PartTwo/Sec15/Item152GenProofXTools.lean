module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof152Gen

theorem card_eq_one_of_isPerfect_of_isPGroup {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    [Fact p.Prime] (hQ : Group.IsPerfect Q) (hp : IsPGroup p Q) : Nat.card Q = 1 := by
  by_contra hne
  have : Nontrivial Q := (Finite.one_lt_card_iff_nontrivial).mp
    (lt_of_le_of_ne Nat.card_pos (Ne.symm hne))
  have : Group.IsNilpotent Q := hp.isNilpotent
  exact Group.IsPerfect.not_isSolvable Q inferInstance

theorem eq_top_of_isPerfect_of_isPGroup_quotient {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    [Fact p.Prime] (hQ : Group.IsPerfect Q) (N : Subgroup Q) [N.Normal]
    (hN : IsPGroup p (Q ⧸ N)) : N = ⊤ := by
  have hperf : Group.IsPerfect (Q ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have h1 := card_eq_one_of_isPerfect_of_isPGroup hperf hN
  rw [← Subgroup.index_eq_one, Subgroup.index_eq_card]
  exact h1

theorem card_eq_one_of_isPerfect_of_card_dvd_six {Q : Type*} [Group Q] [Finite Q]
    (hQ : Group.IsPerfect Q) (h6 : Nat.card Q ∣ 6) : Nat.card Q = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 Q) := inferInstance
  have hidx3 : ¬ 3 ∣ (P : Subgroup Q).index := Sylow.not_dvd_index P
  have hidx6 : (P : Subgroup Q).index ∣ 2 * 3 :=
    ((P : Subgroup Q).index_dvd_card).trans h6
  have hidx2 : (P : Subgroup Q).index ∣ 2 :=
    (Nat.Coprime.dvd_of_dvd_mul_right
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hidx3).symm hidx6)
  have hPtop : (P : Subgroup Q) = ⊤ := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hidx2 with h1 | h2
    · exact Subgroup.index_eq_one.mp h1
    · have : (P : Subgroup Q).Normal := Subgroup.normal_of_index_eq_two h2
      refine eq_top_of_isPerfect_of_isPGroup_quotient (p := 2) hQ _ (IsPGroup.of_card (n := 1) ?_)
      rw [pow_one, ← Subgroup.index_eq_card, h2]
  have hQ3 : IsPGroup 3 Q := by
    have h := P.isPGroup'
    rw [hPtop] at h
    exact h.of_equiv Subgroup.topEquiv
  exact card_eq_one_of_isPerfect_of_isPGroup hQ hQ3

theorem index_ne_three_of_isPerfect {Q : Type*} [Group Q] [Finite Q] (hQ : Group.IsPerfect Q)
    (M : Subgroup Q) : M.index ≠ 3 := by
  intro h3
  have : M.FiniteIndex := ⟨by rw [h3]; norm_num⟩
  have hdvd : M.normalCore.index ∣ 6 := by
    have h := Subgroup.index_normalCore_dvd_factorial_index M
    rw [h3] at h
    exact h
  have : M.normalCore.Normal := Subgroup.normalCore_normal M
  have hperf : Group.IsPerfect (Q ⧸ M.normalCore) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' M.normalCore)
      (QuotientGroup.mk'_surjective _)
  have h1 : M.normalCore.index = 1 := by
    rw [Subgroup.index_eq_card] at hdvd ⊢
    exact card_eq_one_of_isPerfect_of_card_dvd_six hperf hdvd
  have hM : M = ⊤ := top_le_iff.mp ((Subgroup.index_eq_one.mp h1) ▸ M.normalCore_le)
  rw [hM, Subgroup.index_top] at h3
  norm_num at h3

theorem false_of_isPerfect_of_card_five_mul {Q : Type*} [Group Q] [Finite Q]
    (hQ : Group.IsPerfect Q) {k : ℕ} (hk : 1 ≤ k) (hcard : Nat.card Q = 5 * 2 ^ k)
    (hP5 : ∀ P : Sylow 5 Q, Nat.card (P : Subgroup Q) = 5)
    (hn : ∀ j ≤ k, 2 ^ j ≡ 1 [MOD 5] → j = 0) : False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 Q) := inferInstance
  have hP : Nat.card (P : Subgroup Q) = 5 := hP5 P
  have hidx : (P : Subgroup Q).index = 2 ^ k := by
    have h := (P : Subgroup Q).card_mul_index
    rw [hP, hcard] at h
    omega
  have h1 : Nat.card (Sylow 5 Q) = 1 := by
    have hdvd := Sylow.card_dvd_index P
    rw [hidx] at hdvd
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hmod := card_sylow_modEq_one 5 Q
    rw [hjeq] at hmod ⊢
    rw [hn j hj hmod, pow_zero]
  have : Subsingleton (Sylow 5 Q) := (Nat.card_eq_one_iff_unique.mp h1).1
  have : (P : Subgroup Q).Normal := Sylow.normal_of_subsingleton P
  have hq : IsPGroup 2 (Q ⧸ (P : Subgroup Q)) :=
    IsPGroup.of_card (n := k) (by rw [← Subgroup.index_eq_card, hidx])
  have htop := eq_top_of_isPerfect_of_isPGroup_quotient hQ _ hq
  rw [htop, Subgroup.index_top] at hidx
  have : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

theorem false_of_isPerfect_of_card_twenty {Q : Type*} [Group Q] [Finite Q]
    (hQ : Group.IsPerfect Q) (hcard : Nat.card Q = 20) : False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine false_of_isPerfect_of_card_five_mul hQ (k := 2) (by norm_num)
    (by rw [hcard]; norm_num) ?_ ?_
  · intro P
    rw [Sylow.card_eq_multiplicity, hcard, show (20 : ℕ) = 4 * 5 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_five,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  · intro j hj hmod
    interval_cases j
    · rfl
    · exact absurd hmod (by decide)
    · exact absurd hmod (by decide)

theorem false_of_isPerfect_of_card_forty {Q : Type*} [Group Q] [Finite Q]
    (hQ : Group.IsPerfect Q) (hcard : Nat.card Q = 40) : False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine false_of_isPerfect_of_card_five_mul hQ (k := 3) (by norm_num)
    (by rw [hcard]; norm_num) ?_ ?_
  · intro P
    rw [Sylow.card_eq_multiplicity, hcard, show (40 : ℕ) = 8 * 5 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_five,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  · intro j hj hmod
    interval_cases j
    · rfl
    · exact absurd hmod (by decide)
    · exact absurd hmod (by decide)
    · exact absurd hmod (by decide)

theorem false_of_isPerfect_card_one_hundred_twenty {C : Type*} [Group C] [Finite C]
    (Z : Subgroup C) [Z.Normal] (hZ3 : Nat.card Z = 3)
    (hQ : Group.IsPerfect (C ⧸ Z)) (hQ360 : Nat.card (C ⧸ Z) = 360) (F : Subgroup C)
    (hF : Group.IsPerfect F) (hF120 : Nat.card F = 120) : False := by
  set π := QuotientGroup.mk' Z with hπ
  set F' := F.map π with hF'
  have hF'p : Group.IsPerfect F' := Group.IsPerfect.map _
  have hcard : Nat.card F' * Nat.card (Z ⊓ F : Subgroup C) = 120 := by
    have h1 := Subgroup.relIndex_mul_card π.ker F
    rw [Subgroup.relIndex_ker, hπ, QuotientGroup.ker_mk', hF120] at h1
    exact h1
  have hZF : Nat.card (Z ⊓ F : Subgroup C) ∣ 3 := hZ3 ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).mp hZF with h1 | h3
  · rw [h1, mul_one] at hcard
    apply index_ne_three_of_isPerfect hQ F'
    have h := F'.card_mul_index
    rw [hcard, hQ360] at h
    omega
  · rw [h3] at hcard
    exact false_of_isPerfect_of_card_forty hF'p (by omega)

end CFSG.RankThree.PartTwo.Sec15.Proof152Gen
