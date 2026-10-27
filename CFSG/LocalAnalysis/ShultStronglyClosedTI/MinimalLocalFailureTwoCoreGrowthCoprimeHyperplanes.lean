module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthCoprimeFixedPoints
public import CFSG.GroupTheory.HyperplaneGeneration

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowthCoprime

universe u v

theorem noncyclic_elementary_odd_actor_card
    {A : Type v} [Group A] [Finite A] {p : ℕ} (hp : p.Prime) (hpOdd : Odd p)
    [CFSG.IsElementaryAbelian p A] (hAnc : ¬ IsCyclic A) :
    p ^ 2 ≤ Nat.card A ∧ Odd (Nat.card A) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (CFSG.IsElementaryAbelian.isPGroup p A).exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra hsmall
    have hcases : n = 0 ∨ n = 1 := by omega
    rcases hcases with rfl | rfl
    · exact hAnc (isCyclic_of_card_dvd_prime (p := p) (by simp [hn]))
    · exact hAnc (isCyclic_of_card_dvd_prime (p := p) (by simp [hn]))
  rw [hn]
  exact ⟨(Nat.pow_le_pow_iff_right hp.one_lt).mpr hn2, hpOdd.pow⟩

theorem exists_nontrivial_hyperplane_fixed_two_group
    {W : Type u} [Group W] [Finite W] [Nontrivial W]
    {A : Type v} [Group A] [Finite A] {p : ℕ} (hp : p.Prime) (hpOdd : Odd p)
    [CFSG.IsElementaryAbelian p A] [MulDistribMulAction A W]
    (hAnc : ¬ IsCyclic A) (hW : IsPGroup 2 W) :
    ∃ B : Subgroup A, B.index = p ∧ CFSG.fixedPointSubgroup B W ≠ ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hAcard, hAodd⟩ := noncyclic_elementary_odd_actor_card hp hpOdd hAnc
  have hAone : 1 < Nat.card A := lt_of_lt_of_le (by nlinarith [hp.one_lt]) hAcard
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp hAone
  have hcop := (two_group_solvable_coprime hW hAodd).2
  have hnot : ¬ p ∣ Nat.card W := by
    intro hdiv
    have hpA : p ∣ Nat.card A := by
      obtain ⟨n, hn⟩ := (CFSG.IsElementaryAbelian.isPGroup p A).exists_card_eq
      have hnpos : 0 < n := by
        by_contra hnzero
        have hn0 : n = 0 := by omega
        simp [hn0] at hn
        omega
      rw [hn]
      exact dvd_pow_self p (Nat.ne_of_gt hnpos)
    have heq : p = 1 := Nat.eq_one_of_dvd_coprimes hcop hpA hdiv
    exact hp.ne_one heq
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation
    (A := A) (H := W) (p := p) hnot
  by_contra hnone
  have hall : ∀ B : Subgroup A, B.index = p → CFSG.fixedPointSubgroup B W = ⊥ := by
    intro B hB
    by_contra hBne
    exact hnone ⟨B, hB, hBne⟩
  have hbot : (⊤ : Subgroup W) = ⊥ := by
    apply le_antisymm _ bot_le
    rw [← hgen]
    exact iSup₂_le fun B hB => (hall B hB).le
  have hone : Nat.card W = 1 := by
    have htopcard : Nat.card (⊤ : Subgroup W) = Nat.card W :=
      Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [← htopcard, hbot]
    simp
  exact (ne_of_gt (Finite.one_lt_card (α := W))) hone

theorem exists_nonidentity_actor_with_nonidentity_fixed_two_group
    {W : Type u} [Group W] [Finite W] [Nontrivial W]
    {A : Type v} [Group A] [Finite A] {p : ℕ} (hp : p.Prime) (hpOdd : Odd p)
    [CFSG.IsElementaryAbelian p A] [MulDistribMulAction A W]
    (hAnc : ¬ IsCyclic A) (hW : IsPGroup 2 W) :
    ∃ a : A, a ≠ 1 ∧ ∃ x : W, x ≠ 1 ∧ a • x = x := by
  obtain ⟨B, hB, hF⟩ := exists_nontrivial_hyperplane_fixed_two_group hp hpOdd hAnc hW
  have hAcard := (noncyclic_elementary_odd_actor_card hp hpOdd hAnc).1
  have hBcard : 1 < Nat.card B := by
    have hcard := B.card_mul_index
    rw [hB] at hcard
    by_contra hsmall
    have hle : Nat.card B ≤ 1 := by omega
    have hcardle : Nat.card A ≤ p := by nlinarith
    nlinarith [hp.one_lt]
  let : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp hBcard
  let : Nontrivial (CFSG.fixedPointSubgroup B W) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hF
  obtain ⟨b, hb⟩ := exists_ne (1 : B)
  obtain ⟨x, hx⟩ := exists_ne (1 : CFSG.fixedPointSubgroup B W)
  refine ⟨b, (fun h => hb (Subtype.ext h)), x, (fun h => hx (Subtype.ext h)), ?_⟩
  exact x.property b

theorem exists_nonidentity_actor_with_nonidentity_fixed_two_quotient
    {M : Type u} [Group M] [Finite M]
    {A : Type v} [Group A] [Finite A] {p : ℕ} (hp : p.Prime) (hpOdd : Odd p)
    [CFSG.IsElementaryAbelian p A] [MulDistribMulAction A M]
    (hAnc : ¬ IsCyclic A) (hM : IsPGroup 2 M)
    (Q : Subgroup M) [Q.Normal] (hQinv : CFSG.IsInvariant A M Q)
    (hQproper : Q ≠ ⊤) :
    letI : MulDistribMulAction A (M ⧸ Q) :=
      CFSG.quotientMulDistribMulAction (A := A) (G := M) Q hQinv
    ∃ a : A, a ≠ 1 ∧ ∃ x : M ⧸ Q, x ≠ 1 ∧ a • x = x := by
  let : MulDistribMulAction A (M ⧸ Q) :=
    CFSG.quotientMulDistribMulAction (A := A) (G := M) Q hQinv
  let : Nontrivial (M ⧸ Q) := QuotientGroup.nontrivial_iff.mpr hQproper
  exact exists_nonidentity_actor_with_nonidentity_fixed_two_group hp hpOdd hAnc
    (hM.to_quotient Q)

end CFSG.ShultStronglyClosedTI.TwoCoreGrowthCoprime
