module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientBinary
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientKernelCore
public import CFSG.RankThree.Coprime.InvolutionFixedRankBound
public import CFSG.RankThree.GroupTheory.SteinbergBMClassTwoExtraspecialAction
public import CFSG.LinearAlgebra.OddSolvableUnitary.CommutatorForm
public import CFSG.GroupTheory.ExtraspecialCentralizerInnerAut

public section

namespace CFSG.RankThree.PartOne.Quotient36

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY
open scoped IsMulCommutative

section Extraspecial

theorem exists_card_eq_pow_extraspecial {S : Type*} [Group S] [Finite S]
    (hS : IsExtraspecialPGroup 2 S) : ∃ n : ℕ, 1 ≤ n ∧ Nat.card S = 2 ^ (1 + 2 * n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Module (ZMod 2) (Additive (Abelianization S)) :=
    CFSG.GroupTheory.extraspecialQuotientModule hS
  obtain ⟨ε⟩ := CFSG.OddSolvableUnitary.nonempty_center_mulEquiv (D := S) (r := 2) hS.2.2.2
  obtain ⟨B, hBa, hBn, -⟩ := CFSG.OddSolvableUnitary.exists_commForm hS.2.1.symm ε
  have : Finite (Additive (Abelianization S)) :=
    Finite.of_surjective (fun x : S => Additive.ofMul (Abelianization.of x))
      fun v => QuotientGroup.mk_surjective (Additive.toMul v)
  have : Module.Finite (ZMod 2) (Additive (Abelianization S)) := Module.Finite.of_finite
  obtain ⟨a, ha⟩ := LinearMap.BilinForm.IsAlt.even_finrank (K := ZMod 2) hBa hBn
  have hab : Nat.card (Abelianization S) = 2 ^ (2 * a) := by
    have : Nat.card (Additive (Abelianization S)) = 2 ^ (a + a) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, ha]
    rw [← two_mul] at this
    exact this
  have hcard : Nat.card S = 2 ^ (1 + 2 * a) := by
    rw [CFSG.OddSolvableUnitary.card_eq_card_abelianization_mul hS.2.1.symm hS.2.2.2, hab,
      pow_add, pow_one, mul_comm]
  refine ⟨a, ?_, hcard⟩
  by_contra h0
  have ha0 : a = 0 := by omega
  rw [ha0, mul_zero, add_zero, pow_one] at hcard
  have htop : Subgroup.center S = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hS.2.2.2, hcard])
  have hc : commutator S = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro g _
    exact Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top x) g
  have h1 : (⊥ : Subgroup S) = ⊤ := by rw [← hc, hS.2.1, htop]
  have h2 : Nat.card S = 1 := by
    rw [← Subgroup.card_top, ← h1, Subgroup.card_bot]
  omega

theorem exists_center_eq_zpowers {S : Type*} [Group S] (hS : IsExtraspecialPGroup 2 S) :
    ∃ z : S, Subgroup.center S = Subgroup.zpowers z := by
  have hcard : Nat.card (Subgroup.center S) = 2 := hS.2.2.2
  have hne : Subgroup.center S ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  refine ⟨z, ?_⟩
  symm
  have hle : Subgroup.zpowers z ≤ Subgroup.center S := Subgroup.zpowers_le.mpr hz
  have : Finite (Subgroup.center S) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hcard, Nat.card_zpowers]
  have h2 : orderOf z ∣ 2 := by
    have h3 := orderOf_dvd_natCard (⟨z, hz⟩ : Subgroup.center S)
    rw [hcard] at h3
    rw [← Subgroup.orderOf_coe (⟨z, hz⟩ : Subgroup.center S)] at h3
    exact h3
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hz1'
  · exact h.ge

theorem extraspecial_action_n_le_three {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {X : Type*} [Group X]
    [Finite X] (hXq : IsPGroup q X) (hXexp : ∀ x : X, x ^ q = 1)
    (hXcl : commutator X ≤ Subgroup.center X) {S : Type*} [Group S] [MulDistribMulAction S X]
    [FaithfulSMul S X] {n : ℕ} (hS : IsExtraspecialPGroup 2 S)
    (hcard : Nat.card S = 2 ^ (1 + 2 * n))
    (hrank : ∀ s : S, s ≠ 1 → CFSG.pRank q (fixedPointSubgroup (Subgroup.zpowers s) X) ≤ 3) :
    n ≤ 3 := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨z, hz⟩ := exists_center_eq_zpowers hS
  have hρ : Function.Injective (MulDistribMulAction.toMulAut S X) := fun a b h =>
    eq_of_smul_eq_smul (fun x => congrArg (fun f : MulAut X => f x) h)
  refine (CFSG.RankThree.GroupTheory.SteinbergBM.class_two_extraspecial_action_bound hq2 hXq
    hXexp hXcl hS hcard hz (MulDistribMulAction.toMulAut S X) hρ ?_).1
  intro s hs
  have : CFSG.RankThree.PartTwo.fixedSubgroupOf (MulDistribMulAction.toMulAut S X s) =
      fixedPointSubgroup (Subgroup.zpowers s) X := by
    ext x
    rw [CFSG.RankThree.PartTwo.mem_fixedSubgroupOf, mem_fixedPointSubgroup_zpowers_iff]
    rfl
  rw [this]
  exact hrank s hs

end Extraspecial

theorem lowerCentralSeries_two_eq_bot {X : Type*} [Group X]
    (hXcl : commutator X ≤ Subgroup.center X) : (⊤ : Subgroup X).lowerCentralSeries 2 = ⊥ := by
  have h2 : (⊤ : Subgroup X).lowerCentralSeries 2 = ⁅commutator X, (⊤ : Subgroup X)⁆ := by
    simp [Subgroup.lowerCentralSeries, commutator_def]
  rw [h2, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro g _
  exact Subgroup.mem_center_iff.mp (hXcl hx) g

theorem small_faithful_quotient_shape
    (hrec : SmallExtraspecialOddActionRecognition)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp3 : 3 < p) (hq2 : q ≠ 2)
    {X : Type} [Group X] [Finite X] (hXq : IsPGroup q X) (hXexp : ∀ x : X, x ^ q = 1)
    (hXcl : commutator X ≤ Subgroup.center X)
    {S : Type} [Group S] [Finite S] [MulDistribMulAction S X] [FaithfulSMul S X]
    (hS2 : IsPGroup 2 S)
    (hrank : ∀ s : S, s ≠ 1 → CFSG.pRank q (fixedPointSubgroup (Subgroup.zpowers s) X) ≤ 3)
    {A : Type} [Group A] [Finite A] [IsElementaryAbelian p A] (hA : Nat.card A = p ^ 2)
    [MulDistribMulAction A S]
    (hshape : IsElementaryAbelian 2 S ∨ IsExtraspecialPGroup 2 S)
    (hirr : NontrivIrredFrattini A S) :
    ((IsElementaryAbelian 2 S ∧ ((p = 7 ∧ Nat.card S = 8) ∨ (p = 5 ∧ Nat.card S = 16))) ∨
      (IsExtraspecialPGroup 2 S ∧ p = 5 ∧ Nonempty (S ≃* QD32))) ∧
    Nat.card (MulDistribMulAction.toMulAut A S).range = p ∧
    Nat.card (MulDistribMulAction.toMulAut A S).ker = p ∧
    (∀ a : A, (∀ s : S, a • s = s) ↔
      (letI := frattiniQuotientAction A S; ∀ v : S ⧸ frattini S, a • v = v)) := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨d, hVd, h4, h6, hcyc, hcardr, hker, hkercard⟩ := binary_action_data hp hp3 hS2 hirr
  have hcardker := hkercard hA
  rcases hshape with hel | hext
  · have : Fact (IsPGroup 2 S) := ⟨hS2⟩
    have hΦ : frattini S = ⊥ := frattini_eq_bot_of_isElementaryAbelian (R := S) (p := 2)
    have hVS : Nat.card (S ⧸ frattini S) = Nat.card S := by
      rw [hΦ]
      exact Subgroup.index_bot
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hS2
    have hdm : d = m := Nat.pow_right_injective (le_refl 2) (hVd.symm.trans (hVS.trans hm))
    have hbound : m ≤ 3 + 1 := by
      let _ : CommGroup S := IsMulCommutative.instCommGroup
      let _ : Module (ZMod 2) (Additive S) := IsElementaryAbelian.isVectorSpace 2
      exact (CFSG.RankThree.Coprime.class_two_involution_fixed_rank_bound (p := q)
        (hq.odd_of_ne_two hq2) hXq (Monoid.exponent_dvd_of_forall_pow_eq_one hXexp)
        (lowerCentralSeries_two_eq_bot hXcl) m 3 hm hrank).1
    refine ⟨Or.inl ⟨hel, ?_⟩, hcardr, hcardker, hker⟩
    rcases h4 (by omega) with ⟨h7, hd3⟩ | ⟨h5, hd4⟩
    · left
      exact ⟨h7, by rw [hm, ← hdm, hd3]; norm_num⟩
    · right
      exact ⟨h5, by rw [hm, ← hdm, hd4]; norm_num⟩
  · obtain ⟨n, hn1, hcard⟩ := exists_card_eq_pow_extraspecial hext
    have hn3 := extraspecial_action_n_le_three hq hq2 hXq hXexp hXcl hext hcard hrank
    obtain ⟨h5, -, hQD, -, -, -, -⟩ := hrec p n A S hp hp3 hext hn1 hn3 hcard hirr
    exact ⟨Or.inr ⟨hext, h5, hQD⟩, hcardr, hcardker, hker⟩

end CFSG.RankThree.PartOne.Quotient36
