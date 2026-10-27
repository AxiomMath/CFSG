module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieD4
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieTypeCard
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieArithG2

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Group

variable {G : Type*} [Group G]

theorem eq_one_of_isPGroup_two_of_pow_three {P : Subgroup G} (hP : IsPGroup 2 P) {y : G}
    (hy : y ∈ P) (hy3 : y ^ 3 = 1) : y = 1 := by
  obtain ⟨j, hj⟩ := hP ⟨y, hy⟩
  have hj' : y ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hd : orderOf y ∣ Nat.gcd 3 (2 ^ j) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hy3) (orderOf_dvd_of_pow_eq_one hj')
  have hg : Nat.gcd 3 (2 ^ j) = 1 := Nat.Coprime.pow_right j (by norm_num : Nat.Coprime 3 2)
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

theorem quot_pCore_facts {J : Type*} [Group J] [Group.IsPerfect J] {k : J} (hk1 : k ≠ 1)
    (hk3 : k ^ 3 = 1) :
    Group.IsPerfect (J ⧸ CFSG.pCore 2 J) ∧ Nontrivial (J ⧸ CFSG.pCore 2 J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (CFSG.pCore 2 J).Normal := CFSG.pCore_normal
  refine ⟨Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _), ?_⟩
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  have hk : k ∈ CFSG.pCore 2 J := by
    rw [← QuotientGroup.eq_one_iff]
    exact Subsingleton.elim _ _
  exact hk1 (eq_one_of_isPGroup_two_of_pow_three CFSG.pCore_isPGroup hk hk3)

end Group

section G2


theorem isSimpleGroup_adjointGroup_of_perfect' (τ : Tag) (k : Type) [Field k] [Finite k]
    (hperf : Group.IsPerfect (adjointGroup τ k)) : IsSimpleGroup (adjointGroup τ k) := by
  have hnc := (opposite_simple_root_noncommutativity τ k).2.2.1
  have : Nontrivial (adjointGroup τ k) := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨⟨a * b, b * a, hab⟩⟩
  have hZ : Subgroup.center (adjointGroup τ k) = ⊥ := center_adjointGroup_eq_bot
  refine IsSimpleGroup.mk fun M hM => ?_
  by_cases hbot : M = ⊥
  · exact Or.inl hbot
  · right
    have hnot : ¬ M ≤ Subgroup.center (adjointGroup τ k) := by
      rw [hZ]
      exact fun h => hbot (le_bot_iff.1 h)
    have hsolv := (noncentral_normal_solvable_quotient τ k M hnot).2.1
    by_contra htop
    have : Nontrivial (adjointGroup τ k ⧸ M) := by
      rw [← not_subsingleton_iff_nontrivial, QuotientGroup.subsingleton_iff]
      exact htop
    exact Group.IsPerfect.not_isSolvable _ hsolv

theorem g2Excl429 : G2Excl429 := by
  intro k _ _ m hk hm G _ _ C J ⟨eC⟩ hJC hJperf hsub htype
  haveI := hJperf
  obtain ⟨E, hEJ, -, hE3, hE9, -⟩ := exists_e9_of_type429 htype
  obtain ⟨k₀, hk₀E, hk₀1, hk₀3⟩ := exists_ne_one_pow_three hE3 hE9
  have hk₀J : k₀ ∈ J := hEJ hk₀E
  have hJnt : J ≠ ⊥ := fun hb => hk₀1 ((Subgroup.mem_bot).mp (hb ▸ hk₀J))
  have hk₀1' : (⟨k₀, hk₀J⟩ : J) ≠ 1 := fun h => hk₀1 (congrArg Subtype.val h)
  have hk₀3' : (⟨k₀, hk₀J⟩ : J) ^ 3 = 1 := Subtype.ext (by simpa using hk₀3)
  obtain ⟨hQperf, hQnt⟩ := quot_pCore_facts hk₀1' hk₀3'
  haveI := hQnt
  have hcardC : Nat.card C = CFSG.Open.ordG2 (2 ^ m) := by
    rw [Nat.card_congr eC.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hk]
  have hQJ : Nat.card (J ⧸ CFSG.pCore 2 J) ∣ Nat.card J := by
    haveI : (CFSG.pCore 2 J).Normal := CFSG.pCore_normal
    exact Subgroup.card_quotient_dvd_card _
  have hJCd : Nat.card J ∣ Nat.card C := Subgroup.card_dvd_of_le hJC
  rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
  ·
    have hdvd : Nat.card (J ⧸ CFSG.pCore 2 J) ∣ 12096 := by
      have := hQJ.trans hJCd
      rw [hcardC] at this
      simpa [CFSG.Open.ordG2] using this
    have hle : Nat.card (J ⧸ CFSG.pCore 2 J) ≤ 12096 := Nat.le_of_dvd (by norm_num) hdvd
    rcases card_of_isType429 htype with ⟨p, e, hp, hp3, he, ⟨hq, hc⟩ | ⟨hq, hc, hsol⟩⟩ |
      hc | hc | hc | hc
    · exact g2two_L3 hdvd (Nat.le_trans hp.two_le (Nat.le_self_pow (by omega) p)) hq hc
    · have h2 := g2two_U3 hdvd (Nat.le_trans hp.two_le (Nat.le_self_pow (by omega) p)) hq hc
      exact Group.IsPerfect.not_isSolvable _ (hsol h2)
    · rw [hc] at hdvd
      norm_num at hdvd
    · rw [hc] at hle
      norm_num at hle
    · rw [hc] at hle
      norm_num at hle
    · rw [hc] at hle
      norm_num at hle
  ·
    have hk3 : 3 ≤ Nat.card k := by
      rw [hk]
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    haveI hCs : IsSimpleGroup (adjointGroup .G2 k) := isSimpleGroup_adjointGroup_of_perfect' .G2 k
      (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card k hk3)
    have hCs' : IsSimpleGroup C := eC.isSimpleGroup
    have hJC' : J = C := eq_of_subnormal_of_le_simple hJC le_rfl hsub hCs' hJnt
    haveI hJs : IsSimpleGroup J := by
      rw [hJC']
      exact hCs'
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hN : CFSG.pCore 2 J = ⊥ := by
      haveI : (CFSG.pCore 2 J).Normal := CFSG.pCore_normal
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 J) with h | h
      · exact h
      · exfalso
        have hkN : (⟨k₀, hk₀J⟩ : J) ∈ CFSG.pCore 2 J := h ▸ Subgroup.mem_top _
        exact hk₀1' (eq_one_of_isPGroup_two_of_pow_three CFSG.pCore_isPGroup hkN hk₀3')
    have hcardQ : Nat.card (J ⧸ CFSG.pCore 2 J) = CFSG.Open.ordG2 (2 ^ m) := by
      have e1 : (J ⧸ CFSG.pCore 2 J) ≃* J :=
        (QuotientGroup.quotientMulEquivOfEq hN).trans QuotientGroup.quotientBot
      rw [Nat.card_congr e1.toEquiv, ← hcardC]
      exact congrArg (fun H : Subgroup G => Nat.card H) hJC'
    have hbig : 604800 < CFSG.Open.ordG2 (2 ^ m) := by
      have h4 : 4 ≤ 2 ^ m := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
      unfold CFSG.Open.ordG2
      have h6 : 4 ^ 6 ≤ (2 ^ m) ^ 6 := Nat.pow_le_pow_left h4 6
      have h2 : 4 ^ 2 ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left h4 2
      have hA : 4095 ≤ (2 ^ m) ^ 6 - 1 := by omega
      have hB : 15 ≤ (2 ^ m) ^ 2 - 1 := by omega
      calc 604800 < 4 ^ 6 * 4095 * 15 := by norm_num
        _ ≤ (2 ^ m) ^ 6 * ((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul h6 hA) hB
    rcases card_of_isType429 htype with ⟨p, e, hp, hp3, he, ⟨hq, hc⟩ | ⟨hq, hc, -⟩⟩ |
      hc | hc | hc | hc
    · exact g2_mul_three_ne_L3 hm2 hp hp3 he (hcardQ ▸ hc)
    · exact g2_mul_three_ne_U3 hm2 hp hp3 he (hcardQ ▸ hc)
    all_goals omega

end G2

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
