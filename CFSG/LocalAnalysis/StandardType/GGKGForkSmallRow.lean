module

public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkTransfer
public import CFSG.LocalAnalysis.StandardType.GGKGForkVacuous
public import CFSG.LocalAnalysis.StandardType.GGTorusTBGroupCard
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmall
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSmall
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanks

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggKGSm_two_dvd_card_of_perfect_nontrivial {R : Type} [Group R] [Finite R]
    [Nontrivial R] [Group.IsPerfect R] : 2 ∣ Nat.card R := by
  by_contra h2
  exact Group.IsPerfect.not_isSolvable R
    (CFSG.Milestones.odd_order_solvable (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)))

private theorem ggKGSm_two_dvd_card_adjointGroup {τ : CFSG.Blueprint.Chevalley.Tag} {K : Type}
    [Field K] [CharP K 2]
    (i : Fin τ.rank) :
    2 ∣ Nat.card (CFSG.Blueprint.Chevalley.adjointGroup τ K) := by
  have h2 : (CFSG.LieType.Chevalley.xElement (K := K) i 1) ^ 2 = 1 := by
    rw [pow_two, ← CFSG.LieType.Chevalley.xElement_add]
    have h1 : (1 : K) + 1 = 0 := by
      have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
      calc (1 : K) + 1 = 2 := by norm_num
        _ = 0 := htwo
    rw [h1, CFSG.LieType.Chevalley.xElement_zero]
  have hne : CFSG.LieType.Chevalley.xElement (K := K) i 1 ≠ 1 :=
    CFSG.LieType.Chevalley.xElement_ne_one (K := K) one_ne_zero (j := i)
  exact orderOf_eq_prime h2 hne ▸ orderOf_dvd_natCard _

theorem ggKGSm_two_dvd_card_chevG2 {K : Type} [Field K] [Finite K] [CharP K 2] :
    2 ∣ Nat.card (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K false)) := by
  have h : 2 ∣ Nat.card (TableBExc.RecipeGroup .G2 K) := by
    rw [Nat.card_congr (TableBExc.recipeEquiv .G2 K).toEquiv]
    exact ggKGSm_two_dvd_card_adjointGroup (τ := .G2) (K := K) ⟨0, by decide⟩
  exact h

theorem ggKGSm_two_dvd_card_sz {a : ℕ} {K : Type} [Field K] [Finite K]
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    2 ∣ Nat.card (LargeEvenCenterQuot (LargeEvenSzGroup a K)) := by
  have hZ : Subgroup.center (LargeEvenSzGroup a K) = ⊥ := by
    rw [largeEvenSzGroup_eq]
    exact CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hK
  let e : LargeEvenCenterQuot (LargeEvenSzGroup a K) ≃* LargeEvenSzGroup a K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  rw [Nat.card_congr e.toEquiv, largeEvenSzGroup_eq]
  letI : Nontrivial (CFSG.Blueprint.suzukiGroup a K) :=
    (CFSG.LieType.Ree.suzuki_simple ha hK).2.1
  letI : Group.IsPerfect (CFSG.Blueprint.suzukiGroup a K) :=
    (CFSG.LieType.Ree.suzuki_perfect ha hK).2
  letI : Finite (CFSG.Blueprint.suzukiGroup a K) :=
    (CFSG.LieType.Ree.suzuki_simple ha hK).1
  exact ggKGSm_two_dvd_card_of_perfect_nontrivial

theorem ggKGSm_two_dvd_card_triD4 {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    2 ∣ Nat.card
      (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)) := by
  obtain ⟨e⟩ := TableBExcSmallRest.nonempty_triD4_equiv hn K hK σ hσ
  rw [Nat.card_congr e.toEquiv]
  haveI : Finite (CFSG.Blueprint.Chevalley.ModGL CFSG.Blueprint.Chevalley.TwistTag.D4.tag K) :=
    CFSG.LieType.Chevalley.finite_modGL
  haveI : Finite (CFSG.LieType.Chevalley.graphFixedRootGroup CFSG.Blueprint.Chevalley.TwistTag.D4 K
      σ.toRingHom) := Subtype.finite
  obtain ⟨hperf, ⟨x, hx, y, hy, hxy⟩, -⟩ :=
    CFSG.LieType.Chevalley.finite_fixed_root_group_perfect
      (t := CFSG.Blueprint.Chevalley.TwistTag.D4) (p := 2) (f := n)
      Nat.prime_two hn K
      (by simpa only [CFSG.Blueprint.Chevalley.TwistTag.order] using hK) σ.toRingHom hσ
  letI : Group.IsPerfect (CFSG.LieType.Chevalley.graphFixedRootGroup
      CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom) := Subgroup.isPerfect_iff.mpr hperf
  letI : Nontrivial (CFSG.LieType.Chevalley.graphFixedRootGroup
      CFSG.Blueprint.Chevalley.TwistTag.D4 K σ.toRingHom) :=
    ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (by
      have hxy' : x = y := congrArg Subtype.val h
      subst hxy'
      rfl)⟩
  exact ggKGSm_two_dvd_card_of_perfect_nontrivial

theorem ggKGSm_two_dvd_card_twF4 {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K CFSG.LieType.Ree.ReeTag.F4.prime]
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    2 ∣ Nat.card (LargeEvenCenterQuot (LargeEvenTwF4H a K)) := by
  obtain ⟨e⟩ := TableBExcSmallRest.nonempty_twF4_equiv ha K hK
  rw [Nat.card_congr e.toEquiv]
  haveI : Finite (CFSG.Blueprint.Chevalley.ModGL CFSG.LieType.Ree.ReeTag.F4.tag K) :=
    CFSG.LieType.Chevalley.finite_modGL
  haveI : Finite (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) := Subtype.finite
  letI : Group.IsPerfect (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) :=
    ⟨CFSG.LieType.Ree.ReeTag.commutator_reeGamma_eq_top (t := CFSG.LieType.Ree.ReeTag.F4)
      ha (show Nat.card K = CFSG.LieType.Ree.ReeTag.F4.prime ^ (2 * a + 1) from hK)⟩
  letI : Nontrivial (CFSG.LieType.Ree.ReeTag.F4.reeGamma K a) :=
    CFSG.LieType.Ree.ReeTag.nontrivial_reeGamma (t := CFSG.LieType.Ree.ReeTag.F4)
  exact ggKGSm_two_dvd_card_of_perfect_nontrivial

private theorem ggKGSm_false_of_der {p : ℕ} {lab : LargeEvenLabel} (hp5 : 5 ≤ p)
    (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der)
    (hs : LargeEvenSplit p lab) : False := by
  rcases ht with ht | ht | ht
  · have hlab' := hlab
    dsimp only [LargeEvenInLambda2] at hlab'
    rw [ht] at hlab'
    obtain ⟨-, hn1⟩ := hlab'.2
    have hs' := hs
    dsimp only [LargeEvenSplit, LargeEvenUntwisted] at hs'
    rw [ht] at hs'
    rcases hs' with ⟨-, h⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · rw [hn1] at h
      have hle := Nat.le_of_dvd (by norm_num : 0 < 1) (by simpa using h)
      omega
    · exact h trivial
    · rcases h with h | h <;> cases h
    · omega
  · have hlab' := hlab
    dsimp only [LargeEvenInLambda2] at hlab'
    rw [ht] at hlab'
    obtain ⟨-, hn1⟩ := hlab'.2
    have hs' := hs
    dsimp only [LargeEvenSplit, LargeEvenUntwisted] at hs'
    rw [ht] at hs'
    rcases hs' with ⟨-, h⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · rw [hn1] at h
      have hle := Nat.le_of_dvd (by norm_num : 0 < 1) (by simpa using h)
      omega
    · exact h trivial
    · rcases h with h | h <;> cases h
    · omega
  · have hlab' := hlab
    dsimp only [LargeEvenInLambda2] at hlab'
    rw [ht] at hlab'
    obtain ⟨-, hn1⟩ := hlab'.2
    have hs' := hs
    dsimp only [LargeEvenSplit, LargeEvenUntwisted] at hs'
    rw [ht] at hs'
    rcases hs' with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · rw [hn1] at h
      have hle := Nat.le_of_dvd (by norm_num : 0 < 3) (by simpa using h)
      omega
    · rcases h with h | h <;> cases h
    · omega

theorem ggKGOneOn_small :
    GGKGOneOn (GGKGRowLabel .small) := by
  intro p lab hp hlab hl hs
  obtain ⟨hp5, hsplit⟩ := hl
  obtain ⟨t, l, n⟩ := lab
  rcases hs with ht | ht | ht | ht | ht | ht | ht
  · subst ht
    intro Q hQ
    obtain ⟨K, i1, i2, hK, hQ', hpc⟩ :=
      (TableBExc.largeEvenLabelAll_card_lt_G2 hp hlab rfl hsplit) Q hQ
    haveI : CharP K 2 := charP_two_of_card hK
    refine ⟨K, i1, i2, hK, hQ', 0, TypeA.ggTorusLift_zero
      (ggKGSm_two_dvd_card_chevG2 (K := K)), ?_⟩
    intro L' _ _ ψ A hA
    exact (ggTorusTBGroup_false_of_card_lt hpc hA).elim
  · subst ht
    intro Q hQ
    obtain ⟨K, i1, i2, hK, hQ', hpc⟩ :=
      (TableBExcSmallRest.largeEvenLabelAll_card_lt_triD4
        (fun _ => TableBExcSmallRanks.ggTriD4ThreeRankInput_holds) hp hlab rfl hsplit) Q hQ
    haveI : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
    set σ := iterateFrobeniusEquiv K 2 n with hσdef
    have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
      rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
    refine ⟨K, i1, i2, hK, hQ', 0, TypeA.ggTorusLift_zero
      (ggKGSm_two_dvd_card_triD4 hlab.1 hK σ hσ), ?_⟩
    intro L' _ _ ψ A hA
    exact (ggTorusTBGroup_false_of_card_lt hpc hA).elim
  · subst ht
    intro Q hQ
    obtain ⟨K, i1, i2, hK, hQ', hpc⟩ :=
      (TableBExc.largeEvenLabelAll_card_lt_twB2 hp hlab rfl hsplit) Q hQ
    have hlab' := hlab
    dsimp only [LargeEvenInLambda2] at hlab'
    obtain ⟨-, hodd, hn3⟩ := hlab'.2
    have ha : 1 ≤ (n - 1) / 2 := by omega
    refine ⟨K, i1, i2, hK, hQ', 0, TypeA.ggTorusLift_zero
      (ggKGSm_two_dvd_card_sz ha hK), ?_⟩
    intro L' _ _ ψ A hA
    exact (ggTorusTBGroup_false_of_card_lt hpc hA).elim
  · subst ht
    intro Q hQ
    obtain ⟨K, i1, i2, hK, hQ', hpc⟩ :=
      (TableBExcSmallRanks.largeEvenLabelAll_card_lt_twF4_of_ne_three
        (by omega) hp hlab rfl hsplit) Q hQ
    have hlab' := hlab
    dsimp only [LargeEvenInLambda2] at hlab'
    obtain ⟨-, hodd, hn3⟩ := hlab'.2
    have ha : 1 ≤ (n - 1) / 2 := by omega
    haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_two_of_card hK
    refine ⟨K, i1, i2, hK, hQ', 0, TypeA.ggTorusLift_zero
      (ggKGSm_two_dvd_card_twF4 ha hK), ?_⟩
    intro L' _ _ ψ A hA
    exact (ggTorusTBGroup_false_of_card_lt hpc hA).elim
  · subst ht
    exact (ggKGSm_false_of_der hp5 hlab (Or.inl rfl) hsplit).elim
  · subst ht
    exact (ggKGSm_false_of_der hp5 hlab (Or.inr (Or.inl rfl)) hsplit).elim
  · subst ht
    exact (ggKGSm_false_of_der hp5 hlab (Or.inr (Or.inr rfl)) hsplit).elim

end CFSG.StandardType

end
