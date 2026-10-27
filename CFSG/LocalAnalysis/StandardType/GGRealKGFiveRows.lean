module

public import CFSG.LocalAnalysis.StandardType.GGRealKG
public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGRealKGOmegaRow
import CFSG.LocalAnalysis.StandardType.GGKGForkOneDone
import CFSG.LocalAnalysis.StandardType.GGRealKGLinNsRoot
import CFSG.LocalAnalysis.StandardType.GGRealKGSpRoot
import CFSG.LocalAnalysis.StandardType.GGRealKGUSplitRoot
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineTwF4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace RealKGFive

private theorem two_dvd_card_of_perfect {R : Type} [Group R] [Finite R]
    [Nontrivial R] [Group.IsPerfect R] : 2 ∣ Nat.card R := by
  by_contra h2
  exact Group.IsPerfect.not_isSolvable R
    (CFSG.Milestones.odd_order_solvable (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)))

private theorem two_dvd_card_adjointGroup {τ : CFSG.Blueprint.Chevalley.Tag} {K : Type}
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

private theorem two_dvd_card_chevG2 {K : Type} [Field K] [Finite K] [CharP K 2] :
    2 ∣ Nat.card (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K false)) := by
  have h : 2 ∣ Nat.card (TableBExc.RecipeGroup .G2 K) := by
    rw [Nat.card_congr (TableBExc.recipeEquiv .G2 K).toEquiv]
    exact two_dvd_card_adjointGroup (τ := .G2) (K := K) ⟨0, by decide⟩
  exact h

private theorem two_dvd_card_sz {a : ℕ} {K : Type} [Field K] [Finite K]
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
  exact two_dvd_card_of_perfect

private theorem two_dvd_card_triD4 {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
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
  exact two_dvd_card_of_perfect

private theorem two_dvd_card_twF4 {a : ℕ} {K : Type} [Field K] [Finite K]
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
  exact two_dvd_card_of_perfect

end RealKGFive

open RealKGFive in
theorem ggRealRootSL2On_small :
    GGRealRootSL2On fun p lab => 5 ≤ p ∧ GGKGRowLabel .small p lab := by
  intro p lab hp hlab hl hs
  obtain ⟨hp5, hs⟩ := hs
  have hp2 : p ≠ 2 := hl.1
  have hn2 : 2 ≤ lab.n := hl.2.1
  have hdvd := ggKG_dvd_of_lattice hp ⟨hp5, hl.2.1, hl.2.2⟩
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hn2 hdvd
  rcases hs with ht | ht | ht | ht | ht | ht | ht <;> dsimp only at ht <;> subst ht
  · intro Q hQ
    obtain ⟨K, i1, i2, hK, hQ', hpc⟩ :=
      (NbrInnerNine.largeEvenLabelAll_card_lt_G2_all (lab := ⟨.G2, l, n⟩) hp hp2 rfl) Q hQ
    haveI : CharP K 2 := charP_two_of_card hK
    refine ⟨K, i1, i2, hK, hQ', 0, TypeA.ggTorusLift_zero (two_dvd_card_chevG2 (K := K)), ?_⟩
    intro L' _ _ ψ A hA
    exact (ggTorusTBGroup_false_of_card_lt hpc hA).elim
  · have hpq : p ∣ (2 ^ n) ^ 2 - 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact hl.2.2
    intro Q hQ
    obtain ⟨K, i1, i2, hK, hQ', hpc⟩ :=
      (NbrInnerNine.largeEvenLabelAll_card_lt_triD4_of hp hlab rfl (Or.inr hpq)) Q hQ
    haveI : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
    set σ := iterateFrobeniusEquiv K 2 n with hσdef
    have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
      rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
    refine ⟨K, i1, i2, hK, hQ', 0, TypeA.ggTorusLift_zero (two_dvd_card_triD4 hlab.1 hK σ hσ), ?_⟩
    intro L' _ _ ψ A hA
    exact (ggTorusTBGroup_false_of_card_lt hpc hA).elim
  · intro Q hQ
    obtain ⟨K, i1, i2, hK, hQ', hpc⟩ :=
      (NbrInnerNine.largeEvenLabelAll_card_lt_twB2_all hp hp2 hlab rfl) Q hQ
    have hn3 : 3 ≤ n := hlab.2.2.2
    have ha : 1 ≤ (n - 1) / 2 := by omega
    refine ⟨K, i1, i2, hK, hQ', 0, TypeA.ggTorusLift_zero (two_dvd_card_sz ha hK), ?_⟩
    intro L' _ _ ψ A hA
    exact (ggTorusTBGroup_false_of_card_lt hpc hA).elim
  · have hcard : LargeEvenLabelAll ⟨.twF4, l, n⟩ fun R _ I _ => ∀ X : Subgroup (MulAut R),
        (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
      rcases hdvd with h | h
      · exact NbrInnerNine.largeEvenLabelAll_card_lt_twF4_sub hp hp2 hlab rfl h
      · exact TableBExcSmallRanks.largeEvenLabelAll_card_lt_twF4_of_ne_three (by omega) hp hlab
          rfl (Or.inr (Or.inl ⟨id, by simp, h⟩))
    intro Q hQ
    obtain ⟨K, i1, i2, hK, hQ', hpc⟩ := hcard Q hQ
    have hn3 : 3 ≤ n := hlab.2.2.2
    have ha : 1 ≤ (n - 1) / 2 := by omega
    haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_two_of_card hK
    refine ⟨K, i1, i2, hK, hQ', 0, TypeA.ggTorusLift_zero (two_dvd_card_twF4 ha hK), ?_⟩
    intro L' _ _ ψ A hA
    exact (ggTorusTBGroup_false_of_card_lt hpc hA).elim
  all_goals
    have h1 : n = 1 := hlab.2.2
    omega

end CFSG.StandardType

end
