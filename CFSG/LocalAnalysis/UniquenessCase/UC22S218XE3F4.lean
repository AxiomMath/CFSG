module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218F4
import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcReeTorus
import CFSG.RankThree.PartOne.SEITZ7.SzPair
import CFSG.CGT.PushingUpLit.CGT6K1.InnerEven
import CFSG.RankThree.PartOne.K128.F4Syl
import CFSG.Mathlib.Arithmetic.TwoPowModThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

open CFSG.LieType.Ree.ReeTag (F4)

open CFSG.LieType.Ree.LargeReeCover (torusPair)

open CFSG.LieType.Ree.LargeReeInvolution
open CFSG.RankThree.PartOne.SEITZ7


theorem uc22s218_f4_exists_levi_torus {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    {a p : ℕ} (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hpq : p ∣ 2 ^ (2 * a + 1) + 1 ∨ p ∣ (2 ^ (2 * a + 1)) ^ 2 + 1)
    {s r : ℕ} (hs : Odd s) (hsn : s ∣ 2 * a + 1) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) :
    ∃ x ∈ (F4.reeFixedTorus K a).subgroupOf (F4.reeGamma K a), orderOf x = r ∧
      ∃ S : Subgroup ↥(F4.reeGamma K a), S ≤ centralizer {x} ∧
        (IsL2 ↥S (2 * a + 1) ∨ IsSz ↥S (2 * a + 1)) ∧ p ∣ Nat.card S := by
  have : Finite (CFSG.Blueprint.Chevalley.ModGL F4.tag K) :=
    CFSG.LieType.Chevalley.finite_modGL
  have : CharP K 2 := ‹CharP K F4.prime›
  have : Fact r.Prime := ⟨hr⟩
  have hrq : r ∣ 2 ^ (2 * a + 1) - 1 :=
    hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
  have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd hs.pos hrs
  have hr3 : r ≠ 3 := fun h => uc22s218_f4_not_three_dvd hs (h ▸ hrs)
  have hr5 : 5 ≤ r := hr.five_le_of_ne_two_of_ne_three hr2 hr3
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r
    (by rw [Nat.card_units, hK]; exact hrq)
  rcases hpq with hpq | hpq
  · let x : ↥(F4.reeGamma K a) :=
      ⟨torusPair a (w, w ^ 2), CFSG.LieType.Ree.LargeReeCover.torusPair_mem_reeGamma a hK _⟩
    have hR : rankOneGroupOne K a ≤ F4.reeGamma K a := rankOneGroupOne_le_reeGamma hK
    let S := (rankOneGroupOne K a).subgroupOf (F4.reeGamma K a)
    refine ⟨x, Subgroup.mem_subgroupOf.2 (rankOne_torusPair_mem_reeFixedTorus hK _ _), ?_,
      S, ?_, Or.inl ?_, ?_⟩
    · change orderOf x = r
      rw [Subgroup.orderOf_mk, orderOf_injective (torusPair a)
        (CFSG.RankThree.LargeReeOrder.torusPair_injective hK), Prod.orderOf,
        Nat.lcm_eq_left (orderOf_pow_dvd (x := w) 2), hw]
    · intro y hy
      rw [mem_centralizer_iff]
      rintro _ rfl
      apply Subtype.ext
      exact ((CFSG.ComponentClassification.RankTwoExceptional.ReeSec8.cent_torusPair
        hK hr hr5 hrq (IsPrimitiveRoot.iff_orderOf.2 hw)).1 y
          (Subgroup.mem_subgroupOf.1 hy)).symm
    · let := Fintype.ofFinite K
      exact CFSG.CGT.PushingUpLit.CGT6K1.lieModel_PSL_two_of_mulEquiv_SL_two (by omega)
        (by rw [← Nat.card_eq_fintype_card]; exact hK)
        ((Subgroup.subgroupOfEquivOfLe hR).trans (rankOneEquivSL K a hK).symm)
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR).toEquiv,
        card_rankOneGroupOne hK]
      have hfactor : (2 ^ (2 * a + 1)) ^ 2 - 1 =
          (2 ^ (2 * a + 1) + 1) * (2 ^ (2 * a + 1) - 1) := by
        simpa using Nat.sq_sub_sq (2 ^ (2 * a + 1)) 1
      rw [hfactor]
      exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hpq _) _
  · let x : ↥(F4.reeGamma K a) :=
      ⟨torusPair a (1, w), CFSG.LieType.Ree.LargeReeCover.torusPair_mem_reeGamma a hK _⟩
    have hB : szSubB K a ≤ F4.reeGamma K a := szSubB_le_reeGamma hK
    let S := (szSubB K a).subgroupOf (F4.reeGamma K a)
    refine ⟨x, Subgroup.mem_subgroupOf.2 (rankOne_torusPair_mem_reeFixedTorus hK _ _), ?_,
      S, ?_, Or.inr ?_, ?_⟩
    · change orderOf x = r
      rw [Subgroup.orderOf_mk, orderOf_injective (torusPair a)
        (CFSG.RankThree.LargeReeOrder.torusPair_injective hK), Prod.orderOf,
        orderOf_one, Nat.lcm_one_left, hw]
    · have hxR : torusPair a (1, w) ∈ rankOneGroupTwo K a := by
        rw [rankOneTorusPair_right]
        exact Subgroup.subset_closure (Or.inl (Or.inr ⟨w, rfl⟩))
      intro y hy
      rw [mem_centralizer_iff]
      rintro _ rfl
      apply Subtype.ext
      exact commute_rankOneGroupTwo_szSubB _ hxR y (Subgroup.mem_subgroupOf.1 hy)
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, a, ha, K,
        inferInstance, inferInstance, rfl, hK,
        ⟨(Subgroup.subgroupOfEquivOfLe hB).trans
          ((szSubBEquiv (K := K) (a := a)).symm.trans (rankOneEquivSuzuki K a ha hK))⟩⟩))
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv,
        ← Nat.card_congr (szSubBEquiv (K := K) (a := a)).toEquiv,
        card_rankOneGroupTwo ha hK]
      exact dvd_mul_of_dvd_right hpq _

theorem uc22s218_f4_dvd_add_one_or_sq_add_one {K : Type} [Field K] [Finite K]
    [CharP K F4.prime] {a p : ℕ} (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ 2 ^ (2 * a + 1) - 1)
    (hrk : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(F4.reeGamma K a))) :
    p ∣ 2 ^ (2 * a + 1) + 1 ∨ p ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := by
  have : Finite (CFSG.Blueprint.Chevalley.ModGL F4.tag K) :=
    CFSG.LieType.Chevalley.finite_modGL
  by_cases hp3 : p = 3
  · subst hp3
    have hq := CFSG.two_pow_mod_three_of_odd (show Odd (2 * a + 1) from ⟨a, rfl⟩)
    exact Or.inl (Nat.dvd_iff_mod_eq_zero.2 (by omega))
  · 
    have hrk' : 2 ≤ CFSG.pRank p ↥(F4.reeGamma K a) := by
      rwa [CFSG.SectionRank.pRank_eq_open_pRank_top]
    obtain ⟨d, hd, hpd⟩ := CFSG.RankThree.PartOne.K128.ree_class hK hp
      (hp.five_le_of_ne_two_of_ne_three hp2 hp3) hrk'
    rcases hd with rfl | rfl | rfl
    · exact (hpq (by simpa [CFSG.RankThree.PartOne.K128.phiF4] using hpd)).elim
    · exact Or.inl (by simpa [CFSG.RankThree.PartOne.K128.phiF4] using hpd)
    · exact Or.inr (by simpa [CFSG.RankThree.PartOne.K128.phiF4] using hpd)

end CFSG.LocalAnalysis.UniquenessCase.UC22
