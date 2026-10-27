module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLPairs
import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOther
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcOut
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLESixTwoCent
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLNoJ1Mark
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLNoJ1MarkTriality
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLNoJ1Ppd
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.Monster.Existence.Compat.Sp8
import CFSG.RankThree.GF2n.Smith81.InspPpd
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Open TableB
open CFSG.Blueprint.Chevalley (adjointGroup)
open CFSG.RankThree.GF2n.Smith81.Insp (ppd_of_dvd_ordE6)

private abbrev E6Rec (K : Type) [Field K] : Type :=
  LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)

section Cells


private theorem false_of_dvd_card_fixed {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (hfin : Finite (E6Rec K)) {s : MulAut (E6Rec K)} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1)
    (hsI : s ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K
      (LargeEvenChevH (LargeEvenCartanE 6) K false))
    {J₁ : Subgroup (E6Rec K)} (hJ : J₁ ≤ ggFix s) {p : ℕ} (hp : p = 13 ∨ p = 73)
    (hdvd : p ∣ Nat.card J₁) : False := by
  haveI := CFSG.Monster.Existence.Compat.subsingleton_units_of_card_two hK
  obtain ⟨y, rfl⟩ := chevIDImage_subset_inn_of_subsingleton
    (LargeEvenChevH (LargeEvenCartanE 6) K false) hsI
  let e : E6Rec K ≃* adjointGroup .E6 K := recipeChevEquiv .E6 K
  have hy3 : y ^ 3 = 1 := by
    have hc : MulAut.conj (y ^ 3) = 1 := by rw [map_pow]; exact hs3
    have hmem : e (y ^ 3) ∈ Subgroup.center (adjointGroup .E6 K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut (E6Rec K) => φ (e.symm g)) hc
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      have h2 : e (y ^ 3 * e.symm g) = e (e.symm g * y ^ 3) := by
        rw [(mul_inv_eq_iff_eq_mul.1 h1)]
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
      exact h2.symm
    rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot] at hmem
    exact e.injective (by simpa using hmem)
  have hy1 : y ≠ 1 := fun h => hs1 (by rw [h, map_one])
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hcomm : ∀ z : ↥J₁, (z : E6Rec K) * y = y * z := fun z => by
    have h := mem_ggFix.1 (hJ z.2)
    rw [MulAut.conj_apply] at h
    exact (mul_inv_eq_iff_eq_mul.1 h).symm
  haveI := hfin
  rcases hp with rfl | rfl
  · haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 13 hdvd
    exact E6_two_not_commute_order_thirteen hK e (x := (z : E6Rec K))
      (by rwa [Subgroup.orderOf_coe]) hyo (hcomm z)
  · haveI : Fact (Nat.Prime 73) := ⟨by norm_num⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 73 hdvd
    exact E6_two_not_commute_order_seventy_three hK e (x := (z : E6Rec K))
      (by rwa [Subgroup.orderOf_coe]) hyo (hcomm z)

private theorem card_dvd_ordE6_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 1)
    (J₁ : Subgroup (E6Rec K)) : Nat.card J₁ ∣ ordE6 (2 ^ 1) := by
  rw [← CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_E6
    (untwistedChevalleyModel_largeEven .E6 hK)]
  exact Subgroup.card_subgroup_dvd_card J₁

theorem ggInndiagOnCompAt_E6_two_triD4 {lab : LargeEvenLabel} (htag : lab.tag = .E6)
    (hn : lab.n = 1) : GGInndiagOnCompAt lab fun n l => l = ⟨.triD4, 0, n⟩ := by
  obtain ⟨t, r, g⟩ := lab
  dsimp only at htag hn
  subst htag hn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, ?_⟩
  intro _ _ hfin s _ n hs3 hs1 _ _ hsI _ _ J₁ hJ₁ hmark _
  obtain ⟨hn1, hdvd⟩ := ordTrialityD4_dvd_card_of_marking hmark
  obtain ⟨p, hp, hpd⟩ := exists_ppd_dvd_ordTrialityD4 hn1 (Or.inr (Or.inr rfl)) (by omega)
  obtain ⟨a, ha, had⟩ := ppd_of_dvd_ordE6 hp (by omega)
    ((hpd.trans hdvd).trans (card_dvd_ordE6_two hK J₁))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  have hle := Nat.le_of_dvd (by omega) had
  obtain rfl : n = 1 := by omega
  exact false_of_dvd_card_fixed (hK.trans (pow_one 2)) hfin hs3 hs1 hsI hJ₁.1 (Or.inl rfl)
    ((by decide +kernel : 13 ∣ ordTrialityD4 (2 ^ 1)).trans hdvd)

theorem ggInndiagOnCompAt_E6_two_aPair {lab : LargeEvenLabel} (htag : lab.tag = .E6)
    (hn : lab.n = 1) :
    GGInndiagOnCompAt lab fun n l => l = ⟨.A, 2, 3 * n⟩ ∨ l = ⟨.twA, 2, 3 * n⟩ := by
  obtain ⟨t, r, g⟩ := lab
  dsimp only at htag hn
  subst htag hn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, ?_⟩
  intro _ _ hfin s _ n hs3 hs1 _ _ hsI _ _ J₁ hJ₁ hmark _
  have hJR := card_dvd_ordE6_two hK J₁
  rcases exists_label_disjunct_marking hmark with hm | hm
  · obtain ⟨hm1, hdvd⟩ := ordA_two_dvd_card_of_marking hm
    obtain ⟨p, hp, hpd⟩ := exists_ppd_dvd_ordA_two_nine (n := n) (by omega)
    obtain ⟨a, ha, had⟩ := ppd_of_dvd_ordE6 hp (by omega) ((hpd.trans hdvd).trans hJR)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    have hle := Nat.le_of_dvd (by omega) had
    obtain rfl : n = 1 := by omega
    exact false_of_dvd_card_fixed (hK.trans (pow_one 2)) hfin hs3 hs1 hsI hJ₁.1 (Or.inr rfl)
      ((by decide +kernel : 73 ∣ ordA 2 (2 ^ (3 * 1))).trans hdvd)
  · obtain ⟨hm1, hdvd⟩ := ordTwistedA_dvd_card_of_twA_marking (by norm_num) hm
    obtain ⟨p, hp, hpd⟩ := exists_ppd_dvd_ordTwistedA_two_eighteen (n := n) (by omega)
    obtain ⟨a, ha, had⟩ := ppd_of_dvd_ordE6 hp (by omega) ((hpd.trans hdvd).trans hJR)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    have hle := Nat.le_of_dvd (by omega) had
    omega

end Cells

end CFSG.StandardType.SCFourCover

end
