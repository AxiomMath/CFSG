module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329Data
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieCrossExc
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6TwMain
public import CFSG.Foundations.SteinbergCADefinitionNodes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel chevalleyExceptionalTags)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.Open (StatedLieTag)
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree
  (four_le_pRank_three_of_untwistedModel_any)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3 (twistedE6ThreeRankFour_holds)
open CFSG.HardMathSupport.Timmesfeld.Tables.T1b (e6RankLowerTw e6RankLowerUntw)

theorem k329heavy_four_le_pRank_quotient
    (S : Type) [Group S] [Finite S] {t : StatedLieTag} (ht : t ∈ k329HeavyTags) {n r e : ℕ}
    (hL : LieModel S t n r e) : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  simp only [k329HeavyTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨-, hm⟩ := hL.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
    exact four_le_pRank_three_of_untwistedModel_any (Or.inl rfl) hm
  · obtain ⟨-, hm⟩ := hL.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
    exact four_le_pRank_three_of_untwistedModel_any (Or.inr (Or.inl rfl)) hm
  · exact twistedE6ThreeRankFour_holds S r e
      (hL.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags]))
  · obtain ⟨-, hm⟩ := hL.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
    exact four_le_pRank_three_of_untwistedModel_any (Or.inr (Or.inr (Or.inl rfl))) hm
  · obtain ⟨-, hm⟩ := hL.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
    exact four_le_pRank_three_of_untwistedModel_any (Or.inr (Or.inr (Or.inr rfl))) hm

theorem k329heavy_card_center_dvd
    {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K) {t : StatedLieTag}
    {n r e : ℕ} (hL : LieModel (K ⧸ Subgroup.center K) t n r e) :
    Nat.card (Subgroup.center K) ∣ (genericOrders t n r e).1 * (genericOrders t n r e).2 *
      ((exceptionalOrders t n r e).1 * (exceptionalOrders t n r e).2) := by
  have hq' : CFSG.IsQuasisimple K :=
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1).2 hq
  have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq'
    (MulEquiv.refl (K ⧸ Subgroup.center K))
  obtain ⟨-, ⟨eq⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models _ t n r e hL
  rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
    Nat.card_congr eq.toEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod] at hdvd
  have hm : ∀ m : ℕ, Nat.card (Multiplicative (ZMod m)) = m := fun m => by
    rw [Nat.card_congr Multiplicative.toAdd]
    exact Nat.card_zmod m
  simpa only [hm] using hdvd

theorem k329heavy_three_dvd_table {t : StatedLieTag} (ht : t ∈ k329HeavyTags) {n r e : ℕ}
    (h : 3 ∣ (genericOrders t n r e).1 * (genericOrders t n r e).2 *
      ((exceptionalOrders t n r e).1 * (exceptionalOrders t n r e).2)) :
    (t = .E6 ∧ 3 ∣ r ^ e - 1) ∨ (t = .twistedE6 ∧ 3 ∣ r ^ e + 1) := by
  simp only [k329HeavyTags, Finset.mem_insert, Finset.mem_singleton] at ht
  have hx : ¬ 3 ∣ (exceptionalOrders t n r e).1 * (exceptionalOrders t n r e).2 := by
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> unfold exceptionalOrders <;> split <;>
      first | decide | (exfalso; contradiction)
  have h' : 3 ∣ (genericOrders t n r e).1 * (genericOrders t n r e).2 :=
    ((Nat.Prime.dvd_mul Nat.prime_three).1 h).resolve_right hx
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp only [genericOrders, Nat.mul_one] at h'
  · omega
  · exact Or.inl ⟨rfl, (Nat.dvd_gcd_iff.1 h').2⟩
  · exact Or.inr ⟨rfl, (Nat.dvd_gcd_iff.1 h').2⟩
  · exact absurd (h'.trans (Nat.gcd_dvd_left 2 _)) (by decide)
  · omega

theorem k329heavy_six_le_pRank_of_center
    {K : Type} [Group K] [Finite K] {t : StatedLieTag} {n r e : ℕ}
    (hL : LieModel (K ⧸ Subgroup.center K) t n r e) (hZ : 3 ∣ Nat.card (Subgroup.center K))
    (h : (t = .E6 ∧ 3 ∣ r ^ e - 1) ∨ (t = .twistedE6 ∧ 3 ∣ r ^ e + 1)) :
    6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  rcases h with ⟨rfl, h3⟩ | ⟨rfl, h3⟩
  · exact (e6RankLowerUntw K n r e hL h3).1 hZ
  · exact (e6RankLowerTw K n r e hL h3).1 hZ

theorem k329HeavyRankStatement_holds
    : k329HeavyRankStatement := by
  intro K _ _ hq t ht n r e hL _
  by_cases hZ : 3 ∣ Nat.card (Subgroup.center K)
  · have h6 := k329heavy_six_le_pRank_of_center hL hZ
      (k329heavy_three_dvd_table ht (hZ.trans (k329heavy_card_center_dvd hq hL)))
    omega
  · rw [← CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hZ]
    exact k329heavy_four_le_pRank_quotient _ ht hL

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
