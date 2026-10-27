module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperCommutingImagesCenter
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePointRoot

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint

universe u v

variable {G : Type u} [Group G]

theorem properCommutingImages_regular_complement_ne_bot
    {Ω : Type v} [MulAction G Ω] [Finite Ω]
    (S : Subgroup G) (alpha : Ω)
    (hdegree : 3 ≤ Nat.card Ω)
    (hregular : IsRegularOn S {omega : Ω | omega ≠ alpha}) : S ≠ ⊥ := by
  let U : Set Ω := {omega | omega ≠ alpha}
  have hU : U = (Set.univ : Set Ω) \ {alpha} := by
    ext omega
    simp only [U, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_univ,
      Set.mem_singleton_iff, true_and]
  have hcard : U.ncard + 1 = Nat.card Ω := by
    rw [hU]
    simpa only [Set.ncard_univ] using
      (Set.ncard_sdiff_singleton_add_one (s := (Set.univ : Set Ω)) (Set.mem_univ alpha))
  have htwo : 1 < U.ncard := by omega
  obtain ⟨beta, hbeta, _⟩ := Set.exists_ne_of_one_lt_ncard htwo alpha
  obtain ⟨gamma, hgamma, hne⟩ := Set.exists_ne_of_one_lt_ncard htwo beta
  obtain ⟨s, hs, _⟩ := hregular hbeta hgamma
  intro hbot
  have hsone : (s : G) = 1 := Subgroup.mem_bot.mp (hbot ▸ s.property)
  rw [hsone, one_smul] at hs
  exact hne hs.symm

variable [Finite G]

theorem properCommutingImages_coset_degree
    (H : Subgroup G) (hH : IsStronglyEmbedded H) :
    Odd (Nat.card (G ⧸ H)) ∧ 3 ≤ Nat.card (G ⧸ H) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hTH⟩ := hH.containsSylowTwo
  have hindexOdd : Odd H.index := Nat.not_even_iff_odd.mp (fun heven =>
    T.not_dvd_index ((even_iff_two_dvd.mp heven).trans (Subgroup.index_dvd_of_le hTH)))
  have hindexGt : 1 < H.index := Subgroup.one_lt_index_of_ne_top hH.ne_top
  have hthree : 3 ≤ H.index := by
    have hmod := Nat.odd_iff.mp hindexOdd
    omega
  exact ⟨H.index_eq_card ▸ hindexOdd, H.index_eq_card ▸ hthree⟩

theorem properCommutingImages_corefree_nontrivial_normal_root
    (H : Subgroup G) (hH : IsStronglyEmbedded H) (hrank : TwoRankAtLeastTwo G)
    (hcore : CFSG.oddCore G = ⊥) :
    ∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ H ∧ (S.subgroupOf H).Normal ∧
      S ≠ ⊥ ∧ IsRegularOn S {omega : G ⧸ H | omega ≠ QuotientGroup.mk 1} := by
  obtain ⟨S, hS, hSH, hSN, hregular⟩ :=
    exists_normal_regular_twoSubgroup_of_corefree H hH hrank hcore
  have hSne := properCommutingImages_regular_complement_ne_bot S
    (QuotientGroup.mk 1 : G ⧸ H) (properCommutingImages_coset_degree H hH).2 hregular
  exact ⟨S, hS, hSH, hSN, hSne, hregular⟩

theorem properCommutingImages_corefree_involutions_commute
    (H : Subgroup G) (hH : IsStronglyEmbedded H) (hrank : TwoRankAtLeastTwo G)
    (hcore : CFSG.oddCore G = ⊥)
    (a b : G) (haH : a ∈ H) (haorder : orderOf a = 2)
    (hbH : b ∈ H) (hborder : orderOf b = 2) : Commute a b := by
  obtain ⟨S, hS, hSH, hSN, hSne, _⟩ :=
    properCommutingImages_corefree_nontrivial_normal_root H hH hrank hcore
  exact properCommutingImages_center_image_commute S
    (properCommutingImages_involutions_in_normal_root_center H hH S hS hSH hSN hSne
      a haH haorder)
    (properCommutingImages_involutions_in_normal_root_center H hH S hS hSH hSN hSne
      b hbH hborder)

end CFSG.ShultStronglyClosedTI
