module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem isCyclic_outer_of_perfect_cover_of_suzukiModel'
    {H J : Type} [Group H] [Group J] [Group.IsPerfect J] {f : ℕ}
    (h : CFSG.Blueprint.SuzukiModel H 2 f)
    (e : J ⧸ Subgroup.center J ≃* H) : IsCyclic (Outer J) :=
  (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity H 2 f h).2 J ⟨e⟩ |>.1

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

theorem isCyclic_outer_thetaQuot_of_mem_thetaComponentsAt
    (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz) (c : Ctx82E3 D)
    {x : G} (hx1 : x ≠ 1) {L : Subgroup G} (hL : L ∈ thetaComponentsAt 3 x)
    (h3 : ¬ 3 ∣ Nat.card L) :
    IsCyclic (Outer (L ⧸ aschbacherSolvableCore 3 L)) := by
  classical
  obtain ⟨hLle, hLsub⟩ := CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp hL
  let C : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let P' : Subgroup ↥C := L.subgroupOf C
  let Q : Type := P' ⧸ aschbacherSolvableCore 3 P'
  let S : Type := Q ⧸ Subgroup.center Q
  have hQ : CFSG.IsQuasisimple Q := hLsub.2.2
  have hsimple : IsSimpleGroup S := hQ.2.1
  haveI : IsSimpleGroup S := hsimple
  have hnab : ∃ a b : S, a * b ≠ b * a := hQ.2.2
  have hK : CFSG.Open.IsKGroup ↥C := isKGroup_centralizer c hx1
  let φ : P' →* S :=
    (QuotientGroup.mk' (Subgroup.center Q)).comp
      (QuotientGroup.mk' (aschbacherSolvableCore 3 P'))
  have hφ : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective (Subgroup.center Q)).comp
      (QuotientGroup.mk'_surjective _)
  have hcat : CFSG.Open.IsCatalogGroup S :=
    hK.isCatalogGroup_of_surjective P' hnab φ hφ
  have hcard : Nat.card P' = Nat.card L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLle).toEquiv
  have h3S : ¬ 3 ∣ Nat.card S := by
    intro h
    have h1 : 3 ∣ Nat.card Q := h.trans (Subgroup.card_quotient_dvd_card (Subgroup.center Q))
    have h2 : 3 ∣ Nat.card P' :=
      h1.trans (Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 P'))
    rw [hcard] at h2
    exact h3 h2
  obtain ⟨f, hf⟩ := hPSz S hnab hcat h3S
  haveI : Group.IsPerfect Q := hQ.1
  have hcycQ : IsCyclic (Outer Q) :=
    isCyclic_outer_of_perfect_cover_of_suzukiModel' (J := Q) hf (MulEquiv.refl S)
  have hmap : P'.map C.subtype = L := by
    change (L.subgroupOf C).map C.subtype = L
    exact Subgroup.map_subgroupOf_eq_of_le hLle
  have he : Q ≃* (L ⧸ aschbacherSolvableCore 3 L) :=
    hmap ▸ CFSG.RankThree.PartTwo.Sec13.thetaQuotEquivSub C P'
  exact isCyclic_of_injective (equivalence he).symm.toMonoidHom
    (equivalence he).symm.injective

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
