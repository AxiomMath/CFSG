module

public import CFSG.RankThree.PartOne.S12.Facts
public import CFSG.RankThree.PartOne.S12.Sec13
public import CFSG.RankThree.PartOne.S12.Sec13Base
public import CFSG.RankThree.PartOne.S12.Sec12Three
public import CFSG.RankThree.PartOne.S12.Sec132
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

structure Sec13Facts (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G)
    (L E : Subgroup G) : Prop where
  irreducible : torusIrreducible E
  noTransvection : ¬ torusHasTransvection p E
  zeroStar : sectionTenZeroStar p A ⊆ sectionTenOne p A
  inZeroStar : L ∈ thetaCompZeroStarE p E
  reflection : ∀ t ∈ reflectionSet p E, E = autFixedInG E t ⊔ autMovedInG E t ∧
    autFixedInG E t ⊓ autMovedInG E t = ⊥ ∧ Nat.card ↥(autMovedInG E t) = p
  axes : ∀ t ∈ reflectionSet p E, ∀ s ∈ reflectionSet p E, autFixedInG E t ⊓ autFixedInG E s ≠ ⊥
  centralizer : ¬ p ∣ Nat.card (Subgroup.center L) →
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G)
  conjugates : ∀ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)), w ∉ cNormalizer c →
    ∃ x ∈ torusImage E L, ∃ y ∈ torusImage E L,
      x * (E.normalizerMonoidHom ⟨w, hw⟩ * y * (E.normalizerMonoidHom ⟨w, hw⟩)⁻¹) ≠
        (E.normalizerMonoidHom ⟨w, hw⟩ * y * (E.normalizerMonoidHom ⟨w, hw⟩)⁻¹) * x
  reinstantiate : ∀ X ∈ thetaCompZeroStarE p E, ∃ (B : Subgroup G) (c' : G),
    B ∈ admissibleTriples p E ∧ c' ∈ B ∧ c' ≠ 1 ∧
      Sec12Hyp G p B c' X E ∧ Sec12Facts G p B c' X E
  kt_le : ∀ J ∈ thetaCompZeroStarE p E, ∀ t ∈ reflectionSet p E, t ∈ torusImage E J →
    ∀ K : Subgroup G, IsKt p E t K → K ≤ J

theorem Sec13Facts.of_nodes (hSchreier : SchreierFor InCatalog) (hTwoAction : TwoActionInputs)
    (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple) (h11 : Sec11One)
    (h122 : Node122) (h122b : Node122b) (h123 : Node123) (h124 : Node124) (h125 : Node125)
    (h126 : Node126) (h127 : Node127) (h128 : Node128) (h129 : Node129)
    {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hT : ¬ Outcome152Five p E A (lieGenerated p E)) :
    Sec13Facts G p A c L E := by
  obtain ⟨hirr, hnot, hzero⟩ := sec13_one_of_nodes h126 h127 h128 h129 h hT
  have hL : L ∈ thetaCompZeroStarE p E := by
    refine Sec12Hyp.mem_thetaCompZeroStarE hSchreier hTwoAction h106 h ?_
    rcases h122 G p A c L E h with hG | hS
    · exact Sec12Three.hCE_generic h hG.center_pPrime (h.restr_of_generic hG)
    · exact Sec12Three.hCE_su5 hS
  have hreinst : ∀ X ∈ thetaCompZeroStarE p E, ∃ (B : Subgroup G) (c' : G),
      B ∈ admissibleTriples p E ∧ c' ∈ B ∧ c' ≠ 1 ∧
        Sec12Hyp G p B c' X E ∧ Sec12Facts G p B c' X E := by
    intro X hX
    obtain ⟨B, hB, hXz⟩ := hX.1
    have hXF : X ∈ thetaComponentFamily p B := hXz.1
    obtain ⟨c', hc'B, hc'1, hXc⟩ := mem_thetaComponentFamily_iff.mp hXF
    have hXzs : X ∈ sectionTenZeroStar p B :=
      ⟨hXz, hXF, fun K hK hXK => hX.2.2 K ⟨B, hB, hK⟩ hXK⟩
    have hX1 : X ∈ sectionTenOne p B := sec13_one_b h11 h126 h127 h128 h129 h hT hB hXzs
    have h' : Sec12Hyp G p B c' X E := h.reinstantiate hB hc'B hc'1 ⟨⟨hXzs, hX1⟩, hXc⟩
    exact ⟨B, c', hB, hc'B, hc'1, h', Sec12Facts.of_nodes h122 h122b h123 h124 h125 h'⟩
  refine ⟨hirr, hnot, hzero, hL, fun t ht => ?_, fun t ht s hs => ?_, fun hZ => ?_,
    fun w hw hwH => ?_, hreinst, fun J hJ t ht htJ K hK => ?_⟩
  · exact node121a_of_hyp G p A c L E h t ht
  · exact node134one_of_hyp G p A c L E h t ht s hs
  · exact node136b_of_node122 h122 G p A c L E h hZ
  · exact node138b_of_inputs h124 G p A c L E h w hw hwH
  · obtain ⟨B, c', hB, hc'B, hc'1, h', -⟩ := hreinst J hJ
    exact isKt_le_of_mem_torusImage h' selected_prime_elements_normalize_theta_components htJ
      (node121a_of_hyp G p A c L E h t ht).1 hK

end CFSG.RankThree.PartOne
