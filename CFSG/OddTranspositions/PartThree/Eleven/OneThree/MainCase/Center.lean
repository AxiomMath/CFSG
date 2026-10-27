module

public import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.TwoPoint
import CFSG.OddTranspositions.PartThree.EightNine.Main
import CFSG.OddTranspositions.PartFour.SeventeenTwo

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ
open CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G}


namespace MainHyp

variable {hC : HypothesisC D}

theorem pCore_le_center (h : MainHyp hC) :
    CFSG.pCore 2 (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha) := by
  obtain ⟨β, hβ⟩ := exists_mem_Dalpha hC
  obtain ⟨s, hs⟩ := mem_blockClass_iff.mp hβ.1
  have hbβ : s * hC.d * s⁻¹ ∈ β := by
    rw [hs]
    exact ⟨hC.d, hC.d_mem_alpha, rfl⟩
  have hbStar : s * hC.d * s⁻¹ ∈ DalphaStar D hC.alpha := subset_DalphaStar hβ hbβ
  refine pCore_le_center_of_forall_conj_eq hC hbStar fun q hq => ?_
  have hqN : (q : G) ∈ Subgroup.normalizer hC.alpha :=
    (Halpha_le_normalizer_block D hC.alpha) q.2
  have hqα : (fun x => (q : G) * x * (q : G)⁻¹) '' hC.alpha = hC.alpha :=
    cimg_eq_self_of_mem_normalizer hqN
  have hqβ : cimg (q : G) β ∈ blockLine D hC.alpha β := by
    rw [h.blockLine_eq hβ]
    refine Set.mem_insert_of_mem _ ⟨(q : G), ?_, rfl⟩
    exact ⟨q, hq, rfl⟩
  have hqβDα : cimg (q : G) β ∈ Dalpha D hC.alpha := by
    have h := Dalpha.conj hC.setup.normal hβ (q : G)
    rwa [hqα] at h
  have hbimg : (q : G) * (s * hC.d * s⁻¹) * (q : G)⁻¹ ∈ cimg (q : G) β :=
    ⟨s * hC.d * s⁻¹, hbβ, rfl⟩
  rw [h.blockLine_eq_pair hβ] at hqβ
  rcases hqβ with hqβα | hqββ
  · exact absurd hqβα hqβDα.2.2.1
  · rw [hqββ] at hbimg
    have h89 := lemma8_9_of_theorem8_7 theorem8_7_holds
    unfold Lemma8_9 at h89
    exact h89 G D hC h.rad h.not_wreath β hβ (s * hC.d * s⁻¹) hbβ q hq hbimg

end MainHyp

end CFSG.OddTranspositions.PartThree.ElevenThree
