module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorARank
import CFSG.LocalAnalysis.StandardType.KGLangTorAInput

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggNbrLangTorTypeALabel_of_typeASix {p : ℕ} {lab : LargeEvenLabel}
    (h : GGNbrLangTypeASixLabel p lab) : GGNbrLangTorTypeALabel p lab := by
  obtain ⟨ht, hr⟩ := h
  refine ⟨ht, ?_⟩
  rcases hr with ⟨rfl, h2 | h5⟩ | ⟨rfl, h4⟩
  · norm_num [h2]
  · norm_num [h5]
  · norm_num [h4]

theorem ggNbrLangAxisOn_typeASixNonSplit :
    GGNbrLangAxisOn fun p lab => GGNbrLangTypeASixLabel p lab ∧ ¬ GGTypeASplitPrime p lab := by
  intro G _ _ p B Bs x L D J hcfg y K hK hN
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBstar : GGBstar p B Bs := hcfg.2.1
  refine NbrLangTypeA.ggMarkingAll_mono ?_
    (ggRegKG_markingAll_and (ggRegKG_markingAll_and
      (ggRegKG_markingAll_and (ggRegKG_markingAll_perfect_simple ↥K)
        (ggRegKG_markingAll_guard (S := fun _ lab => lab.tag = .A ∨ lab.tag = .twA)
          (P := GGRawInnField p) (p := p)
          (fun lab hlab hs => ggRawInnFieldOn_typeA p hp hp2 lab hlab hs) ↥K))
      (ggRegKG_markingAll_guard (S := fun _ lab => lab.tag = .A ∨ lab.tag = .twA)
        (P := GGRawPCyclic p) (p := p)
        (fun lab hlab hs => ggRawPCyclicOn_typeA p hp hp2 lab hlab hs) ↥K))
      (ggMarkingAll_kgLangAxisTorA kgLangAxisTorAInput_holds hp hp2 ↥K))
  rintro lab R _ I F θ ⟨⟨⟨⟨hX, hs, hna⟩, hrawθ⟩, hpcθ⟩, hKGθ⟩ hSl hall b₀ hb₀ hb₀I
  have hT := ggNbrLangTorTypeALabel_of_typeASix hSl.1
  obtain ⟨B₀, hB₀, hcard, hb₀', hmem⟩ := exists_index_prime_of_raw_pcyclic hp hBstar.2.1 hs hna
    (hpcθ hT.1) ((ggLAut K θ).comp (Subgroup.inclusion hN)) hb₀ hb₀I
  exact ⟨B₀, hB₀, hcard, hb₀', fun b hb h => (hmem b hb).2 h,
    ggNbrLangTorACore_of_hyperplane hBstar.2.1 hBstar.2.2.2 hN hX θ
      (hrawθ hT.1 hs hna).2.2.1 (hKGθ hT) hall b₀ hb₀ hb₀I hB₀ hmem
      (ggNbr_sq_le_card_A₀ hcfg hK hN θ hB₀ hcard hmem)
      fun hsp => absurd hsp hSl.2⟩

@[expose] def GGNbrLangRest12NonRegOpenLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrLangRest12NonRegNotRankLabel p lab ∧
    (GGNbrLangTypeASixLabel p lab → GGTypeASplitPrime p lab)

theorem ggNbrLangAxisOn_rest12NonRegNotRank_of_open
    (h : GGNbrLangAxisOn GGNbrLangRest12NonRegOpenLabel) :
    GGNbrLangAxisOn GGNbrLangRest12NonRegNotRankLabel := by
  refine (GGNbrLangAxisOn.or ggNbrLangAxisOn_typeASixNonSplit h).mono ?_
  intro p lab hS
  by_cases hs : GGNbrLangTypeASixLabel p lab ∧ ¬ GGTypeASplitPrime p lab
  · exact Or.inl hs
  · exact Or.inr ⟨hS, fun h6 => Classical.byContradiction fun hn => hs ⟨h6, hn⟩⟩

end CFSG.StandardType
