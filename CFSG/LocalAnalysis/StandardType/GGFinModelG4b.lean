module

public import CFSG.LocalAnalysis.StandardType.GGFinModelCore
public import CFSG.LocalAnalysis.StandardType.GGFinModelIndex
public import CFSG.LocalAnalysis.StandardType.GGFinModelInnDiag
public import CFSG.LocalAnalysis.StandardType.GGFinModelCorner

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.HardMathSupport.Timmesfeld.LangTorus

namespace GGDatumModel

theorem ggBfull_diag_all
    {t : StatedLieTag} {f p : ℕ} {ht : GGExcFive t} (M : GGDatumModel t f p ht) {n : ℕ}
    [NeZero p] (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f) :
    ∀ b ∈ (M.torusData (n := n) hf hp hp2 hreg).ggBfull, GGInnDiagU t n f b := by
  intro b hb
  by_cases ht6 : t = .E6 ∨ t = .twistedE6
  · obtain ⟨z, rfl⟩ := hb
    refine ggFixGp_conj_innDiagU ht6 hf (M.torusData (n := n) hf hp hp2 hreg).pkg.inj
      ((M.torusData (n := n) hf hp hp2 hreg).uMap z) ?_
      ((M.torusData (n := n) hf hp hp2 hreg).uMap_mem_normalizer z)
    rw [← ggFixGp_eq_fix M.D M.hΦ]
    exact (M.torusData (n := n) hf hp hp2 hreg).uMap_mem_fix z
  · refine (M.torusData (n := n) hf hp hp2 hreg).ggBfull_diag_of_coprime
      (M.coprime_relIndex_of_not_corner hf hp hp2 hreg ?_) b hb
    intro hc
    rcases hc.2 with h | h
    · exact ht6 (Or.inl h.1)
    · exact ht6 (Or.inr h.1)

theorem ggBfull_coord_surj_inner_all
    {t : StatedLieTag} {f p : ℕ} {ht : GGExcFive t} (M : GGDatumModel t f p ht) {n : ℕ}
    [NeZero p] (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f) :
    ∀ g ∈ LatCorootSpan (ggU (absTag t) 6 f).D p, (∀ i, g (piB t p f i) = g i) →
      ∃ b : (M.torusData (n := n) hf hp hp2 hreg).ggBfull,
        (b : GGAutU t n f) ∈ (ggPsiU t n f).range ∧
          Multiplicative.toAdd ((M.torusData (n := n) hf hp hp2 hreg).ggCoord b) = g := by
  intro g hg hπ
  by_cases hc : GGCorner t p f
  · let z : Multiplicative (ggFixAdd p (piB t p f)) :=
      Multiplicative.ofAdd ⟨g, mem_ggFixAdd.2 hπ⟩
    refine ⟨⟨(M.torusData (n := n) hf hp hp2 hreg).ggBetaHom z, ⟨z, rfl⟩⟩, ?_, ?_⟩
    · rw [ggPsiU_range_eq_conj t n f]
      exact ((M.torusData (n := n) hf hp hp2 hreg).ggBetaHom_mem_inn_iff z).2
        (M.uMap_mem_range_of_corner hf hp hp2 hreg hc z hg)
    · rw [GGTorusData.ggCoord_apply]
      rfl
  · exact (M.torusData (n := n) hf hp hp2 hreg).ggBfull_coord_surj_of_coprime
      (M.coprime_relIndex_of_not_corner hf hp hp2 hreg hc) g hπ

end GGDatumModel

end CFSG.StandardType.GGFinModel
