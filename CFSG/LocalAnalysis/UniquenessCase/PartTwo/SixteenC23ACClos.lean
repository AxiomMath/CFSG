module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AGen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23a_centralizer_cClos_le (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hne : v1Sub D.M V₀ V h.hyp151.isElemAbelian L ≠ ⊥) (i : ℕ) :
    centralizer (E3.cClos V i D.T : Set G) ≤ D.M := by
  have hV := h.hyp151.isElemAbelian
  have hP := D.sylowM.isPGroup
  have hTM := D.sylowM.le
  have hW : E3.wClos V i D.T ≤ D.T := iSup₂_le fun _ hA => hA.1
  have hV1V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h.hyp151.hyp125 hV
  have hVT : V ≤ D.T := s15_13A_le_T h.hyp151.hyp125
  have hV12 : IsPGroup 2 (v1Sub D.M V₀ V hV L) := hV.isPGroup.to_le hV1V
  obtain ⟨u, hu, hu1, hcomm⟩ := s15_Glue3_exists_fixed (P := E3.wClos V i D.T)
    (U := v1Sub D.M V₀ V hV L) (hP.to_le hW) hV12 hne
    (fun x hx => s15_Infra_le_normalizer_v1Sub h.hyp151.hyp125 hV (hTM (hW hx)))
  have huc : u ∈ E3.cClos V i D.T := ⟨hVT (hV1V hu), mem_centralizer_iff.2 hcomm⟩
  exact le_trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 huc))
    (c23a_centralizer_le D h (Subgroup.mem_sup_right hu) hu1)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
