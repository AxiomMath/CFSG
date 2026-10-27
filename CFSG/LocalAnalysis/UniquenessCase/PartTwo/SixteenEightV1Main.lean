module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1Idx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1Rank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16e_v1Sub_eq_bot_of_noncyclic (D : Data G) (h61 : UC6.R6_1 D) {V₀ V L : Subgroup G}
    (h : Hyp125 D V₀ V) (hV : IsElemAbelian 2 V) {i p : ℕ} (hp : p ∈ D.sig)
    {B : Subgroup G} (hBM : B ≤ D.M) (hBp : IsPGroup p B) (hBc : ¬ IsCyclic B)
    (hBV₁ : ∀ b ∈ B, ∀ u ∈ v1Sub D.M V₀ V hV L, b * u = u * b)
    (hC : ¬ centralizer (E3.cClos V i D.T : Set G) ≤ D.M) : v1Sub D.M V₀ V hV L = ⊥ := by
  by_contra hne
  have hP := D.sylowM.isPGroup
  have hTM := D.sylowM.le
  have hW : E3.wClos V i D.T ≤ D.T := iSup₂_le fun _ hA => hA.1
  have hV1V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h hV
  have hVT : V ≤ D.T := s15_13A_le_T h
  have hV12 : IsPGroup 2 (v1Sub D.M V₀ V hV L) := hV.isPGroup.to_le hV1V
  obtain ⟨u, hu, hu1, hcomm⟩ := s15_Glue3_exists_fixed (P := E3.wClos V i D.T)
    (U := v1Sub D.M V₀ V hV L) (hP.to_le hW) hV12 hne
    (fun x hx => s15_Infra_le_normalizer_v1Sub h hV (hTM (hW hx)))
  apply hC
  have huc : u ∈ E3.cClos V i D.T := ⟨hVT (hV1V hu), mem_centralizer_iff.2 hcomm⟩
  refine le_trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 huc)) ?_
  exact centralizer_le_of_noncyclic D h61 hp hBM hBp hBc hu1
    ⟨1, by simpa using hV.2 u (hV1V hu)⟩
    (fun b hb => Subgroup.mem_centralizer_singleton_iff.2 (hBV₁ b hb u hu))

theorem s16e_v1Sub_eq_bot (D : Data G) (hSg : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Setting16 D V₀ V L) (h0 : V₀ = ⊥)
    (hc : Case168_2Star D V₀ V hV L ∨ Case168_5Star D V₀ V hV L)
    (hC : ¬ centralizer (E3.cClos V D.k D.T : Set G) ≤ D.M) :
    v1Sub D.M V₀ V hV L = ⊥ := by
  rcases hc with hc | hc
  · obtain ⟨B, hBM, hBp, hBc, hBV₁⟩ :=
      s16e_exists_noncyclic_cent_of_case168_2Star D hSg hS.hyp151 h0 hc
    have h3 : 3 ∈ D.sig := by rw [hc.2.2]; exact Set.mem_singleton 3
    exact s16e_v1Sub_eq_bot_of_noncyclic D h61 hS.hyp151.hyp125 hV h3 hBM hBp hBc hBV₁ hC
  · obtain ⟨B, hBM, hBp, hBc, hBV₁⟩ :=
      s16e_exists_noncyclic_cent_of_case168_5Star D hS.hyp151 h0 hc
    have h3 : 3 ∈ D.sig := by rw [hc.2.2.2]; exact Set.mem_singleton 3
    exact s16e_v1Sub_eq_bot_of_noncyclic D h61 hS.hyp151.hyp125 hV h3 hBM hBp hBc hBV₁ hC

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
