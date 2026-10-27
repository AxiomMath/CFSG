module

public import CFSG.Quasithin.MS93.S5B512

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S512N

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {F : Type} [Field F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem pair_geo (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    {μ γ : Vtx (puAmalgam h.le)} (hc : IsCritical _ μ γ) :
    IsMVtx _ μ ∧ IsMVtx _ γ ∧ IsMVtx _ (geo _ μ γ 2) ∧
      (puAmalgam h.le).treeGraph.dist μ γ = 4 ∧
      (puAmalgam h.le).treeGraph.Adj μ (geo _ μ γ 1) ∧
      (puAmalgam h.le).treeGraph.Adj (geo _ μ γ 1) (geo _ μ γ 2) ∧
      (puAmalgam h.le).treeGraph.Adj (geo _ μ γ 2) (geo _ μ γ 3) ∧
      (puAmalgam h.le).treeGraph.Adj (geo _ μ γ 3) γ ∧
      (puAmalgam h.le).treeGraph.dist μ (geo _ μ γ 2) = 2 ∧
      (puAmalgam h.le).treeGraph.dist (geo _ μ γ 2) γ = 2 ∧
      IsCritical _ γ μ ∧ geo _ γ μ 2 = geo _ μ γ 2 ∧ geo _ γ μ 1 = geo _ μ γ 3 ∧
      geo _ γ μ 3 = geo _ μ γ 1 := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hd : (puAmalgam h.le).treeGraph.dist μ γ = 4 := hc.2.1.trans hb4
  have h4 : geo _ μ γ 4 = γ := by
    have := geo_dist (puAmalgam h.le) μ γ
    rwa [hd] at this
  have hs : ∀ i, i ≤ 4 → geo _ γ μ (4 - i) = geo _ μ γ i := fun i hi => by
    have := geo_symm (puAmalgam h.le) (u := μ) (w := γ) (i := i) (by omega)
    rwa [hd] at this
  refine ⟨hc.1, hc.isMVtx_right _ hyp, isMVtx_geo_two _ hyp hb0 hc, hd, ?_, ?_, ?_, ?_, ?_, ?_,
    ms22_iii _ hyp hb0 h.centHyp hc, hs 2 (by omega), hs 3 (by omega), hs 1 (by omega)⟩
  · exact adj_geo_one _ (by omega)
  · exact adj_geo _ (i := 1) (by omega)
  · exact adj_geo _ (i := 2) (by omega)
  · have := adj_geo _ (u := μ) (w := γ) (i := 3) (by omega)
    rwa [h4] at this
  · exact dist_geo _ (by omega)
  · rw [dist_geo_right _ (by omega), hd]

theorem chain_geo (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4) {q : ℕ}
    {α' ν μ₁ μ₂ : Vtx (puAmalgam h.le)} (hch : S5B.IsChain512 h q a α' ν μ₁ μ₂) :
    IsCritical _ (baseA (puAmalgam h.le)) α' ∧ geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _ ∧
      IsCritical _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) ∧
      geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 2 = baseA _ ∧
      (∃ y ∈ stab _ (baseA (puAmalgam h.le)), μ₁ = y • geo _ (baseA (puAmalgam h.le)) α' 2) ∧
      IsCritical _ μ₂ (baseA (puAmalgam h.le)) ∧ IsCritical _ (baseA (puAmalgam h.le)) μ₂ ∧
      geo _ μ₂ (baseA (puAmalgam h.le)) 2 = μ₁ ∧ geo _ (baseA (puAmalgam h.le)) μ₂ 2 = μ₁ ∧
      (∃ y ∈ stab _ μ₁, μ₂ = y • baseA (puAmalgam h.le)) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  obtain ⟨hαβ, -, -, hc, hμ, hcμ, hs2⟩ := hch
  have hlamAt : μ₁ ∈ S5B.lamAt h q a (baseA _) α' (geo _ (baseA (puAmalgam h.le)) α' 2) :=
    ⟨1, one_smul _ _, by rw [one_smul, hαβ], by simpa using hμ⟩
  have hstep : S5B.IsLamStep h q a (baseA _) α' μ₁ := ⟨hc, hlamAt, hcμ⟩
  obtain ⟨-, hgeo⟩ := S5B.lamStep_geo h hb4 hstep
  obtain ⟨-, hgeo2⟩ := S5B.lamStep_geo h hb4 hs2
  rw [hgeo] at hgeo2
  have hc2 : IsCritical _ μ₂ (baseA (puAmalgam h.le)) := by
    have := hs2.2.2
    rwa [hgeo] at this
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hc2', hm2, -, -⟩ := pair_geo h hb4 hc2
  have hmem := hs2.2.1
  rw [hgeo] at hmem
  refine ⟨hc, hαβ, hcμ, hgeo, S5B.exists_mem_stab_of_mem_lam hμ, hc2, hc2', hgeo2,
    hm2.trans hgeo2, S5B.exists_mem_stab_of_mem_lamAt h hmem⟩

end S512N

end CFSG.Quasithin.MS93
