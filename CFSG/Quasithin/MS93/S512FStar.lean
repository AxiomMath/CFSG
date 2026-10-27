module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.MS93.S512TChain

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S512F

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem exists_qv_sup_zm_eq_stab' (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _)
    (hq1 : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k)
    {g x : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hx : x ∈ puTrans h.le L (baseA _))
    (hc55 : S5.Concl55 h (2 ^ k) α' (geo _ (baseA (puAmalgam h.le)) α' 2) g x)
    {μ₁ : Vtx (puAmalgam h.le)} (hμeq : μ₁ = g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2 ∨
      μ₁ = x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) :
    ∃ ρ, (puAmalgam h.le).treeGraph.Adj (baseA _) ρ ∧ (puAmalgam h.le).treeGraph.Adj ρ μ₁ ∧
      Qv _ ρ ⊔ ZM _ α' = stab _ (baseA (puAmalgam h.le)) := by
  have hb0 := h.critDist_pos
  have hd4 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = critDist (puAmalgam h.le) := hc.2.1
  have hb2 := two_le_critDist _ h.hyp20 hb0
  have hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) (geo _ (baseA (puAmalgam h.le)) α' 2) := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rwa [hαβ] at this
  have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
  have hgα : g⁻¹ • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 (inv_mem hg)
  have hxα : x⁻¹ • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 (inv_mem hxst)
  have hαβ₁ : (puAmalgam h.le).treeGraph.Adj (baseA _) (g⁻¹ • baseB (puAmalgam h.le)) := by
    have := (adj_smul _ g⁻¹ _ _).2 (adj_baseA_baseB (puAmalgam h.le))
    rwa [hgα] at this
  obtain ⟨⟨hA1, hA2⟩, -, -⟩ := hc55
  rcases hμeq with rfl | rfl
  · refine ⟨_, hαβ₁, (adj_smul _ g⁻¹ _ _).2 hβγ, ?_⟩
    rwa [S512T.zHat_eq h hd hc hq1] at hA1
  · refine ⟨x⁻¹ • g⁻¹ • baseB (puAmalgam h.le), ?_, ?_, ?_⟩
    · have := (adj_smul _ x⁻¹ _ _).2 hαβ₁
      rwa [hxα] at this
    · exact (adj_smul _ x⁻¹ _ _).2 ((adj_smul _ g⁻¹ _ _).2 hβγ)
    · rw [qv_smul]
      exact hA2

end S512F

end CFSG.Quasithin.MS93
