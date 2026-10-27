module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.MS93.S4AH1
public import CFSG.Quasithin.MS93.Sec2Three
public import CFSG.Quasithin.MS93.SkHyp

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement

section Group

variable {Γ : Type} [Group Γ]

theorem burnsideSL3G_le_normalizer_inf_centralizer {N U W : Subgroup Γ}
    (hU : N ≤ Subgroup.normalizer (U : Set Γ)) (hW : N ≤ Subgroup.normalizer (W : Set Γ)) :
    N ≤ Subgroup.normalizer ((U ⊓ Subgroup.centralizer (W : Set Γ) : Subgroup Γ) : Set Γ) := by
  refine le_normalizer_of_map_conj_le fun n hn => ?_
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨hsU, hsC⟩ := Subgroup.mem_inf.mp hs
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hU hn) s).mp hsU, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hw' : n⁻¹ * w * n⁻¹⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hW (inv_mem hn)) w).mp hw
  have hc := Subgroup.mem_centralizer_iff.mp hsC _ hw'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hc ⊢
  calc w * (n * s * n⁻¹) = n * (n⁻¹ * w * n * s) * n⁻¹ := by group
    _ = n * (s * (n⁻¹ * w * n)) * n⁻¹ := by rw [hc]
    _ = n * s * n⁻¹ * w := by group

theorem burnsideSL3G_le_normalizer_of_commutator_le {S Z K : Subgroup Γ}
    (hKZ : K ≤ Subgroup.normalizer (Z : Set Γ)) (hc : ⁅S, K⁆ ≤ S ⊔ Z) :
    K ≤ Subgroup.normalizer ((S ⊔ Z : Subgroup Γ) : Set Γ) :=
  le_normalizer_sup_of_commutator_le hKZ hc

end Group

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem burnsideSL3G_exists_isCritical_geo (h : PUHyp M T L) {x β : Vtx (puAmalgam h.le)}
    (hx : IsMVtx _ x) (hxβ : (puAmalgam h.le).treeGraph.Adj x β) :
    ∃ x₀ : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) x x₀ ∧
      geo (puAmalgam h.le) x x₀ 1 = β := by
  obtain ⟨x₁, hc₁⟩ := exists_isCritical_of_isMVtx _ h.hyp20 hx
  obtain ⟨g, hg, hgβ⟩ := exists_mem_stab_smul _ (adj_geo_one_of_isCritical _ h.critDist_pos hc₁)
    hxβ
  have hgx : g • x = x := (mem_stab _).mp hg
  refine ⟨g • x₁, ?_, ?_⟩
  · have := (isCritical_smul _ g x x₁).mpr hc₁
    rwa [hgx] at this
  · rw [← hgx, geo_smul]
    exact hgβ

end CFSG.Quasithin.MS93.S4L
