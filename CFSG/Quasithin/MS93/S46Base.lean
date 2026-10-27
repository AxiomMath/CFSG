module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutData
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.MS93.Sec2Two

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

section B4

variable {X}

theorem zm_le_qv_of_dist_le_three (hb : critDist X = 4) {δ μ : Vtx X} (hδ : IsMVtx X δ)
    (hd : X.treeGraph.dist δ μ ≤ 3) : ZM X δ ≤ Qv X μ :=
  zm_le_qv_of_dist_lt X hδ (by omega)

theorem zm_le_vv_of_adj {ρ δ : Vtx X} (hρδ : X.treeGraph.Adj ρ δ) (hδ : IsMVtx X δ) :
    ZM X δ ≤ Vv X ρ := by
  have h1 : Zv X δ ≤ Vv X ρ := le_iSup₂_of_le (f := fun μ (_ : μ ∈ {μ : Vtx X |
      X.treeGraph.dist ρ μ ≤ 2}) => Zv X μ) δ
    (show X.treeGraph.dist ρ δ ≤ 2 by rw [dist_eq_one_of_adj X hρδ]; omega) le_rfl
  rwa [zv_of_isMVtx X hδ] at h1

theorem vv_eq_iSup_of_not_isMVtx {ρ : Vtx X} (hρ : ¬ IsMVtx X ρ) :
    Vv X ρ = ⨆ δ ∈ X.treeGraph.neighborSet ρ, ZM X δ := by
  apply le_antisymm
  · refine iSup₂_le fun μ hμ => ?_
    have hμ' : X.treeGraph.dist ρ μ ≤ 2 := hμ
    by_cases hμM : IsMVtx X μ
    ·
      have hodd : ¬ Even (X.treeGraph.dist ρ μ) := by
        rw [even_dist_iff]
        tauto
      have h1 : X.treeGraph.dist ρ μ = 1 := by
        rcases (by omega : X.treeGraph.dist ρ μ = 0 ∨ X.treeGraph.dist ρ μ = 1 ∨
            X.treeGraph.dist ρ μ = 2) with h | h | h
        · exact absurd (by rw [h]; exact ⟨0, rfl⟩) hodd
        · exact h
        · exact absurd (by rw [h]; exact ⟨1, rfl⟩) hodd
      have hadj : X.treeGraph.Adj ρ μ := SimpleGraph.dist_eq_one_iff_adj.mp h1
      rw [zv_of_isMVtx X hμM]
      exact le_iSup₂_of_le (f := fun δ (_ : δ ∈ X.treeGraph.neighborSet ρ) => ZM X δ) μ hadj
        le_rfl
    · rw [zv_of_not_isMVtx X hμM]
      by_cases hμρ : μ = ρ
      · subst hμρ
        obtain ⟨δ, hδ⟩ := exists_adj X μ
        exact (zh_le_zm X hδ.symm).trans (le_iSup₂_of_le (f := fun δ (_ : δ ∈
          X.treeGraph.neighborSet μ) => ZM X δ) δ hδ le_rfl)
      · have h2 : X.treeGraph.dist ρ μ = 2 := by
          have hne : X.treeGraph.dist ρ μ ≠ 0 := fun h0 => hμρ ((dist_eq_zero_iff X).mp h0).symm
          have heven : Even (X.treeGraph.dist ρ μ) := by
            rw [even_dist_iff]
            tauto
          rcases heven with ⟨k, hk⟩
          omega
        have hlt : 0 < X.treeGraph.dist ρ μ := by omega
        set δ := geo X ρ μ 1 with hδdef
        have hρδ : X.treeGraph.Adj ρ δ := adj_geo_one X hlt
        have hδμ : X.treeGraph.Adj δ μ := by
          have := adj_geo X (u := ρ) (w := μ) (i := 1) (by omega)
          rwa [geo_of_le X (by omega : X.treeGraph.dist ρ μ ≤ 1 + 1)] at this
        exact (zh_le_zm X hδμ).trans (le_iSup₂_of_le (f := fun δ (_ : δ ∈
          X.treeGraph.neighborSet ρ) => ZM X δ) δ hρδ le_rfl)
  · refine iSup₂_le fun δ hδ => ?_
    have hδM : IsMVtx X δ := by
      have := (isMVtx_iff_of_adj X hδ)
      tauto
    exact zm_le_vv_of_adj hδ hδM

theorem vv_le_centralizer_of_not_isMVtx (h : Hyp20 X) (hb : 2 < critDist X) {ρ : Vtx X}
    (hρ : ¬ IsMVtx X ρ) : Vv X ρ ≤ Subgroup.centralizer (Vv X ρ : Set X.Universal) := by
  rw [vv_eq_iSup_of_not_isMVtx hρ]
  refine iSup₂_le fun δ hδ => ?_
  rw [Subgroup.le_centralizer_iff]
  refine iSup₂_le fun δ' hδ' => ?_
  have hδM : IsMVtx X δ := by have := isMVtx_iff_of_adj X hδ; tauto
  have hδ'M : IsMVtx X δ' := by have := isMVtx_iff_of_adj X hδ'; tauto
  have hd : X.treeGraph.dist δ' δ < critDist X := by
    have h1 := dist_triangle X δ' ρ δ
    rw [tdist_comm X δ' ρ, dist_eq_one_of_adj X hδ, dist_eq_one_of_adj X hδ'] at h1
    omega
  exact (zm_le_qv_of_dist_lt X hδ'M hd).trans (zm_le_centralizer_qv X h hδM |> fun h' =>
    Subgroup.le_centralizer_iff.mp h')

theorem vv_le_qv_of_adj_of_not_isMVtx (hb : 2 < critDist X) {ρ δ : Vtx X}
    (hρ : ¬ IsMVtx X ρ) (hρδ : X.treeGraph.Adj ρ δ) : Vv X ρ ≤ Qv X δ := by
  rw [vv_eq_iSup_of_not_isMVtx hρ]
  refine iSup₂_le fun δ' hδ' => ?_
  have hδ'M : IsMVtx X δ' := by have := isMVtx_iff_of_adj X hδ'; tauto
  refine zm_le_qv_of_dist_lt X hδ'M ?_
  have h1 := dist_triangle X δ' ρ δ
  rw [tdist_comm X δ' ρ, dist_eq_one_of_adj X hρδ, dist_eq_one_of_adj X hδ'] at h1
  omega

theorem vv_le_qv_of_dist_le_two (hb : critDist X = 4) {ρ μ : Vtx X} (hρ : ¬ IsMVtx X ρ)
    (hd : X.treeGraph.dist ρ μ ≤ 2) : Vv X ρ ≤ Qv X μ := by
  rw [vv_eq_iSup_of_not_isMVtx hρ]
  refine iSup₂_le fun δ hδ => ?_
  have hδM : IsMVtx X δ := by have := isMVtx_iff_of_adj X hδ; tauto
  refine zm_le_qv_of_dist_le_three hb hδM ?_
  have h1 := dist_triangle X δ ρ μ
  rw [tdist_comm X δ ρ, dist_eq_one_of_adj X hδ] at h1
  omega

theorem centerOf_vv_le_qv (h : Hyp20 X) (hC : CentHyp X) (hb : 2 < critDist X)
    {α μ : Vtx X} (hα : IsMVtx X α) (hμ : IsMVtx X μ) (hd : X.treeGraph.dist α μ = 2) :
    centerOf (Vv X α) ≤ Qv X μ := by
  set ρ := geo X α μ 1 with hρdef
  have hαρ : X.treeGraph.Adj α ρ := adj_geo_one X (by omega)
  have hρμ : X.treeGraph.Adj ρ μ := by
    have := adj_geo X (u := α) (w := μ) (i := 1) (by omega)
    rwa [geo_of_le X (by omega : X.treeGraph.dist α μ ≤ 1 + 1)] at this
  have hVQ : Vv X α ≤ Qv X ρ := by
    have h2 : Vv X α ≤ Qv X α := by
      refine iSup₂_le fun ν hν => ?_
      have hν' : X.treeGraph.dist α ν ≤ 2 := hν
      by_cases hνM : IsMVtx X ν
      · rw [zv_of_isMVtx X hνM]
        exact zm_le_qv_of_dist_lt X hνM (by rw [tdist_comm]; omega)
      · rw [zv_of_not_isMVtx X hνM]
        obtain ⟨κ, hκ⟩ := exists_adj X ν
        have hκM : IsMVtx X κ := by have := isMVtx_iff_of_adj X hκ; tauto
        by_cases hνα : X.treeGraph.Adj α ν
        · exact (zh_le_zm X hνα).trans (zm_le_qv_self X hα (by omega))
        ·
          exfalso
          have hodd : ¬ Even (X.treeGraph.dist α ν) := by rw [even_dist_iff]; tauto
          have h1 : X.treeGraph.dist α ν = 1 := by
            rcases (by omega : X.treeGraph.dist α ν = 0 ∨ X.treeGraph.dist α ν = 1 ∨
                X.treeGraph.dist α ν = 2) with e | e | e
            · exact absurd (by rw [e]; exact ⟨0, rfl⟩) hodd
            · exact e
            · exact absurd (by rw [e]; exact ⟨1, rfl⟩) hodd
          exact hνα (SimpleGraph.dist_eq_one_iff_adj.mp h1)
    exact h2.trans (qv_le_qv X h hα hαρ)
  have hZμ : ZM X μ ≤ Vv X α := by
    have : Zv X μ ≤ Vv X α := le_iSup₂_of_le (f := fun ν (_ : ν ∈ {ν : Vtx X |
        X.treeGraph.dist α ν ≤ 2}) => Zv X ν) μ (show X.treeGraph.dist α μ ≤ 2 by omega) le_rfl
    rwa [zv_of_isMVtx X hμ] at this
  have hcent : centerOf (Vv X α) ≤ Qv X ρ ⊓ Subgroup.centralizer (ZM X μ : Set X.Universal) :=
    le_inf (inf_le_left.trans hVQ) (inf_le_right.trans (Subgroup.centralizer_le hZμ))
  rw [hC μ ρ hμ hρμ.symm] at hcent
  exact hcent

end B4

end CFSG.Quasithin.MS93.S46
