module

import CFSG.Quasithin.MS93.Sec2Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.MS93.Sec2Geo

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ SimpleGraph CFSG.Open

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem zv_le_qv_of_dist_lt {ν μ : Vtx X} (hd : X.treeGraph.dist ν μ < critDist X) :
    Zv X ν ≤ Qv X μ := by
  by_cases hν : IsMVtx X ν
  · rw [zv_of_isMVtx X hν]; exact zm_le_qv_of_dist_lt X hν hd
  · rw [zv_of_not_isMVtx X hν]
    by_cases hνμ : ν = μ
    · subst hνμ; exact zh_le_qv X ν
    have hpos : 0 < X.treeGraph.dist ν μ := by
      rcases Nat.eq_zero_or_pos (X.treeGraph.dist ν μ) with h0 | h0
      · exact absurd ((dist_eq_zero_iff X).mp h0) hνμ
      · exact h0
    have hadj := adj_geo_one X hpos
    have hρ : IsMVtx X (geo X ν μ 1) := by
      by_contra hρ; exact hν ((isMVtx_iff_of_adj X hadj).mpr hρ)
    refine (zh_le_zm X hadj.symm).trans (zm_le_qv_of_dist_lt X hρ ?_)
    rw [dist_geo_right X (show 1 ≤ X.treeGraph.dist ν μ by omega)]
    omega

theorem zv_le_centralizer (h : Hyp20 X) (hb : 0 < critDist X) (μ : Vtx X) :
    Zv X μ ≤ Subgroup.centralizer (Qv X μ : Set X.Universal) := by
  by_cases hμ : IsMVtx X μ
  · rw [zv_of_isMVtx X hμ]
    exact (zm_le_xm X h hb hμ).trans (xm_le_centralizer X μ)
  · rw [zv_of_not_isMVtx X hμ]; exact zh_le_centralizer X μ

theorem zv_le_centralizer_zv (h : Hyp20 X) (hb : 0 < critDist X) {ν μ : Vtx X}
    (hd : X.treeGraph.dist ν μ < critDist X) :
    Zv X ν ≤ Subgroup.centralizer (Zv X μ : Set X.Universal) :=
  (zv_le_qv_of_dist_lt X hd).trans
    (Subgroup.le_centralizer_iff.mp (zv_le_centralizer X h hb μ))

theorem isElemAbelian_zv (h : Hyp20 X) (hb : 0 < critDist X) (μ : Vtx X) :
    IsElemAbelian 2 (Zv X μ) := by
  by_cases hμ : IsMVtx X μ
  · rw [zv_of_isMVtx X hμ]; exact isElemAbelian_zm X h hb hμ
  · rw [zv_of_not_isMVtx X hμ]; exact isElemAbelian_xm X μ

theorem zv_le_vi {δ ρ : Vtx X} {i : ℕ} (hd : X.treeGraph.dist δ ρ ≤ i) : Zv X ρ ≤ Vi X δ i :=
  le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx X | X.treeGraph.dist δ ρ ≤ i}) => Zv X ρ) ρ hd
    le_rfl

theorem vi_le_vi {δ δ' : Vtx X} {i j : ℕ} (hd : i + X.treeGraph.dist δ δ' ≤ j) :
    Vi X δ i ≤ Vi X δ' j := by
  refine iSup₂_le fun ρ hρ => zv_le_vi X ?_
  have := dist_triangle X δ' δ ρ
  rw [tdist_comm X δ' δ] at this
  simp only [Set.mem_ofPred_eq] at hρ
  omega

theorem vi_le_qv {δ μ : Vtx X} {i : ℕ} (hd : i + X.treeGraph.dist δ μ < critDist X) :
    Vi X δ i ≤ Qv X μ := by
  refine iSup₂_le fun ρ hρ => zv_le_qv_of_dist_lt X ?_
  have := dist_triangle X ρ δ μ
  rw [tdist_comm X ρ δ] at this
  simp only [Set.mem_ofPred_eq] at hρ
  omega

theorem vi_le_centralizer_vi (h : Hyp20 X) (hb : 0 < critDist X) {δ δ' : Vtx X} {i j : ℕ}
    (hd : i + j + X.treeGraph.dist δ δ' < critDist X) :
    Vi X δ i ≤ Subgroup.centralizer (Vi X δ' j : Set X.Universal) := by
  refine iSup₂_le fun ρ hρ => Subgroup.le_centralizer_iff.mpr ?_
  refine iSup₂_le fun ρ' hρ' => Subgroup.le_centralizer_iff.mpr ?_
  apply zv_le_centralizer_zv X h hb
  have h1 := dist_triangle X ρ δ ρ'
  have h2 := dist_triangle X δ δ' ρ'
  rw [tdist_comm X ρ δ] at h1
  simp only [Set.mem_ofPred_eq] at hρ hρ'
  omega

theorem isElemAbelian_iSup {G : Type*} [Group G] {ι : Type*} (K : ι → Subgroup G)
    (hK : ∀ i, IsElemAbelian 2 (K i))
    (hc : ∀ i j, K i ≤ Subgroup.centralizer (K j : Set G)) : IsElemAbelian 2 (⨆ i, K i) := by
  have hcomm : ⨆ i, K i ≤ Subgroup.centralizer ((⨆ i, K i : Subgroup G) : Set G) := by
    refine iSup_le fun i => Subgroup.le_centralizer_iff.mpr (iSup_le fun j => ?_)
    exact Subgroup.le_centralizer_iff.mpr (hc i j)
  refine ⟨isMulCommutative_subgroup_iff.mpr fun x hx y hy => (hcomm hx y hy).symm, ?_⟩
  intro x hx
  rw [Subgroup.iSup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact (hK i).2 x hi
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxy : x * y = y * x := by
      rw [← Subgroup.iSup_eq_closure] at hx hy
      exact (hcomm hy x hx)
    rw [(Commute.mul_pow hxy 2), ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem isElemAbelian_vi (h : Hyp20 X) (hb : 0 < critDist X) {δ : Vtx X} {i : ℕ}
    (hd : 2 * i < critDist X) : IsElemAbelian 2 (Vi X δ i) := by
  have hVi : Vi X δ i = ⨆ ρ : {ρ : Vtx X // X.treeGraph.dist δ ρ ≤ i}, Zv X ρ := by
    rw [Vi, iSup_subtype']
    rfl
  rw [hVi]
  refine isElemAbelian_iSup _ (fun ρ => isElemAbelian_zv X h hb ρ) fun ρ ρ' => ?_
  apply zv_le_centralizer_zv X h hb
  have := dist_triangle X ρ.1 δ ρ'.1
  rw [tdist_comm X ρ.1 δ] at this
  have h1 := ρ.2
  have h2 := ρ'.2
  omega

end CFSG.Quasithin.MS93.S45
