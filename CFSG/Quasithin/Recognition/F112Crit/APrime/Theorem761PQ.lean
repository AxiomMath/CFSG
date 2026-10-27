module

public import CFSG.Quasithin.Recognition.F112Crit.APrime.Config
public import CFSG.Quasithin.Recognition.F112Crit.Lemma65

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.CosetGeom (stab ballStab nbrs vtype Vv critDist dist)

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T L E : Subgroup G}

private theorem vtype_eq_true_of_dist_eq_critDist (hA : ConfigA G₀ G₁ G₂ T L E)
    {γ δ : CosetGeom G₀ G₁ G₂} (hγ : vtype γ = false)
    (hγδ : dist γ δ = critDist G₀ G₁ G₂ E) : vtype δ = true := by
  cases h : vtype δ with
  | false =>
    exfalso
    have hv : vtype γ = vtype δ := by rw [hγ, h]
    have he : Even (dist γ δ) := (CosetGeom.vtype_eq_iff_even_dist hA.hyp.gen γ δ).mp hv
    rw [hγδ] at he
    exact (Nat.not_even_iff_odd.mpr hA.odd) he
  | true => rfl

theorem ConfigA.relIndex_Vv_inf_pCoreOf_le_two (hA : ConfigA G₀ G₁ G₂ T L E)
    (hL : LocalA G₀ G₁ G₂ E) {γ δ : CosetGeom G₀ G₁ G₂} (hγ : vtype γ = false)
    (hγδ : dist γ δ = critDist G₀ G₁ G₂ E) :
    (Vv E γ ⊓ pCoreOf 2 (stab δ)).relIndex (Vv E γ) ≤ 2 := by
  classical
  have hbpos : 0 < critDist G₀ G₁ G₂ E := (CosetGeom.critDist_spec hA.hypV hA.ne_bot).1
  have hδt : vtype δ = true := vtype_eq_true_of_dist_eq_critDist hA hγ hγδ
  obtain ⟨δ', hδ', hδ'dist⟩ :=
    CosetGeom.exists_adj_dist_eq hA.hyp.gen (α := γ) (δ := δ)
      (d := critDist G₀ G₁ G₂ E - 1) (by omega)
  have hP : Vv E γ ≤ stab δ ⊓ stab δ' :=
    le_inf (hL.le_stab γ hγ δ hγδ.le) (hL.le_stab γ hγ δ' (by omega))
  exact (hL.point δ hδt).relIndex_le_two δ' hδ' (Vv E γ) hP
    (hL.elemAbelian γ hγ).isPGroup

theorem ConfigA.inf_pCoreOf_le_of_dist_eq (hA : ConfigA G₀ G₁ G₂ T L E)
    (hL : LocalA G₀ G₁ G₂ E) {γ ν δ : CosetGeom G₀ G₁ G₂} (hγ : vtype γ = false)
    (hν : vtype ν = false) (hγν : dist γ ν = critDist G₀ G₁ G₂ E + 1) (hδ : δ ∈ nbrs ν)
    (hγδ : dist γ δ = critDist G₀ G₁ G₂ E) :
    Vv E γ ⊓ pCoreOf 2 (stab δ) ≤ pCoreOf 2 (stab ν) := by
  classical
  have hνγ : dist ν γ = critDist G₀ G₁ G₂ E + 1 := by
    rw [CosetGeom.dist_comm, hγν]
  obtain ⟨γ₁, hγ₁, hγ₁dist⟩ :=
    CosetGeom.exists_adj_dist_eq hA.hyp.gen (α := ν) (δ := γ)
      (d := critDist G₀ G₁ G₂ E) hνγ
  have hνδ : dist δ ν = 1 := by
    rw [CosetGeom.dist_comm, CosetGeom.dist_eq_one_iff_adj.mpr hδ]
  have hQδ : pCoreOf 2 (stab δ) ≤ stab ν :=
    (CosetGeom.pCoreOf_stab_le_ballStab_one hA.hyp δ).trans
      (CosetGeom.ballStab_le_stab_of_dist_le (n := 1) hνδ.le)
  have hγ₁γ : dist γ₁ γ = 1 := by
    rw [CosetGeom.dist_comm, CosetGeom.dist_eq_one_iff_adj.mpr hγ₁]
  have hQγ₁ : pCoreOf 2 (stab γ₁) ≤ stab γ :=
    (CosetGeom.pCoreOf_stab_le_ballStab_one hA.hyp γ₁).trans
      (CosetGeom.ballStab_le_stab_of_dist_le (n := 1) hγ₁γ.le)
  have hX : Vv E γ ⊓ pCoreOf 2 (stab δ) ≤ Vv E γ ⊓ stab ν :=
    le_inf inf_le_left (inf_le_right.trans hQδ)
  have hY : Vv E ν ⊓ pCoreOf 2 (stab γ₁) ≤ Vv E ν ⊓ stab γ :=
    le_inf inf_le_left (inf_le_right.trans hQγ₁)
  have hXi := ConfigA.relIndex_Vv_inf_pCoreOf_le_two hA hL hγ hγδ
  have hYi := ConfigA.relIndex_Vv_inf_pCoreOf_le_two hA hL hν hγ₁dist
  exact (no_mutual_offenders (Eγ := Vv E γ) (Qγ := pCoreOf 2 (stab γ)) (Hγ := stab γ)
    (Eν := Vv E ν) (Qν := pCoreOf 2 (stab ν)) (Hν := stab ν)
    (X := Vv E γ ⊓ pCoreOf 2 (stab δ)) (Y := Vv E ν ⊓ pCoreOf 2 (stab γ₁))
    (hL.star γ hγ) (hL.star ν hν) (hL.elemAbelian γ hγ) (hL.elemAbelian ν hν)
    (hL.pCoreOf_le_centralizer γ hγ) (hL.pCoreOf_le_centralizer ν hν)
    hX hY hXi hYi).1

theorem ConfigA.inf_pCoreOf_le_centralizer (hA : ConfigA G₀ G₁ G₂ T L E)
    (hL : LocalA G₀ G₁ G₂ E) {γ δ : CosetGeom G₀ G₁ G₂} (hγ : vtype γ = false)
    (hγδ : dist γ δ = critDist G₀ G₁ G₂ E) :
    Vv E γ ⊓ pCoreOf 2 (stab δ) ≤ Subgroup.centralizer (Vv E δ : Set G) := by
  classical
  have hbpos : 0 < critDist G₀ G₁ G₂ E := (CosetGeom.critDist_spec hA.hypV hA.ne_bot).1
  have hδt : vtype δ = true := vtype_eq_true_of_dist_eq_critDist hA hγ hγδ
  rw [Subgroup.le_centralizer_iff]
  refine Vv_le_of_forall_mem_nbrs (Z := E) hδt ?_
  intro μ hμ
  have hμt : vtype μ = false := vtype_eq_false_of_mem_nbrs hδt hμ
  have hδμ : dist δ μ = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hμ
  have hd1 : dist γ μ ≤ critDist G₀ G₁ G₂ E + 1 := by
    have := CosetGeom.dist_triangle hA.hyp.gen γ δ μ
    rw [hγδ, hδμ] at this
    exact this
  have hd2 : critDist G₀ G₁ G₂ E ≤ dist γ μ + 1 := by
    have := CosetGeom.dist_triangle hA.hyp.gen γ μ δ
    have hμδ : dist μ δ = 1 := by rw [CosetGeom.dist_comm]; exact hδμ
    rw [hγδ] at this
    omega
  have hne : dist γ μ ≠ critDist G₀ G₁ G₂ E := by
    intro h
    have hv : vtype γ = vtype μ := by rw [hγ, hμt]
    have he : Even (dist γ μ) := (CosetGeom.vtype_eq_iff_even_dist hA.hyp.gen γ μ).mp hv
    rw [h] at he
    exact (Nat.not_even_iff_odd.mpr hA.odd) he
  have hcases : dist γ μ = critDist G₀ G₁ G₂ E - 1 ∨
      dist γ μ = critDist G₀ G₁ G₂ E + 1 := by omega
  have hXle : Vv E γ ⊓ pCoreOf 2 (stab δ) ≤ Subgroup.centralizer (Vv E μ : Set G) := by
    rcases hcases with h | h
    · have hlt : dist γ μ < critDist G₀ G₁ G₂ E := by omega
      exact (inf_le_left.trans (hL.le_pCoreOf_of_dist_lt γ hγ μ hlt)).trans
        (hL.pCoreOf_le_centralizer μ hμt)
    · exact (ConfigA.inf_pCoreOf_le_of_dist_eq hA hL hγ hμt h
        (CosetGeom.mem_nbrs_symm hμ) hγδ).trans (hL.pCoreOf_le_centralizer μ hμt)
  exact Subgroup.le_centralizer_iff.mp hXle

theorem ConfigA.Vv_inf_pCoreOf_le (hA : ConfigA G₀ G₁ G₂ T L E)
    (hL : LocalA G₀ G₁ G₂ E) {γ γ' δ : CosetGeom G₀ G₁ G₂} (hγ : vtype γ = false)
    (hγδ : dist γ δ = critDist G₀ G₁ G₂ E) (hγ' : γ' ∈ nbrs γ) :
    Vv E δ ⊓ pCoreOf 2 (stab γ') ≤ pCoreOf 2 (stab γ) := by
  classical
  have hγ'γ : dist γ' γ = 1 := by
    rw [CosetGeom.dist_comm, CosetGeom.dist_eq_one_iff_adj.mpr hγ']
  have hPstab : Vv E δ ⊓ pCoreOf 2 (stab γ') ≤ stab γ :=
    (inf_le_right.trans (CosetGeom.pCoreOf_stab_le_ballStab_one hA.hyp γ')).trans
      (CosetGeom.ballStab_le_stab_of_dist_le (n := 1) hγ'γ.le)
  have hP2 : IsPGroup 2 (Vv E δ ⊓ pCoreOf 2 (stab γ') : Subgroup G) :=
    IsPGroup.to_le (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (stab γ')) inf_le_right
  have hQ1 := ConfigA.inf_pCoreOf_le_centralizer hA hL hγ hγδ
  have hEP : Vv E γ ⊓ pCoreOf 2 (stab δ) ≤ Vv E γ ⊓ Subgroup.centralizer
      ((Vv E δ ⊓ pCoreOf 2 (stab γ') : Subgroup G) : Set G) :=
    le_inf inf_le_left (hQ1.trans (Subgroup.centralizer_le inf_le_left))
  have hle : (Vv E γ ⊓ Subgroup.centralizer
      ((Vv E δ ⊓ pCoreOf 2 (stab γ') : Subgroup G) : Set G)).relIndex (Vv E γ) ≤ 4 :=
    (Subgroup.relIndex_le_of_le_left hEP Subgroup.index_ne_zero_of_finite).trans
      ((ConfigA.relIndex_Vv_inf_pCoreOf_le_two hA hL hγ hγδ).trans (by norm_num))
  exact StarBound.le_of_relIndex_le_four (hL.star γ hγ) hPstab hP2 hle

end CFSG.Quasithin.F112Crit.APrime

end
