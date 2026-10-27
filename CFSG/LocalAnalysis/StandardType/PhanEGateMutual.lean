module

public import CFSG.LocalAnalysis.StandardType.PhanEGateProj
public import CFSG.LocalAnalysis.StandardType.PhanEGateCoxeter

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Gate

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  {C : Type*} {δ : C → C → W} {J K : Set ι} {a b x y : C}

theorem projSet_eq_residue (hB : IsWeylDistanceBuilding cs δ)
    (h : IsClosestPair cs δ J K a b x y) :
    projSet cs δ J a (residue cs δ K b) = residue cs δ (cs.conjInter J K (δ x y)) x := by
  ext c
  constructor
  · intro hc
    obtain ⟨y', h'⟩ := (mem_projSet_iff hB).mp hc
    have hxc_parJ : δ x c ∈ cs.parabolic J :=
      mem_parabolic_of_mem_residue hB h.1 h'.1
    have hyy'_parK : δ y y' ∈ cs.parabolic K :=
      mem_parabolic_of_mem_residue hB h.2.1 h'.2.1
    have hmin : cs.IsMinimalDoubleCosetRep J K (δ x y) := h.isMinimalDoubleCosetRep hB
    have hdist : δ x c = δ x y * δ y y' * (δ x y)⁻¹ := h.dist_left_eq hB h'
    have hmul : δ x c * δ x y = δ x y * δ y y' := by
      rw [hdist]; group
    have hpar : δ x c ∈ cs.parabolic (cs.conjInter J K (δ x y)) :=
      cs.mem_parabolic_conjInter_of_mul_eq_mul hmin hxc_parJ hyy'_parK hmul
    exact (mem_residue_iff_mem_parabolic hB).mpr hpar
  · intro hc
    have hpar : δ x c ∈ cs.parabolic (cs.conjInter J K (δ x y)) :=
      (mem_residue_iff_mem_parabolic hB).mp hc
    obtain ⟨k, hk, hmul⟩ := cs.exists_mul_eq_mul_of_mem_parabolic_conjInter hpar
    have hcJx : c ∈ residue cs δ J x := by
      have hsub : cs.conjInter J K (δ x y) ⊆ J := cs.conjInter_subset J K (δ x y)
      exact residue_mono hsub x hc
    have hcJa : c ∈ residue cs δ J a := by
      rw [← residue_eq_of_mem hB h.1]
      exact hcJx
    have hproj : IsProjection cs δ (residue cs δ J a) y x := by
      rw [← h.eq_resProj_left hB]
      exact isProjection_resProj hB J a y
    have hgate := hproj.gate hB hcJa
    have hcy : δ c y = (δ x c)⁻¹ * δ x y := by
      rw [dist_inv hB y c, hgate.1, mul_inv_rev, dist_inv hB x y]
      group
    have hk_inv : (δ x c)⁻¹ * δ x y = δ x y * k⁻¹ := by
      have h2 : δ x y * k⁻¹ = (δ x c)⁻¹ * δ x y := by
        calc δ x y * k⁻¹ = ((δ x c)⁻¹ * (δ x c * δ x y)) * k⁻¹ := by group
          _ = ((δ x c)⁻¹ * (δ x y * k)) * k⁻¹ := by rw [hmul]
          _ = (δ x c)⁻¹ * δ x y := by group
      exact h2.symm
    have hcy_final : δ c y = δ x y * k⁻¹ := by
      rw [hcy, hk_inv]
    obtain ⟨y', hy'_res, hdist_cy'⟩ := exists_mem_residue_dist_eq_mul hB c y hk
    have hcy'_eq : δ c y' = δ x y := by
      rw [hdist_cy', hcy_final]
      group
    have hy'_Kb : y' ∈ residue cs δ K b := by
      rw [← residue_eq_of_mem hB h.2.1]
      exact hy'_res
    refine (mem_projSet_iff hB).mpr ⟨y', hcJa, hy'_Kb, ?_⟩
    intro x'' hx'' y'' hy''
    rw [hcy'_eq]
    exact h.2.2 x'' hx'' y'' hy''

theorem resProj_projSet (hB : IsWeylDistanceBuilding cs δ) {c : C}
    (hc : c ∈ projSet cs δ J a (residue cs δ K b)) :
    resProj cs δ K b c ∈ projSet cs δ K b (residue cs δ J a) ∧
      resProj cs δ J a (resProj cs δ K b c) = c := by
  obtain ⟨y', h'⟩ := (mem_projSet_iff hB).mp hc
  have hy' : resProj cs δ K b c = y' := h'.eq_resProj_right hB
  refine ⟨?_, ?_⟩
  · rw [hy']
    exact (mem_projSet_iff hB).mpr ⟨c, h'.symm hB⟩
  · rw [hy']
    exact (h'.symm hB).eq_resProj_right hB

theorem dist_resProj_eq (hB : IsWeylDistanceBuilding cs δ)
    (h : IsClosestPair cs δ J K a b x y) {c : C}
    (hc : c ∈ projSet cs δ J a (residue cs δ K b)) :
    δ c (resProj cs δ K b c) = δ x y := by
  obtain ⟨y', h'⟩ := (mem_projSet_iff hB).mp hc
  have hy' : resProj cs δ K b c = y' := h'.eq_resProj_right hB
  rw [hy']
  exact (h.dist_eq hB h').symm

end CFSG.ClassicalInvolution.Phan.PhanE.Gate

end
