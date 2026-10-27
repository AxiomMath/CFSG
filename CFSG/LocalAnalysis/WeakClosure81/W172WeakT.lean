module

public import CFSG.LocalAnalysis.WeakClosure81.W172D3
public import CFSG.LocalAnalysis.WeakClosure81.W172Two5

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace MinCex172

variable {D : Data G} {V₀ V H : Subgroup G}

theorem w172_wClos_le_conj (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) 1 g) (hgT : vInH V H g ≤ D.T) :
    E3.wClos V 1 D.T ≤ conjSubgroup D.M g := by
  classical
  obtain ⟨M⟩ := exists_modDataE c.hyp.isElemAbelian_eOmegaZ (Hyp183.normalizer_eOmegaZ H D.T)
  have hT : IsPGroup 2 D.T := D.sylowM.isPGroup
  have hTH : D.T ≤ H := c.hyp.hyp171.2.1
  have hm := w172_two5 h162 c hg
  have hiS : 1 ≤ (c.ctx188 h162).iStar := (c.ctx188 h162).iStar_pos
  obtain ⟨e, he, hge⟩ := (c.ctx188 h162).w172_exists_mem_D M ⟨hg, hm.trans hiS⟩ hm
  have hI := (c.ctx188 h162).w172_invSys M
  have heT : e ∈ M.img D.T := by
    have h1 : e ∈ M.img (vInH V H g) := hge ▸ Subgroup.mem_zpowers e
    exact M.img_mono hgT h1
  refine E3.wClos_le_of_forall fun A₀ hA₀ => ?_
  obtain ⟨hA₀T, g', hA₀V, hmQ⟩ := E3.mem_gammaSet_iff.mp hA₀
  have hA₀H : A₀ ≤ H := hA₀T.trans hTH
  have hA₀A' : A₀ ≤ vInH V H g' := le_inf hA₀V hA₀H
  by_cases hC : A₀ ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G)
  · exact hC.trans (w172_centralizer_le_conj_M h162 c hg)
  · obtain ⟨a₀, ha₀A, ha₀C⟩ : ∃ a₀ ∈ A₀, a₀ ∉ Subgroup.centralizer (eOmegaZ H D.T : Set G) := by
      by_contra hcon
      exact hC fun a ha => by
        by_contra h
        exact hcon ⟨a, ha, h⟩
    have hg' : Gam183 V H (eOmegaZ H D.T) 1 g' :=
      ⟨(E3.mQuot_mono hA₀A').trans hmQ.le, fun hle => ha₀C (hle (hA₀A' ha₀A))⟩
    have hm' := w172_two5 h162 c hg'
    obtain ⟨e', he', hge'⟩ := (c.ctx188 h162).w172_exists_mem_D M ⟨hg', hm'.trans hiS⟩ hm'
    have ha₀H : a₀ ∈ H := hA₀H ha₀A
    have hr₀ : M.ρ ⟨a₀, ha₀H⟩ ∈ M.img (vInH V H g') :=
      M.mem_img.2 ⟨⟨a₀, ha₀H⟩, hA₀A' ha₀A, rfl⟩
    have hr₀1 : M.ρ ⟨a₀, ha₀H⟩ ≠ 1 := fun h1 => ha₀C ((M.ρ_eq_one_iff ⟨a₀, ha₀H⟩).1 h1)
    have hee' : M.ρ ⟨a₀, ha₀H⟩ = e' := by
      rw [hge'] at hr₀
      rcases (Subgroup.mem_zpowers_iff.mp hr₀) with ⟨k, hk⟩
      have hsq' : e' * e' = 1 := hI.sq e' he'
      have h2 : e' ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hsq'
      have hk' : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · exfalso
        apply hr₀1
        rw [← hk, hk', h, add_zero, zpow_mul, h2, one_zpow]
      · rw [← hk, hk', h, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
    have he'T : e' ∈ M.img D.T := by
      rw [← hee']
      exact M.mem_img.2 ⟨⟨a₀, ha₀H⟩, hA₀T ha₀A, rfl⟩
    have hcomm : e * e' = e' * e := (c.ctx188 h162).w172_comm_of_mem_img M hT he he' heT he'T
    intro a ha
    have haH : a ∈ H := hA₀H ha
    have hra : M.ρ ⟨a, haH⟩ ∈ M.img (vInH V H g') := M.mem_img.2 ⟨⟨a, haH⟩, hA₀A' ha, rfl⟩
    rw [hge'] at hra
    have hsq : e * e = 1 := hI.sq e he
    have hcomm' : M.ρ ⟨a, haH⟩ * e = e * M.ρ ⟨a, haH⟩ := by
      rcases (Subgroup.mem_zpowers_iff.mp hra) with ⟨k, hk⟩
      rw [← hk]
      exact ((Commute.zpow_left (Commute.symm hcomm) k).eq)
    exact (w172_mem_conj_iff_comm h162 c hg hm M hge hsq he.1 haH).mpr hcomm'

end MinCex172

end CFSG.LocalAnalysis.WeakClosure81

end
