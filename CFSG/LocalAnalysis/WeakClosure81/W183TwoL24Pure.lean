module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoL24Two
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoL24Cent
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Comp2
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Fam
public import CFSG.LocalAnalysis.WeakClosure81.W18Asch5

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

section Certified


namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem w183tp_false_pure (h210 : Asch2_10) (c : MinCex183 D V₀ V H i)
    (h2 : ¬ Concl182 D V₀ V H i) (x : Ctx188 D V₀ V H i 3) (M : ModDataE H (eOmegaZ H D.T))
    (hN : calNIn H D.T = {H ⊓ D.M})
    (hK : kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G)) {L : Subgroup G}
    (hLc : IsComponentModN (kerMV V H) H L) (hLT : L ⊔ D.T = H)
    (hQ : HasQuotShape L (kerMV V H : Set G) (fun X _ => IsL2 X 2 ∨ IsU3 X 2))
    (hall : ∀ g' : G, Gam183 V H (eOmegaZ H D.T) i g' →
      (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g') = 2)
    {g : G} (hgT : vInH V H g ≤ D.T) (hgK : ¬ vInH V H g ≤ kerMV V H)
    (hgi : E3.mQuot (conjSubgroup V g) (vInH V H g) ≤ i)
    (hA : (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g) = 2) :
    False := by
  classical
  have hgam : Gam183 V H (eOmegaZ H D.T) i g :=
    ⟨hgi, fun hle => hgK ((le_inf inf_le_right hle).trans
      c.hyp.inf_centralizer_eOmegaZ_le_kerMV)⟩
  have hgM : g ∈ D.M := x.mem_M_of_relIndex_two M hall hgam hgT
  obtain ⟨-, a₁, -, -, himg, hord⟩ := x.exists_involution_img M hgK hgi hA
  have hd1 : M.ρ a₁ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have hd2 : M.ρ a₁ * M.ρ a₁ = 1 := by
    have h := pow_orderOf_eq_one (M.ρ a₁)
    rw [hord, pow_two] at h
    exact h
  have hdY : M.ρ a₁ ∈ M.img H := M.mem_img.2 ⟨a₁, a₁.2, rfl⟩
  have hX := x.w183tp_centralizes M hN hgM himg hord
  have hT : IsSylowIn 2 (M.img D.T) (M.img H) := x.br1_sylow M
  have hDT : D.T ≤ H := x.hyp.hyp171.2.1
  have hLH : L ≤ H := hLc.2.2.1
  have hQbase : HasQuotShape L (kerMV V H : Set G)
      (fun X _ => IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a) := by
    obtain ⟨X, hXg, φ, hφs, hφk, hP⟩ := hQ
    exact ⟨X, hXg, φ, hφs, hφk, w183tp_shape_base hP⟩
  have hshape : IsL2 ↥(M.img L) 2 ∨ IsU3 ↥(M.img L) 2 :=
    x.br1_shape_transport M hK hLH
      (fun X Y _ _ e h => h.imp (CFSG.Blueprint.LieModel.of_mulEquiv e)
        (CFSG.Blueprint.LieModel.of_mulEquiv e)) hQ
  have hr : CFSG.Open.pRank 3 H ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 3 H]
    exact (not_concl182_iff.mp h2).1.1
  have hcard := h210 G H D.T (kerMV V H) L x.hyp.kgroup x.hyp.isSylowIn_T hr hLc
    (w183tp_shape_dvd hQ) hLT
  rcases w183tp_asch210_split hcard with hone | ⟨t, htT, hne, hall'⟩
  · have hLn : H ≤ Subgroup.normalizer (L : Set G) := by
      rw [← hLT]
      exact sup_le Subgroup.le_normalizer
        (fun t ht => conjSubgroup_eq_iff_mem_normalizer.mp (hone t ht))
    obtain ⟨hLY, hnorm, hsimple, hnonab, hcent⟩ := x.br1_comp_base M hK hLH hLn hLT hQbase
    exact w183tp_false_one hT hLY hnorm hsimple hnonab hcent hshape hdY hd1 hd2 hX
  · have htwo := x.br1_twoComp M hK hLc hLT hQbase htT hne hall'
    have htHinv : t⁻¹ ∈ H := hDT (D.T.inv_mem htT)
    have himg2 : M.img (conjSubgroup L t) = cj (M.ρ ⟨t⁻¹, htHinv⟩) (M.img L) := by
      have h := M.img_conj (A := L) hLH (j := ⟨t⁻¹, htHinv⟩)
      rw [inv_inv] at h
      exact h.symm
    have hshape₂ : IsL2 ↥(M.img (conjSubgroup L t)) 2 ∨ IsU3 ↥(M.img (conjSubgroup L t)) 2 := by
      rw [himg2]
      exact w183tp_shape_cj _ hshape
    exact w183tp_false_two hT htwo hshape hshape₂ hdY hd1 hd2 hX

end Ctx188

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
