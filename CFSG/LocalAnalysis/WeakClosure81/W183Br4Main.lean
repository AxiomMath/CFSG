module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br4Comp
public import CFSG.LocalAnalysis.WeakClosure81.W183Br4Lgl
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5PSp4Five
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.WeakClosure81.W18KernBridge
public import CFSG.LocalAnalysis.WeakClosure81.W18T189FourSteps

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace MinCex183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem false_of_branchIV
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (h1413 : Asch5_14_13Prime)
    (h162 : W3Thm162Gt2 G) (h172 : W3Thm172Weak G) (h5_4 : Asch5_4) (h5_11 : Asch5_11AS)
    (h5_13 : Asch5_13AS) (c : MinCex183 D V₀ V H i) (h2 : ¬ Concl182 D V₀ V H i)
    (hK : kerMV V H ≤ Subgroup.centralizer (eOmegaZ H D.T : Set G)) {L : Subgroup G}
    (hL : IsComponentModN (kerMV V H) H L) (hLT : L ⊔ D.T = H)
    (hX : HasQuotShape L (kerMV V H : Set G) (fun X _ => ShapeIV X)) {g : G}
    (hgK : ¬ vInH V H g ≤ kerMV V H) (hgi : E3.mQuot (conjSubgroup V g) (vInH V H g) ≤ i)
    (hA : 3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g)) : False := by
  classical
  obtain ⟨hOK, -⟩ := exists_component182_ker_AS h172 h5_4 h5_11 h5_13 c h2
  obtain ⟨X, instX, φ, hφs, hφk, hXS⟩ := hX
  letI : Group X := instX
  have hgood : Br4Good X := br4Good_of_shapeIV hGA hXS
  have hXgood : HasQuotShape L (kerMV V H : Set G) (fun X _ => Br4Good X) :=
    ⟨X, instX, φ, hφs, hφk, hgood⟩
  have hXbase : HasQuotShape L (kerMV V H : Set G)
      (fun X _ => IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a) :=
    ⟨X, instX, φ, hφs, hφk, hgood.1, hgood.nonabelian⟩
  by_cases h5 : CFSG.Blueprint.LieModel X .PSp 2 5 1
  · have hL5 : IsComponentModN (OInf H) H L := hOK.symm ▸ hL
    have hX5 : HasQuotShape L (OInf H : Set G)
        (fun X _ => CFSG.Blueprint.LieModel X .PSp 2 5 1) :=
      hOK.symm ▸ ⟨X, instX, φ, hφs, hφk, h5⟩
    exact false_of_psp4Five (Q := G) (H := H) (T := D.T) (M := H ⊓ D.M) (L := L)
      c.hyp.isSylowIn_T (c.calNIn_eq_AS h5_11 h5_13) hL5 hLT hX5
  · have hshape : Shape1413Prime X := by
      rcases hXS with hPSL | ⟨p, hp, hp5, hXp⟩
      · exact Or.inl hPSL
      · have hpne5 : p ≠ 5 := fun hp5' => h5 (hp5' ▸ hXp)
        have hpgt5 : 5 < p := lt_of_le_of_ne hp5 (Ne.symm hpne5)
        exact Or.inr ⟨p, hp, hpgt5, hXp⟩
    have hr : CFSG.Open.pRank 3 H ≤ 3 := by
      rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 3 H]
      exact (not_concl182_iff.mp h2).1.1
    have hconj : ∀ h ∈ H, conjSubgroup L h = L :=
      br4_conj_eq_of_good (H := H) (K := kerMV V H) (L := L) hr hL hXgood
    have hLn : H ≤ Subgroup.normalizer (L : Set G) := by
      intro h hh
      rw [Subgroup.mem_set_normalizer_iff]
      intro l
      have h1 : l ∈ conjSubgroup L h ↔ h * l * h⁻¹ ∈ L := mem_conjSubgroup_iff
      rw [hconj h hh] at h1
      exact h1
    have x : Ctx188 D V₀ V H i 3 := c.ctx188_three_AS h162 h5_11 h2
    obtain ⟨M⟩ := exists_modDataE c.hyp.isElemAbelian_eOmegaZ
      (Hyp183.normalizer_eOmegaZ H D.T)
    have hgam : Gam183 V H (eOmegaZ H D.T) i g := ⟨hgi, fun hle =>
      hgK ((le_inf (inf_le_right : vInH V H g ≤ H) hle).trans
        c.hyp.inf_centralizer_eOmegaZ_le_kerMV)⟩
    have hab : IsElemAbelian 2 (vInH V H g) :=
      (E3.isElemAbelian_conjSubgroup c.hyp.setting.isElemAbelian g).mono inf_le_left
    obtain ⟨-, hA4⟩ := four_le_card_img M inf_le_right hab hA
    have hAH : M.img (vInH V H g) ≤ M.img H := M.img_mono inf_le_right
    have hA4' : 4 ≤ Nat.card ↥(M.img (vInH V H g)) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv) ▸ hA4
    obtain ⟨hAe, hq⟩ := x.img_elemAbelian_quadratic M hgam
    obtain ⟨hLY, hnorm, hsimple, hnonab, hcent⟩ :=
      x.br1_comp_base M hK hL.2.2.1 hLn hLT hXbase
    have hshape' : Shape1413Prime ↥(M.img L) :=
      x.br1_shape_transport M hK hL.2.2.1
        (fun X' Y' _ _ e h => by
          rcases h with hPSL | ⟨p, hp, hp5, hXp⟩
          · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e hPSL)
          · exact Or.inr ⟨p, hp, hp5, CFSG.Blueprint.LieModel.of_mulEquiv e hXp⟩)
        ⟨X, instX, φ, hφs, hφk, hshape⟩
    exact br4_false_one_comp h1413 hLY hnorm hsimple hnonab hcent hshape' hAH hAe hA4' hq

end MinCex183

end CFSG.LocalAnalysis.WeakClosure81

end
