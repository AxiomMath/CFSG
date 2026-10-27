module

public import CFSG.LocalAnalysis.WeakClosure81.W18T189FourSteps
public import CFSG.LocalAnalysis.WeakClosure81.W18ASTail
public import CFSG.LocalAnalysis.WeakClosure81.W18KernBridge
public import CFSG.LocalAnalysis.WeakClosure81.W18T189FourBridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

variable {G : Type} [Group G] [Finite G]

theorem tail189Four_AS_of_inputs (hO : LieOrderFormulasInput)
    (h66 : Asch6_6) : Tail189Four_AS G := by
  intro h162 h172 h5_4 h5_11 h5_12 h5_13 D V₀ V H i c h1 hK g hgT hgK hgi hA
  classical
  have x : Ctx188 D V₀ V H i 2 := c.ctx188_two_AS h162 h5_11 h5_13 h1
  obtain ⟨hsolv, hkerEq, hshape⟩ := c.exists_shape185_AS h172 h5_12 h5_11 h5_13 h1
  obtain ⟨M⟩ := exists_modDataE c.hyp.isElemAbelian_eOmegaZ
    (Hyp183.normalizer_eOmegaZ H D.T)
  have hgam : Gam183 V H (eOmegaZ H D.T) i g := ⟨hgi, fun hle =>
    hgK ((le_inf (inf_le_right : vInH V H g ≤ H) hle).trans c.hyp.inf_centralizer_eOmegaZ_le_kerMV)⟩
  have hab : IsElemAbelian 2 (vInH V H g) :=
    (E3.isElemAbelian_conjSubgroup c.hyp.setting.isElemAbelian g).mono inf_le_left
  obtain ⟨-, hA4⟩ := four_le_card_img M inf_le_right hab hA
  have hAH : M.img (vInH V H g) ≤ M.img H := M.img_mono inf_le_right
  have hA4' : 4 ≤ Nat.card ↥(M.img (vInH V H g)) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv) ▸ hA4
  have hKeq : H ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) = relPPrimeCore 3 H :=
    le_antisymm (hkerEq ▸ c.hyp.inf_centralizer_eOmegaZ_le_kerMV)
      (le_inf (hkerEq ▸ kerMV_le_self V H) (hkerEq ▸ hK))
  have hshape66 := exists_hyp66Shape hshape M hKeq
  obtain ⟨hAe, hq⟩ := x.img_elemAbelian_quadratic M hgam
  obtain ⟨-, hcard, K, U₁, U₂, hAK, cfg⟩ := asch6_6_lgl hO h66 hAH hshape66 hAe hA4' hq
  obtain ⟨w, hw, hw1, hwU⟩ := x.exists_vector_conj M hgam cfg hAK hcard
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := (not_concl181_iff.1 h1).1.2
  have hcop : Nat.Coprime 3
      (Nat.card ↥(H ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G))) :=
    (c.coprime_card_kerMV hsp).coprime_dvd_right
      (Subgroup.card_dvd_of_le c.hyp.inf_centralizer_eOmegaZ_le_kerMV)
  have hHle : H ≤ conjSubgroup D.M g :=
    le_conj_M_of_pglConfig c.hyp.setting c.hyp.ne_bot hsp M hcop hw.1 hw.2 hw1 cfg hwU
  exact x.false_of_le_conj M hgam hHle

end CFSG.LocalAnalysis.WeakClosure81

end
