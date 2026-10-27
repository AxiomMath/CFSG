module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASCtx
public import CFSG.LocalAnalysis.WeakClosure81.W18ASTail
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineAlt
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineBar
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCtx
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineShape
public import CFSG.LocalAnalysis.WeakClosure81.W18PackFix
public import CFSG.LocalAnalysis.WeakClosure81.W18PackRank

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.WeakClosure81.SevenK

@[expose] def Tail189TwoNoSection : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S : Subgroup X), SevenElevenSmallAlt X S →
    ∀ (T : Type) [Group T], Socle185Shape T → ¬ CFSG.Quasithin.E1.IsCompositionFactor X T

section Reduction

variable {G : Type} [Group G] [Finite G]


theorem tail189Two_AS_of_inputs (hCore : OddTranspositionCoreInputSC)
    (hList : OddTranspListBundle)
    (h772 : ∀ (X : Type) [Group X] [Finite X], SevenSevenTwoInput X)
    (hIn : OrthReflParabolic) (hGap : Tail189TwoNoSection) : Tail189Two_AS G := by
  intro h162 h172 h5_4 h5_11 h5_12 h5_13 D V₀ V H i c h1 g hgT hgK hgi hA
  have x : Ctx188 D V₀ V H i 2 := c.ctx188_two_AS h162 h5_11 h5_13 h1
  obtain ⟨-, hkerEq, hshape⟩ := c.exists_shape185_AS h172 h5_12 h5_11 h5_13 h1
  obtain ⟨M⟩ := exists_modDataE c.hyp.isElemAbelian_eOmegaZ (Hyp183.normalizer_eOmegaZ H D.T)
  obtain ⟨hgam, a₁, ha₁D, ha₁K, himg, hord⟩ := x.exists_involution_img M hgK hgi hA
  have ha₁mem : M.ρ a₁ ∈ M.img H := M.mem_img.2 ⟨a₁, a₁.2, rfl⟩
  let a : ↥(M.img H) := ⟨M.ρ a₁, ha₁mem⟩
  have ha2 : orderOf a = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hord
  have hΓ : Subgroup.zpowers (a : LGL 2 M.W) ∈ x.packFamily M := ⟨g, hgam, himg.symm⟩
  have h131 := x.assumption131 M
  have hrank : ∀ A ∈ x.packFamily M, mRank A ≤ x.iStar := fun A hA => x.mRank_le_iStar M hA
  have hVAle : ∀ A ∈ x.packFamily M, x.packSpace M A ≤ fixSub A :=
    fun A _ => x.packSpace_le_fixSub M A
  have hG2 : pCoreOf 2 (M.img H) = ⊥ := x.pCoreOf_img_eq_bot M
  have hker : H ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G) ≤ relPPrimeCore 3 H :=
    hkerEq ▸ c.hyp.inf_centralizer_eOmegaZ_le_kerMV
  obtain ⟨Kk, F, S, _, φ, hsoc, hφs, hφk, hS, hKk⟩ := M.exists_simpleSocleMod hker hshape
  have haK : a ∉ Kk := fun hmem => ha₁K (hkerEq ▸ (hKk a₁ a rfl).1 hmem)
  have hclass : ∀ y : ↥(M.img H),
      ∃ n ∈ Subgroup.normalClosure ({a} : Set ↥(M.img H)), y * a * y⁻¹ = n * a * n⁻¹ :=
    hsoc.exists_conj_normalClosure haK fun c' d' hc' hd' =>
      commute_or_exists_conj_of_isConj h131 hrank hVAle hΓ ha2 hc' hd'
  have h711 := hyp711_UAOf_zpowers h131 hrank hVAle hΓ hclass
  obtain ⟨φ', hφ'bar, hφ'S, -⟩ :=
    exists_isBarMap_kSub_UAOf_zpowers h131 hrank hVAle hΓ ha2 hG2 rfl rfl
  obtain ⟨-, halt⟩ := seven_eleven_small_alt hCore hList (h772 _) hIn h711 hφ'bar hφ'S
  have hN : (Subgroup.normalClosure ({a} : Set ↥(M.img H))).Normal :=
    Subgroup.normalClosure_normal
  have hnot : ¬ Subgroup.normalClosure ({a} : Set ↥(M.img H)) ≤ Kk := fun h =>
    haK (h (Subgroup.subset_normalClosure rfl))
  have hcf := isCompositionFactor_of_simpleSocleMod hsoc hS φ hφs hφk hN hnot
  exact hGap _ _ halt S hS hcf

end Reduction

end CFSG.LocalAnalysis.WeakClosure81

end
