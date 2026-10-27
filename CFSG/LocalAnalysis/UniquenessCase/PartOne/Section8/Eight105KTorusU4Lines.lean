module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.RankThree.PartTwo.Sec21.KS21U4TorusLines
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesU4
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesCore
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Late.GammaZero
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec13.Statements
public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec21.Item229Diagram
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools
public import CFSG.RankThree.PartTwo.Sec21.Membership
public import CFSG.RankThree.PartTwo.Sec21.SylowThree
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open Matrix CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.RankThree.PartOne.KFU (D8Mod d8Tor d8Comb_four d8Vec_mem_SU permGL_mem_SU)
open CFSG.RankThree.PartTwo.Sec21.U4Lines
  (torusD coe_torusD line_cases card_rootsOfUnity_three unitaryInvolution_rootsOfUnity
    weyl₁ weyl₂ conj_weyl₁ conj_weyl₂ shortSL mem_shortSL_of perfectResidual_short
    perfectResidual_conj nonempty_shortSL_mulEquiv_galois)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b : ℕ}

omit [Finite F] [CharP F 2] in
private theorem u4_entry_eq_of_mem_zpowers_torusD {ω : rootsOfUnity 3 F}
    {g : GL (Fin 4) F} (hg : g ∈ Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))) :
    ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 0 0 =
      ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 1 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [← map_zpow, coe_torusD, Prod.pow_def]
  simp

theorem u4_notationB_d8Tor_iff (hb : 0 < b) (hbe : Even b) (hF : Nat.card F = (2 ^ b) ^ 2)
    {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) {Y : Subgroup (GL (Fin 4) F)} :
    F08.NotationB8103 (SU (unitaryInvolution F 2 b) 4) (d8Tor 3 F 4) b Y ↔
      Y = zpowers (torusD ((ω, ω) : D8Mod 3 F)) ∨
        Y = zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)) := by
  have hμ := card_rootsOfUnity_three hbe hF
  have hd8 : d8Tor 3 F 4 ≤ SU (unitaryInvolution F 2 b) 4 := by
    rintro x ⟨v, rfl⟩
    exact d8Vec_mem_SU (Or.inl rfl) d8Comb_four (unitaryInvolution F 2 b)
      (unitaryInvolution_rootsOfUnity hbe) v
  have hw₁ : weyl₁ ∈ SU (unitaryInvolution F 2 b) 4 :=
    permGL_mem_SU (unitaryInvolution F 2 b) _ (by decide)
  have hw₂ : weyl₂ ∈ SU (unitaryInvolution F 2 b) 4 :=
    permGL_mem_SU (unitaryInvolution F 2 b) _ (by decide)
  have hB₁ : zpowers (torusD ((ω, 1) : D8Mod 3 F)) ≤ SU (unitaryInvolution F 2 b) 4 :=
    Subgroup.zpowers_le.mpr (hd8 ⟨((ω, 1) : D8Mod 3 F), rfl⟩)
  have hB₃ : zpowers (torusD ((ω, ω) : D8Mod 3 F)) ≤ SU (unitaryInvolution F 2 b) 4 :=
    Subgroup.zpowers_le.mpr (hd8 ⟨((ω, ω) : D8Mod 3 F), rfl⟩)
  unfold F08.NotationB8103
  constructor
  · rintro ⟨hcard, hYle, hL2⟩
    have hY' : F08.NotationB8103 (SU (unitaryInvolution F 2 b) 4)
        (SU (unitaryInvolution F 2 b) 4) b Y := ⟨hcard, hYle.trans hd8, hL2⟩
    rcases line_cases hμ hω hYle hcard with h1 | h2 | h3 | h4
    · exfalso
      rw [h1] at hY'
      exact u4_not_notationB_line hb hbe hF hω hY'
    · exfalso
      have hL₂ : zpowers (torusD ((1, ω) : D8Mod 3 F)) =
          (zpowers (torusD ((ω, 1) : D8Mod 3 F))).map
            (MulAut.conj weyl₁).toMonoidHom := by
        rw [MonoidHom.map_zpowers]
        congr 1
        exact (conj_weyl₁ ((ω, 1) : D8Mod 3 F)).symm
      rw [h2, hL₂] at hY'
      exact u4_not_notationB_line hb hbe hF hω
        ((notationB8103_map_conj_iff hw₁ hB₁).mp hY')
    · exact Or.inl h3
    · exact Or.inr h4
  · rintro (rfl | rfl)
    · have h := u4_notationB hb hbe hF hω
      exact ⟨h.1, Subgroup.zpowers_le.mpr ⟨((ω, ω) : D8Mod 3 F), rfl⟩, h.2.2⟩
    · have h := u4_notationB hb hbe hF hω
      have hL₄ : zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)) =
          (zpowers (torusD ((ω, ω) : D8Mod 3 F))).map
            (MulAut.conj weyl₂).toMonoidHom := by
        rw [MonoidHom.map_zpowers]
        congr 1
        exact (conj_weyl₂ ((ω, ω) : D8Mod 3 F)).symm
      have h' : F08.NotationB8103 (SU (unitaryInvolution F 2 b) 4)
          (SU (unitaryInvolution F 2 b) 4) b
            (zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) := by
        rw [hL₄]
        exact (notationB8103_map_conj_iff hw₂ hB₃).mpr h
      exact ⟨h'.1, Subgroup.zpowers_le.mpr ⟨((ω, ω⁻¹) : D8Mod 3 F), rfl⟩, h'.2.2⟩

omit [Finite F] [CharP F 2] in
theorem u4_line_four_ne_three {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) :
    zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)) ≠ zpowers (torusD ((ω, ω) : D8Mod 3 F)) := by
  intro h
  have hmem : torusD ((ω, ω⁻¹) : D8Mod 3 F) ∈
      Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F)) := by
    rw [← h]
    exact Subgroup.mem_zpowers _
  have h00 : ((ω : Fˣ) : F) = (((ω⁻¹ : rootsOfUnity 3 F) : Fˣ) : F) := by
    simpa [coe_torusD] using u4_entry_eq_of_mem_zpowers_torusD hmem
  have hne : ω ≠ ω⁻¹ := by
    intro heq
    apply hω
    have h2 : ω ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [heq]
      exact mul_inv_cancel ω
    have h3 : ω ^ 3 = ω := by
      rw [pow_succ, h2, one_mul]
    have hω3 : ω ^ 3 = 1 := by
      apply Subtype.ext
      simpa using (mem_rootsOfUnity 3 (ω : Fˣ)).mp ω.2
    rwa [h3] at hω3
  exact hne (Subtype.ext (Units.ext h00))

private theorem u4_torusD_four_mem_shortSL (hbe : Even b) {ω : rootsOfUnity 3 F} :
    torusD ((ω, ω⁻¹) : D8Mod 3 F) ∈ shortSL (unitaryInvolution F 2 b) := by
  set a : F := ((ω : Fˣ) : F) with ha
  have ht : ((torusD ((ω, ω⁻¹) : D8Mod 3 F) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = diagonal ![a, a⁻¹, a, a⁻¹] := by
    rw [coe_torusD]
    congr 1
    funext i
    fin_cases i <;> simp [ha]
  have hmemSU : torusD ((ω, ω⁻¹) : D8Mod 3 F) ∈ SU (unitaryInvolution F 2 b) 4 :=
    d8Vec_mem_SU (Or.inl rfl) d8Comb_four _ (unitaryInvolution_rootsOfUnity hbe) _
  refine mem_shortSL_of (unitaryInvolution F 2 b) hmemSU ?_ ?_
  · rw [ht]
    exact ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
  · rw [ht]
    simp [ha]

private theorem u4_perfectResidual_line_three (hb : 0 < b) (hbe : Even b)
    (hF : Nat.card F = (2 ^ b) ^ 2) {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) :
    inSubgroup perfectResidual (SU (unitaryInvolution F 2 b) 4 ⊓ Subgroup.centralizer
      (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F)) : Set (GL (Fin 4) F))) =
      shortSL (unitaryInvolution F 2 b) := by
  set σ : F ≃+* F := unitaryInvolution F 2 b with hσdef
  have hb2 : 2 ≤ b := by obtain ⟨k, hk⟩ := hbe; omega
  have hσσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  set a : F := ((ω : Fˣ) : F) with ha
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 3 (ω : Fˣ)).mp ω.2, Units.val_one]
  have ha1 : a ≠ 1 := fun h => hω (Subtype.ext (Units.ext h))
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha3; norm_num at ha3
  have hainv : a ≠ a⁻¹ := by
    intro h
    apply ha1
    have h2 : a * a = 1 := by
      calc a * a = a * a⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ ha0
    calc a = a ^ 3 * a⁻¹ * a⁻¹ := by field_simp
      _ = 1 := by rw [ha3, one_mul, ← h, h2]
  have ht₃ : ((torusD ((ω, ω) : D8Mod 3 F) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = diagonal ![a, a, a⁻¹, a⁻¹] := by
    rw [coe_torusD]
    simp [ha]
  obtain ⟨eS⟩ := nonempty_shortSL_mulEquiv_galois σ hb hF
  have hperfS : ⁅shortSL σ, shortSL σ⁆ = shortSL σ :=
    Subgroup.isPerfect_iff.mp
      (CFSG.RankThree.PartTwo.Sec21.isPerfect_of_mulEquiv_projSL (by omega) eS)
  exact perfectResidual_short σ hσσ ht₃ hainv hperfS

theorem u4_line_le_kOf (hb : 0 < b) (hbe : Even b) (hF : Nat.card F = (2 ^ b) ^ 2)
    {ω : rootsOfUnity 3 F} (hω : ω ≠ 1) :
    zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)) ≤
        F08.KOf8103 (SU (unitaryInvolution F 2 b) 4) (zpowers (torusD ((ω, ω) : D8Mod 3 F))) ∧
      zpowers (torusD ((ω, ω) : D8Mod 3 F)) ≤
        F08.KOf8103 (SU (unitaryInvolution F 2 b) 4)
          (zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) := by
  set σ : F ≃+* F := unitaryInvolution F 2 b with hσdef
  have hS₃ : inSubgroup perfectResidual (SU σ 4 ⊓ Subgroup.centralizer
      (Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F)) : Set (GL (Fin 4) F))) =
      shortSL σ :=
    u4_perfectResidual_line_three hb hbe hF hω
  have hS₃' : F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω) : D8Mod 3 F))) =
      shortSL σ := hS₃
  have hmem₄ : torusD ((ω, ω⁻¹) : D8Mod 3 F) ∈ shortSL σ :=
    u4_torusD_four_mem_shortSL hbe
  have hw₂ : weyl₂ ∈ SU σ 4 := permGL_mem_SU σ _ (by decide)
  have hL₄ : zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F)) =
      (zpowers (torusD ((ω, ω) : D8Mod 3 F))).map
        (MulAut.conj weyl₂).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    congr 1
    exact (conj_weyl₂ ((ω, ω) : D8Mod 3 F)).symm
  have hK₄ : F08.KOf8103 (SU σ 4) (zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))) =
      (shortSL σ).map (MulAut.conj weyl₂).toMonoidHom := by
    rw [hL₄]
    change inSubgroup perfectResidual
      (SU σ 4 ⊓ Subgroup.centralizer
        ((Subgroup.zpowers (torusD ((ω, ω) : D8Mod 3 F))).map
          (MulAut.conj weyl₂).toMonoidHom : Set (GL (Fin 4) F))) =
      (shortSL σ).map (MulAut.conj weyl₂).toMonoidHom
    rw [perfectResidual_conj hw₂, hS₃]
  have hL₃ : zpowers (torusD ((ω, ω) : D8Mod 3 F)) =
      (zpowers (torusD ((ω, ω⁻¹) : D8Mod 3 F))).map
        (MulAut.conj weyl₂).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    congr 1
    simpa using (conj_weyl₂ ((ω, ω⁻¹) : D8Mod 3 F)).symm
  refine ⟨?_, ?_⟩
  · rw [hS₃']; exact Subgroup.zpowers_le.mpr hmem₄
  · rw [hK₄, hL₃]; exact Subgroup.map_mono (Subgroup.zpowers_le.mpr hmem₄)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
