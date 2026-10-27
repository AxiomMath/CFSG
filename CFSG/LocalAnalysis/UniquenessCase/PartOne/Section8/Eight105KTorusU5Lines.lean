module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.RankThree.PartOne.KF.R6LeviA
public import CFSG.RankThree.PartOne.KF.R56Final
import CFSG.GroupTheory.ConjTransport
import CFSG.RankThree.PartTwo.Sec21.KS21U4TorusLines
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesCore
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KTypesU5
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.KF.R7Final
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.KFOUT3.KtyD8
public import CFSG.RankThree.PartOne.KFOUT3.KtyWCtx
public import CFSG.RankThree.PartOne.S12.InputsKF2
public import CFSG.RankThree.PartOne.S12.Sec1322Inputs
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate43
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.GroupTheory.ABGLocalTools.Constraint
import CFSG.GroupTheory.BaerSuzuki
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LieType.Chevalley.LangRootArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.RankThree.Asc83Table.Automizer
import CFSG.RankThree.PartTwo.Late.GammaZero
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.RankThree.PartTwo.Sec13.Statements
import CFSG.RankThree.PartTwo.Sec18.Notation
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartTwo.Sec21.Item229Diagram
import CFSG.RankThree.PartTwo.Sec21.Item23Tools
import CFSG.RankThree.PartTwo.Sec21.Membership
import CFSG.RankThree.PartTwo.Sec21.SylowThree
import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open Matrix CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.RankThree.PartOne (suQ)
open CFSG.RankThree.PartOne.KFU (torus6 diagU dvec5 mem_torus6_iff torus6_pow_eq_one
  diagU_pow diagU_one diagU_inv diagU_val diagU_injective bA6 b6 coe_bA6 coe_b6 b6_mem_torus6
  permGL permGL_mem_SU permGL_conj_diagU perfectResidual_centralizer_b6 suBlock6 suBlock6_injective
  rho6 coe_rho6 diag2Hom)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
private theorem permGL_swap01_conj_dvec5 (a b : Kˣ) :
    permGL (Equiv.swap (0 : Fin 5) 1 * Equiv.swap (3 : Fin 5) 4) * diagU (dvec5 a b) *
      (permGL (Equiv.swap (0 : Fin 5) 1 * Equiv.swap (3 : Fin 5) 4))⁻¹ =
      diagU (dvec5 b a) := by
  have hsym : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap (3 : Fin 5) 4).symm =
      Equiv.swap (0 : Fin 5) 1 * Equiv.swap (3 : Fin 5) 4 := by decide
  rw [permGL_conj_diagU, hsym]
  congr 1
  funext i
  fin_cases i <;> simp [dvec5, Equiv.swap_apply_def]

private theorem eq_inv_of_diagU_dvec5_inv {a b : Kˣ}
    {x y : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx : (x : GL (Fin 5) K) = diagU (dvec5 a⁻¹ b⁻¹))
    (hy : (y : GL (Fin 5) K) = diagU (dvec5 a b)) : x = y⁻¹ := by
  apply Subtype.ext
  rw [hx, Subgroup.coe_inv, hy, ← diagU_inv]
  congr 1
  funext i
  fin_cases i <;> simp [dvec5]

private theorem not_notationB_of_conj_bA6 (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1)
    {g x : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx : g * bA6 (unitaryInvolution K 2 2) ζ hζ * g⁻¹ = x) :
    ¬ F08.NotationB8103 (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊤ 2
      (Subgroup.zpowers (suQ 5 hK x)) := by
  intro hB
  have hmap : Subgroup.zpowers (suQ 5 hK x) =
      (Subgroup.zpowers (suQ 5 hK (bA6 (unitaryInvolution K 2 2) ζ hζ))).map
        (MulAut.conj (suQ 5 hK g)).toMonoidHom := by
    rw [← hx, map_mul, map_mul, map_inv, CFSG.GroupTheory.map_conj_zpowers]
  have hB' : F08.NotationB8103 ⊤ ⊤ 2
      ((Subgroup.zpowers (suQ 5 hK (bA6 (unitaryInvolution K 2 2) ζ hζ))).map
        (MulAut.conj (suQ 5 hK g)).toMonoidHom) := hmap ▸ hB
  have hB0 : F08.NotationB8103 ⊤ ⊤ 2
      (Subgroup.zpowers (suQ 5 hK (bA6 (unitaryInvolution K 2 2) ζ hζ))) :=
    (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes.notationB8103_map_conj_iff
      (L := ⊤) (B := Subgroup.zpowers (suQ 5 hK (bA6 (unitaryInvolution K 2 2) ζ hζ)))
      (g := suQ 5 hK g) (Subgroup.mem_top _) le_top (n := 2)).mp hB'
  exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes.u5_not_notationB_bA6
    hK hζ h1 h3 hB0

private theorem exists_torus6_generator (hK : Nat.card K = (2 ^ 2) ^ 2)
    {Y : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))}
    (hYle : Y ≤ (torus6 (unitaryInvolution K 2 2) 3).map (suQ 5 hK))
    (hYcard : Nat.card Y = 3) :
    ∃ x ∈ torus6 (unitaryInvolution K 2 2) 3, x ^ 3 = 1 ∧
      Y = Subgroup.zpowers (suQ 5 hK x) := by
  have hq : CFSG.RankThree.PartOne.KFU.IsCentralPQuot 3 (suQ 5 hK) :=
    CFSG.RankThree.PartOne.isCentralPQuot_suQ Nat.prime_three (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hK
  obtain ⟨y, hYy, hyord⟩ :=
    CFSG.GroupTheory.exists_zpowers_eq_of_card_eq_prime Nat.prime_three hYcard
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hyord
    norm_num at hyord
  have hy3 : y ^ 3 = 1 := by
    rw [← hyord]
    exact pow_orderOf_eq_one y
  have hyY : y ∈ Y := by
    rw [hYy]
    exact Subgroup.mem_zpowers y
  obtain ⟨t, htT, hty⟩ := Subgroup.mem_map.mp (hYle hyY)
  obtain ⟨x, hxmap, hx3⟩ := hq.exists_lift hy3
  have htx : t = x := hq.eq_of_map_eq (torus6_pow_eq_one htT) hx3 (by rw [hty, hxmap])
  have hxT : x ∈ torus6 (unitaryInvolution K 2 2) 3 := by
    rw [← htx]
    exact htT
  exact ⟨x, hxT, hx3, by rw [hYy, ← hxmap]⟩

private theorem line_case_a_one (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1)
    {x₃ x₄ : ↥(SU (unitaryInvolution K 2 2) 5)}
    {x : ↥(SU (unitaryInvolution K 2 2) 5)} {a b : Kˣ} (hx1 : suQ 5 hK x ≠ 1)
    (ha : a = 1) (hb : b = 1 ∨ b = ζ ∨ b = ζ⁻¹)
    (hab : (x : GL (Fin 5) K) = diagU (dvec5 a b)) :
    Subgroup.zpowers (suQ 5 hK x) = Subgroup.zpowers (suQ 5 hK x₃) ∨
      Subgroup.zpowers (suQ 5 hK x) = Subgroup.zpowers (suQ 5 hK x₄) ∨
      ¬ F08.NotationB8103 (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊤ 2
        (Subgroup.zpowers (suQ 5 hK x)) := by
  rw [ha] at hab
  rcases hb with hb | hb | hb
  · rw [hb] at hab
    exfalso
    have hx1eq : x = 1 := by
      apply Subtype.ext
      rw [hab, Subgroup.coe_one]
      apply Units.ext
      rw [diagU_val]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [dvec5]
    exact hx1 (by rw [hx1eq, map_one])
  · rw [hb] at hab
    exact Or.inr (Or.inr (by
      have hxeq : x = bA6 (unitaryInvolution K 2 2) ζ hζ :=
        Subtype.ext (by rw [hab, coe_bA6])
      rw [hxeq]
      exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes.u5_not_notationB_bA6
        hK hζ h1 h3))
  · rw [hb] at hab
    exact Or.inr (Or.inr (by
      have hxeq : x = (bA6 (unitaryInvolution K 2 2) ζ hζ)⁻¹ :=
        eq_inv_of_diagU_dvec5_inv (a := 1) (b := ζ) hab
          (coe_bA6 (unitaryInvolution K 2 2) ζ hζ)
      rw [hxeq, map_inv, Subgroup.zpowers_inv]
      exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes.u5_not_notationB_bA6
        hK hζ h1 h3))

private theorem line_case_a_ne_one (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1)
    {x₃ x₄ : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ))
    (hx₄ : (x₄ : GL (Fin 5) K) = diagU (dvec5 ζ ζ⁻¹))
    {x : ↥(SU (unitaryInvolution K 2 2) 5)} {a b : Kˣ}
    (ha : a = ζ ∨ a = ζ⁻¹) (hb : b = 1 ∨ b = ζ ∨ b = ζ⁻¹)
    (hab : (x : GL (Fin 5) K) = diagU (dvec5 a b)) :
    Subgroup.zpowers (suQ 5 hK x) = Subgroup.zpowers (suQ 5 hK x₃) ∨
      Subgroup.zpowers (suQ 5 hK x) = Subgroup.zpowers (suQ 5 hK x₄) ∨
      ¬ F08.NotationB8103 (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊤ 2
        (Subgroup.zpowers (suQ 5 hK x)) := by
  let w₁ : ↥(SU (unitaryInvolution K 2 2) 5) :=
    ⟨permGL (Equiv.swap (0 : Fin 5) 1 * Equiv.swap (3 : Fin 5) 4),
      permGL_mem_SU (unitaryInvolution K 2 2) _ (by decide)⟩
  rcases ha with ha | ha <;> rcases hb with hb | hb | hb
  · rw [ha, hb] at hab
    exact Or.inr (Or.inr (by
      have hconj : w₁ * bA6 (unitaryInvolution K 2 2) ζ hζ * w₁⁻¹ = x := by
        apply Subtype.ext
        change (permGL (Equiv.swap (0 : Fin 5) 1 * Equiv.swap (3 : Fin 5) 4) *
          diagU (dvec5 1 ζ) *
          (permGL (Equiv.swap (0 : Fin 5) 1 * Equiv.swap (3 : Fin 5) 4))⁻¹ :
            GL (Fin 5) K) = (x : GL (Fin 5) K)
        rw [permGL_swap01_conj_dvec5 1 ζ, hab]
      exact not_notationB_of_conj_bA6 hK hζ h1 h3 hconj))
  · rw [ha, hb] at hab
    exact Or.inl (by
      have hxeq : x = x₃ := Subtype.ext (by rw [hab, hx₃])
      rw [hxeq])
  · rw [ha, hb] at hab
    exact Or.inr (Or.inl (by
      have hxeq : x = x₄ := Subtype.ext (by rw [hab, hx₄])
      rw [hxeq]))
  · rw [ha, hb] at hab
    exact Or.inr (Or.inr (by
      have hy : ((w₁ * bA6 (unitaryInvolution K 2 2) ζ hζ * w₁⁻¹ :
          ↥(SU (unitaryInvolution K 2 2) 5)) : GL (Fin 5) K) = diagU (dvec5 ζ 1) := by
        change (permGL (Equiv.swap (0 : Fin 5) 1 * Equiv.swap (3 : Fin 5) 4) *
          diagU (dvec5 1 ζ) *
          (permGL (Equiv.swap (0 : Fin 5) 1 * Equiv.swap (3 : Fin 5) 4))⁻¹ :
            GL (Fin 5) K) = diagU (dvec5 ζ 1)
        rw [permGL_swap01_conj_dvec5 1 ζ]
      have hxeq : x = (w₁ * bA6 (unitaryInvolution K 2 2) ζ hζ * w₁⁻¹)⁻¹ :=
        eq_inv_of_diagU_dvec5_inv (a := ζ) (b := 1) hab hy
      have hzp : Subgroup.zpowers (suQ 5 hK x) =
          Subgroup.zpowers (suQ 5 hK (w₁ * bA6 (unitaryInvolution K 2 2) ζ hζ * w₁⁻¹)) := by
        rw [hxeq, map_inv, Subgroup.zpowers_inv]
      rw [hzp]
      exact not_notationB_of_conj_bA6 hK hζ h1 h3 rfl))
  · rw [ha, hb] at hab
    exact Or.inr (Or.inl (by
      have hxeq : x = (x₄)⁻¹ := eq_inv_of_diagU_dvec5_inv (a := ζ) (b := ζ⁻¹) hab hx₄
      rw [hxeq, map_inv, Subgroup.zpowers_inv]))
  · rw [ha, hb] at hab
    exact Or.inl (by
      have hxeq : x = (x₃)⁻¹ := eq_inv_of_diagU_dvec5_inv (a := ζ) (b := ζ) hab hx₃
      rw [hxeq, map_inv, Subgroup.zpowers_inv])

private theorem line_cases_torus6 (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (hζ : unitaryInvolution K 2 2 (ζ : K) = ζ) (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1)
    {x₃ x₄ : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ))
    (hx₄ : (x₄ : GL (Fin 5) K) = diagU (dvec5 ζ ζ⁻¹))
    {x : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hxT : x ∈ torus6 (unitaryInvolution K 2 2) 3) (hx1 : suQ 5 hK x ≠ 1) :
    Subgroup.zpowers (suQ 5 hK x) = Subgroup.zpowers (suQ 5 hK x₃) ∨
      Subgroup.zpowers (suQ 5 hK x) = Subgroup.zpowers (suQ 5 hK x₄) ∨
      ¬ F08.NotationB8103 (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊤ 2
        (Subgroup.zpowers (suQ 5 hK x)) := by
  obtain ⟨a, b, ha, hb, hab⟩ := mem_torus6_iff.1 hxT
  have hμ : Nat.card (rootsOfUnity 3 K) = 3 :=
    CFSG.RankThree.PartTwo.Sec21.U4Lines.card_rootsOfUnity_three (b := 2) even_two hK
  have hω : (⟨ζ, (mem_rootsOfUnity 3 ζ).mpr h3⟩ : rootsOfUnity 3 K) ≠ 1 := by
    intro h
    exact h1 (congrArg Subtype.val h)
  have hunit : ∀ u : Kˣ, u ^ 3 = 1 → u = 1 ∨ u = ζ ∨ u = ζ⁻¹ := by
    intro u hu
    rcases CFSG.RankThree.PartTwo.Sec21.U4Lines.eq_one_or_eq_or_eq_inv hμ hω
      (⟨u, (mem_rootsOfUnity 3 u).mpr hu⟩ : rootsOfUnity 3 K) with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (by simpa using congrArg Subtype.val h))
  rcases hunit a ha with ha | ha | ha
  · exact line_case_a_one hK hζ h1 h3 hx1 ha (hunit b hb) hab
  · exact line_case_a_ne_one hK hζ h1 h3 hx₃ hx₄ (Or.inl ha) (hunit b hb) hab
  · exact line_case_a_ne_one hK hζ h1 h3 hx₃ hx₄ (Or.inr ha) (hunit b hb) hab

omit [Finite K] [CharP K 2] in
private theorem permGL_swap13_conj_dvec5 (a b : Kˣ) :
    permGL (Equiv.swap (1 : Fin 5) 3) * diagU (dvec5 a b) *
      (permGL (Equiv.swap (1 : Fin 5) 3))⁻¹ = diagU (dvec5 a b⁻¹) := by
  rw [permGL_conj_diagU]
  congr 1
  funext i
  fin_cases i <;> simp [dvec5, Equiv.swap_apply_def]

private theorem notationB_torus_forward (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ} (h1 : ζ ≠ 1)
    (h3 : ζ ^ 3 = 1) {x₃ x₄ : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ))
    (hx₄ : (x₄ : GL (Fin 5) K) = diagU (dvec5 ζ ζ⁻¹))
    {Y : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))}
    (hY : F08.NotationB8103 (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K)))
      ((torus6 (unitaryInvolution K 2 2) 3).map (suQ 5 hK)) 2 Y) :
    Y = Subgroup.zpowers (suQ 5 hK x₃) ∨ Y = Subgroup.zpowers (suQ 5 hK x₄) := by
  obtain ⟨hYcard, hYle, hYL2⟩ := hY
  obtain ⟨x, hxT, hx3, hYx⟩ := exists_torus6_generator hK hYle hYcard
  have hx1 : suQ 5 hK x ≠ 1 := by
    intro h
    rw [h, Subgroup.zpowers_one_eq_bot] at hYx
    rw [hYx, Subgroup.card_bot] at hYcard
    norm_num at hYcard
  have hζ : unitaryInvolution K 2 2 (ζ : K) = ζ := by
    have h := CFSG.RankThree.PartTwo.Sec21.U4Lines.unitaryInvolution_rootsOfUnity
      (F := K) (b := 2) even_two (⟨ζ, (mem_rootsOfUnity 3 ζ).mpr h3⟩ : rootsOfUnity 3 K)
    simpa using h
  rcases line_cases_torus6 hK hζ h1 h3 hx₃ hx₄ hxT hx1 with h | h | h
  · exact Or.inl (hYx.trans h)
  · exact Or.inr (hYx.trans h)
  · have hBtop : F08.NotationB8103 (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊤ 2
        (Subgroup.zpowers (suQ 5 hK x)) := by
      refine ⟨?_, le_top, ?_⟩
      · rw [← hYx]
        exact hYcard
      · rw [hYx] at hYL2
        exact hYL2
    exact absurd hBtop h

private theorem notationB_torus_three (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ} (h1 : ζ ≠ 1)
    (h3 : ζ ^ 3 = 1) {x₃ : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ)) :
    F08.NotationB8103 (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K)))
      ((torus6 (unitaryInvolution K 2 2) 3).map (suQ 5 hK)) 2
      (Subgroup.zpowers (suQ 5 hK x₃)) := by
  have hζ : unitaryInvolution K 2 2 (ζ : K) = ζ := by
    have h := CFSG.RankThree.PartTwo.Sec21.U4Lines.unitaryInvolution_rootsOfUnity
      (F := K) (b := 2) even_two (⟨ζ, (mem_rootsOfUnity 3 ζ).mpr h3⟩ : rootsOfUnity 3 K)
    simpa using h
  have hx3T : x₃ ∈ torus6 (unitaryInvolution K 2 2) 3 :=
    mem_torus6_iff.mpr ⟨ζ, ζ, h3, h3, hx₃⟩
  have hx3b : x₃ = b6 (unitaryInvolution K 2 2) ζ hζ := Subtype.ext (by rw [hx₃, coe_b6])
  have hB : F08.NotationB8103 (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊤ 2
      (Subgroup.zpowers (suQ 5 hK x₃)) := by
    rw [hx3b]
    exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes.u5_notationB hK hζ h1 h3
  refine ⟨hB.1, ?_, hB.2.2⟩
  exact Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem (suQ 5 hK) hx3T)

private theorem notationB_torus_four (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ} (h1 : ζ ≠ 1)
    (h3 : ζ ^ 3 = 1) {x₃ x₄ : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ))
    (hx₄ : (x₄ : GL (Fin 5) K) = diagU (dvec5 ζ ζ⁻¹)) :
    F08.NotationB8103 (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K)))
      ((torus6 (unitaryInvolution K 2 2) 3).map (suQ 5 hK)) 2
      (Subgroup.zpowers (suQ 5 hK x₄)) := by
  have hthree := notationB_torus_three hK h1 h3 hx₃
  let w : ↥(SU (unitaryInvolution K 2 2) 5) :=
    ⟨permGL (Equiv.swap (1 : Fin 5) 3), permGL_mem_SU (unitaryInvolution K 2 2) _ (by decide)⟩
  have hw : w * x₃ * w⁻¹ = x₄ := by
    apply Subtype.ext
    change (permGL (Equiv.swap (1 : Fin 5) 3) * (x₃ : GL (Fin 5) K) *
      (permGL (Equiv.swap (1 : Fin 5) 3))⁻¹ : GL (Fin 5) K) = (x₄ : GL (Fin 5) K)
    rw [hx₃, hx₄, permGL_swap13_conj_dvec5]
  have hℓ : Subgroup.zpowers (suQ 5 hK x₄) =
      (Subgroup.zpowers (suQ 5 hK x₃)).map (MulAut.conj (suQ 5 hK w)).toMonoidHom := by
    rw [← hw, map_mul, map_mul, map_inv, CFSG.GroupTheory.map_conj_zpowers]
  have hBtop : F08.NotationB8103 (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊤ 2
      (Subgroup.zpowers (suQ 5 hK x₄)) := by
    rw [hℓ]
    exact (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KTypes.notationB8103_map_conj_iff
      (L := ⊤) (B := Subgroup.zpowers (suQ 5 hK x₃)) (g := suQ 5 hK w)
      (Subgroup.mem_top _) le_top (n := 2)).mpr ⟨hthree.1, le_top, hthree.2.2⟩
  have hx4T : x₄ ∈ torus6 (unitaryInvolution K 2 2) 3 :=
    mem_torus6_iff.mpr ⟨ζ, ζ⁻¹, h3, by rw [inv_pow, h3, inv_one], hx₄⟩
  refine ⟨hBtop.1, ?_, hBtop.2.2⟩
  exact Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem (suQ 5 hK) hx4T)

theorem u5_notationB_torus_iff (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ} (h1 : ζ ≠ 1)
    (h3 : ζ ^ 3 = 1) {x₃ x₄ : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ))
    (hx₄ : (x₄ : GL (Fin 5) K) = diagU (dvec5 ζ ζ⁻¹))
    {Y : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))} :
    F08.NotationB8103 ⊤ ((torus6 (unitaryInvolution K 2 2) 3).map (suQ 5 hK)) 2 Y ↔
      Y = zpowers (suQ 5 hK x₃) ∨ Y = zpowers (suQ 5 hK x₄) := by
  constructor
  · exact notationB_torus_forward hK h1 h3 hx₃ hx₄
  · rintro (rfl | rfl)
    · exact notationB_torus_three hK h1 h3 hx₃
    · exact notationB_torus_four hK h1 h3 hx₃ hx₄

private theorem not_mem_zpowers_x3_x4 {ζ : Kˣ} (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1)
    {x₃ x₄ : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ))
    (hx₄ : (x₄ : GL (Fin 5) K) = diagU (dvec5 ζ ζ⁻¹)) :
    x₄ ∉ zpowers x₃ := by
  have hx3T : x₃ ∈ torus6 (unitaryInvolution K 2 2) 3 :=
    mem_torus6_iff.mpr ⟨ζ, ζ, h3, h3, hx₃⟩
  have hx4T : x₄ ∈ torus6 (unitaryInvolution K 2 2) 3 :=
    mem_torus6_iff.mpr ⟨ζ, ζ⁻¹, h3, by rw [inv_pow, h3, inv_one], hx₄⟩
  have hx33 : x₃ ^ 3 = 1 := torus6_pow_eq_one hx3T
  have hζinv : ζ ≠ ζ⁻¹ := by
    intro h
    have h2 : ζ ^ 2 = 1 := by
      calc ζ ^ 2 = ζ * ζ := pow_two ζ
        _ = ζ * ζ⁻¹ := congrArg (fun u : Kˣ => ζ * u) h
        _ = 1 := mul_inv_cancel ζ
    apply h1
    calc ζ = ζ ^ 3 * (ζ ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2, inv_one, one_mul]
  have hx3pow : ∀ n : ℕ,
      ((x₃ ^ n : ↥(SU (unitaryInvolution K 2 2) 5)) : GL (Fin 5) K) =
        diagU (dvec5 ζ ζ ^ n) := by
    intro n
    rw [Subgroup.coe_pow, hx₃, diagU_pow]
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hz3int : x₃ ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hx33]
  rw [zpow_eq_zpow_emod k hz3int] at hk
  have hlt : k % (3 : ℤ) < 3 := Int.emod_lt_of_pos k (by norm_num)
  have hge : 0 ≤ k % (3 : ℤ) := Int.emod_nonneg k (by norm_num)
  have hk3 : k % (3 : ℤ) = 0 ∨ k % (3 : ℤ) = 1 ∨ k % (3 : ℤ) = 2 := by omega
  rcases hk3 with h0 | h1k | h2
  · rw [h0, zpow_zero] at hk
    have hgl : (x₄ : GL (Fin 5) K) = 1 :=
      (congrArg (fun g : ↥(SU (unitaryInvolution K 2 2) 5) =>
        (g : GL (Fin 5) K)) hk).symm
    have hentry : (ζ : K) = 1 := by
      have := congrFun (congrFun (congrArg (fun g : GL (Fin 5) K =>
        ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) hgl) 0) 0
      simpa [hx₄, diagU_val, dvec5] using this
    exact h1 (Units.ext hentry)
  · rw [h1k, zpow_one] at hk
    have hgl : (x₃ : GL (Fin 5) K) = (x₄ : GL (Fin 5) K) :=
      congrArg (fun g : ↥(SU (unitaryInvolution K 2 2) 5) => (g : GL (Fin 5) K)) hk
    rw [hx₃, hx₄] at hgl
    have hentry := congrFun (diagU_injective hgl) 1
    simp [dvec5] at hentry
    exact hζinv hentry
  · rw [h2, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast] at hk
    have hgl : ((x₃ ^ 2 : ↥(SU (unitaryInvolution K 2 2) 5)) : GL (Fin 5) K) =
        (x₄ : GL (Fin 5) K) :=
      congrArg (fun g : ↥(SU (unitaryInvolution K 2 2) 5) => (g : GL (Fin 5) K)) hk
    rw [hx3pow 2, hx₄] at hgl
    have hentry := congrFun (diagU_injective hgl) 0
    simp [dvec5, pow_two] at hentry
    have hζeq : ζ = 1 := by
      have h := congrArg (fun u : Kˣ => u * ζ⁻¹) hentry
      simpa [pow_two, mul_assoc] using h
    exact h1 hζeq

theorem u5_line_four_ne_three (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ} (h1 : ζ ≠ 1)
    (h3 : ζ ^ 3 = 1) {x₃ x₄ : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ))
    (hx₄ : (x₄ : GL (Fin 5) K) = diagU (dvec5 ζ ζ⁻¹)) :
    zpowers (suQ 5 hK x₄) ≠ zpowers (suQ 5 hK x₃) := by
  have hx3T : x₃ ∈ torus6 (unitaryInvolution K 2 2) 3 :=
    mem_torus6_iff.mpr ⟨ζ, ζ, h3, h3, hx₃⟩
  have hx4T : x₄ ∈ torus6 (unitaryInvolution K 2 2) 3 :=
    mem_torus6_iff.mpr ⟨ζ, ζ⁻¹, h3, by rw [inv_pow, h3, inv_one], hx₄⟩
  have hx33 : x₃ ^ 3 = 1 := torus6_pow_eq_one hx3T
  have hx43 : x₄ ^ 3 = 1 := torus6_pow_eq_one hx4T
  have hnot : x₄ ∉ zpowers x₃ := not_mem_zpowers_x3_x4 h1 h3 hx₃ hx₄
  intro hEq
  have hmem : suQ 5 hK x₄ ∈ zpowers (suQ 5 hK x₃) := hEq ▸ Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : suQ 5 hK (x₃ ^ k) = suQ 5 hK x₄ := by rw [map_zpow, hk]
  have hzmem : x₃ ^ k ∈ zpowers x₃ := ⟨k, rfl⟩
  have hz3 : (x₃ ^ k) ^ 3 = 1 := by
    have hdvd : orderOf (x₃ ^ k) ∣ 3 :=
      (orderOf_dvd_of_mem_zpowers hzmem).trans (orderOf_dvd_of_pow_eq_one hx33)
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hx4eq : x₃ ^ k = x₄ :=
    (CFSG.RankThree.PartOne.isCentralPQuot_suQ (K := K) (n := 5) (f := 2) Nat.prime_three
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hK).eq_of_map_eq hz3 hx43 hk'
  exact hnot (hx4eq ▸ hzmem)


private theorem derInf8_centralizer_suQ_eq (hK : Nat.card K = (2 ^ 2) ^ 2)
    {x : ↥(SU (unitaryInvolution K 2 2) 5)} (hx3 : x ^ 3 = 1) :
    F08.DerInf8 ((⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊓
      Subgroup.centralizer (Subgroup.zpowers (suQ 5 hK x) :
        Set (StatedProj (StatedSU 5 (2 ^ 2) K)))) =
      (inSubgroup perfectResidual (Subgroup.centralizer
        ({x} : Set ↥(SU (unitaryInvolution K 2 2) 5)))).map (suQ 5 hK) := by
  have hq : CFSG.RankThree.PartOne.KFU.IsCentralPQuot 3 (suQ 5 hK) :=
    CFSG.RankThree.PartOne.isCentralPQuot_suQ Nat.prime_three (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hK
  change inSubgroup perfectResidual ((⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K))) ⊓
      Subgroup.centralizer (Subgroup.zpowers (suQ 5 hK x) :
        Set (StatedProj (StatedSU 5 (2 ^ 2) K)))) =
    (inSubgroup perfectResidual (Subgroup.centralizer
      ({x} : Set ↥(SU (unitaryInvolution K 2 2) 5)))).map (suQ 5 hK)
  rw [top_inf_eq, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
    CFSG.RankThree.PartOne.KFU.map_inSubgroup_perfectResidual (suQ 5 hK),
    hq.map_centralizer hx3]

private theorem line_four_le_kOf_line_three (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ} (h1 : ζ ≠ 1)
    (h3 : ζ ^ 3 = 1) {x₃ x₄ : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ))
    (hx₄ : (x₄ : GL (Fin 5) K) = diagU (dvec5 ζ ζ⁻¹)) :
    zpowers (suQ 5 hK x₄) ≤ F08.KOf8103 ⊤ (zpowers (suQ 5 hK x₃)) := by
  have hζ : unitaryInvolution K 2 2 (ζ : K) = ζ := by
    have h := CFSG.RankThree.PartTwo.Sec21.U4Lines.unitaryInvolution_rootsOfUnity
      (F := K) (b := 2) even_two (⟨ζ, (mem_rootsOfUnity 3 ζ).mpr h3⟩ : rootsOfUnity 3 K)
    simpa using h
  have h2 : ζ ^ 2 ≠ 1 := by
    intro h
    apply h1
    calc ζ = ζ ^ 3 * (ζ ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h, inv_one, one_mul]
  have hσσ : ∀ c, unitaryInvolution K 2 2 (unitaryInvolution K 2 2 c) = c :=
    unitaryInvolution_involutive hK
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  have hx3T : x₃ ∈ torus6 (unitaryInvolution K 2 2) 3 :=
    mem_torus6_iff.mpr ⟨ζ, ζ, h3, h3, hx₃⟩
  have hx33 : x₃ ^ 3 = 1 := torus6_pow_eq_one hx3T
  have hx3b : x₃ = b6 (unitaryInvolution K 2 2) ζ hζ := Subtype.ext (by rw [hx₃, coe_b6])
  have hH : inSubgroup perfectResidual (Subgroup.centralizer
      ({x₃} : Set ↥(SU (unitaryInvolution K 2 2) 5))) =
      (suBlock6 (unitaryInvolution K 2 2) hσσ).range := by
    rw [hx3b]
    exact perfectResidual_centralizer_b6 (unitaryInvolution K 2 2) hσσ hK4 hζ h1 h2
  have hx4range : x₄ ∈ (suBlock6 (unitaryInvolution K 2 2) hσσ).range := by
    have hx4rho : x₄ = rho6 (unitaryInvolution K 2 2) hσσ ζ :=
      Subtype.ext (by rw [hx₄, coe_rho6 hσσ hζ])
    rw [hx4rho]
    exact ⟨diag2Hom K ζ, rfl⟩
  unfold F08.KOf8103
  rw [derInf8_centralizer_suQ_eq hK hx33, hH]
  exact Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem (suQ 5 hK) hx4range)

private theorem line_three_le_kOf_line_four (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ} (h1 : ζ ≠ 1)
    (h3 : ζ ^ 3 = 1) {x₃ x₄ : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ))
    (hx₄ : (x₄ : GL (Fin 5) K) = diagU (dvec5 ζ ζ⁻¹)) :
    zpowers (suQ 5 hK x₃) ≤ F08.KOf8103 ⊤ (zpowers (suQ 5 hK x₄)) := by
  have hfirst := line_four_le_kOf_line_three hK h1 h3 hx₃ hx₄
  let w : ↥(SU (unitaryInvolution K 2 2) 5) :=
    ⟨permGL (Equiv.swap (1 : Fin 5) 3), permGL_mem_SU (unitaryInvolution K 2 2) _ (by decide)⟩
  have hw : w * x₃ * w⁻¹ = x₄ := by
    apply Subtype.ext
    change (permGL (Equiv.swap (1 : Fin 5) 3) * (x₃ : GL (Fin 5) K) *
      (permGL (Equiv.swap (1 : Fin 5) 3))⁻¹ : GL (Fin 5) K) = (x₄ : GL (Fin 5) K)
    rw [hx₃, hx₄, permGL_swap13_conj_dvec5]
  have hww : w * w = 1 := by
    apply Subtype.ext
    change (permGL (Equiv.swap (1 : Fin 5) 3) * permGL (Equiv.swap (1 : Fin 5) 3) :
      GL (Fin 5) K) = 1
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  let qw : StatedProj (StatedSU 5 (2 ^ 2) K) := suQ 5 hK w
  have hqw2 : qw * qw = 1 := by
    change suQ 5 hK w * suQ 5 hK w = 1
    rw [← map_mul, hww, map_one]
  have hℓ : Subgroup.zpowers (suQ 5 hK x₄) =
      (Subgroup.zpowers (suQ 5 hK x₃)).map (MulAut.conj qw).toMonoidHom := by
    rw [← hw, map_mul, map_mul, map_inv, CFSG.GroupTheory.map_conj_zpowers]
  have hKconj : F08.KOf8103 ⊤ (Subgroup.zpowers (suQ 5 hK x₄)) =
      (F08.KOf8103 ⊤ (Subgroup.zpowers (suQ 5 hK x₃))).map
        (MulAut.conj qw).toMonoidHom := by
    unfold F08.KOf8103
    rw [hℓ]
    simpa only [F08.DerInf8, inSubgroup, perfectResidual] using
      (CFSG.RankThree.PartTwo.Sec21.U4Lines.perfectResidual_conj (Y := ⊤)
        (Subgroup.mem_top qw) (Subgroup.zpowers (suQ 5 hK x₃)))
  have hmap := Subgroup.map_mono (f := (MulAut.conj qw).toMonoidHom) hfirst
  rw [hℓ, CFSG.GroupTheory.map_conj_map_conj, hqw2] at hmap
  rw [← hKconj] at hmap
  refine le_trans ?_ hmap
  intro x hx
  exact ⟨x, hx, by simp⟩

theorem u5_line_le_kOf (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ} (h1 : ζ ≠ 1)
    (h3 : ζ ^ 3 = 1) {x₃ x₄ : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ))
    (hx₄ : (x₄ : GL (Fin 5) K) = diagU (dvec5 ζ ζ⁻¹)) :
    zpowers (suQ 5 hK x₄) ≤ F08.KOf8103 ⊤ (zpowers (suQ 5 hK x₃)) ∧
      zpowers (suQ 5 hK x₃) ≤ F08.KOf8103 ⊤ (zpowers (suQ 5 hK x₄)) :=
  ⟨line_four_le_kOf_line_three hK h1 h3 hx₃ hx₄,
    line_three_le_kOf_line_four hK h1 h3 hx₃ hx₄⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
