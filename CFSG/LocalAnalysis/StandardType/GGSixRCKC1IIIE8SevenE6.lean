module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIE6Seven
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutE6Two
public import CFSG.LocalAnalysis.StandardType.GGSixRCK1416Defs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeStepA
public import Certificates.Certificate14972
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIE8Transport
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1CentralCover
import CFSG.LocalAnalysis.StandardType.GGE6TwoSevenComp
import CFSG.LocalAnalysis.StandardType.GGCompListMarked
import CFSG.LocalAnalysis.StandardType.GGK0MarkedArithmetic
import CFSG.LocalAnalysis.StandardType.GGReverseMarking
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldE6
import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
import CFSG.LocalAnalysis.StandardType.GGHalfCentGroup

public section
namespace CFSG.StandardType.RCKC1
open CFSG CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType


theorem k2At_of_e8_seven_e6_label_compConfig
    {X : Type} [Group X] [Finite X] {n : ℕ}
    {ψ : (ggU .E8 n 1).K →* X} {G₀ A B₁ D J L K V : Subgroup X} {e r : X}
    (hcfg : RCKRP.RCKCompConfig .E8 n 1 ψ 7 G₀ A B₁ D J L K e)
    (hrow : GGSixRCKJRow .III J) (hFour : FourAt J V r)
    (hCore : CoreCommAt J V r) (hShort : ShortAt J r)
    (hlabel : GGHasLabel ⟨.E6, 0, 1⟩ (↥K ⧸ Subgroup.center ↥K)) : K2At K V r := by
  classical
  by_cases hKJ : K = J
  · subst K
    exact k2At_self_of_coreCommAt hFour.1 hCore
  obtain ⟨-, -, hp, hp2, hA, hBA, hDB, hDcard, hAN, -, hBNJ, -, -, -, -, -, -, -,
    hJcomp, -, -, -, -, -, -, heD, hene, hKcomp, hJK, -⟩ := hcfg
  obtain ⟨hBNK, d, hdD, -, hJd⟩ := RCKRP.le_normalizer_and_exists_isComponentOf_of_plane
    hp hA hBA hDB hDcard hAN hBNJ hJcomp heD hene hKcomp hJK
  have hdN : d ∈ Subgroup.normalizer (K : Set X) := hBNK (hDB hdD)
  let α : MulAut K := K.normalizerMonoidHom ⟨d, hdN⟩
  have hα7 : α ^ 7 = 1 := by
    have hd7 : (⟨d, hdN⟩ : Subgroup.normalizer (K : Set X)) ^ 7 = 1 :=
      Subtype.ext (hA.2 d (hBA (hDB hdD)))
    change (K.normalizerMonoidHom ⟨d, hdN⟩) ^ 7 = 1
    rw [← map_pow, hd7, map_one]
  have hα1 : α ≠ 1 := by
    intro h1
    have hKC : K ≤ Subgroup.centralizer ({d} : Set X) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : y = d := Set.mem_singleton_iff.mp hy
      subst y
      have h := congrArg (fun β : MulAut K => ((β ⟨x, hx⟩ : K) : X)) h1
      change d * x * d⁻¹ = x at h
      exact mul_inv_eq_iff_eq_mul.mp h
    have hJc : IsComponentOf J K := by
      simpa only [inf_eq_left.mpr hKC] using hJd
    exact hKJ (GGHalf.eq_of_isComponentOf_isQuasisimple hKcomp.2.2 hJc).symm
  have hKperf : commutator ↥K = ⊤ := hKcomp.2.2.1
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hKcomp.2.2.2
  have hnab : ∃ a b : ↥K ⧸ Subgroup.center ↥K, a * b ≠ b * a :=
    exists_mul_ne_mul_centerQuot_of_perfect hKperf inferInstance
  have hM := GGK0MarkedArithmetic.markedModel_of_label
    (by simp [LargeEvenInLambda2]) hnab hlabel
  have hLM : LieModel (↥K ⧸ Subgroup.center ↥K) .E6 0 2 1 := by
    simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM
  obtain ⟨κ, hαinner⟩ := exists_conj_of_e6_two_of_pow_eq_one hKperf hLM hp hp2 (by decide) hα7
  obtain ⟨hperf, lab, hΛ, hraw⟩ := largeEvenMarking_of_lieModel_centerQuot hKperf hLM
  obtain ⟨R, _, I, F, -, -, θ, htag, -, -, hdeg⟩ := largeEvenRawDatum_exists hraw
  have hlab : lab = ⟨.E6, 0, 1⟩ := by
    rcases lab with ⟨tag, rank, exponent⟩
    cases tag <;> simp_all [markTag, markDeg, LargeEvenInLambda2]
    all_goals split_ifs at htag
  subst lab
  have hrawI := ggRawInnFieldOn_E6 7 (by decide) (by decide) ⟨.E6, 0, 1⟩ hΛ rfl _ hraw
  have hmarked : LargeEvenRawDatum (⟨.E6, 0, 1⟩ : LargeEvenLabel) fun R _ I _ =>
      ∃ θ : ↥K ⧸ Subgroup.center ↥K ≃* R, ∃ β ∈ I,
        LargeEvenInduces θ (fun x y => y = α x) β := by
    apply largeEvenRawDatum_mono _ hrawI
    rintro R _ I F ⟨⟨hsimple, hnab, θ, -, -, -, -⟩, hI⟩
    let β : MulAut R := MulAut.conj (θ (QuotientGroup.mk κ))
    refine ⟨θ, β, (hI hsimple hnab).2.2.1 _, ?_⟩
    intro x y hy
    subst y
    simp [β, hαinner]
  obtain ⟨labJ, hmem, hlabelJ⟩ := GGCompList.of_rawMarking E6TwoSeven.ggE6TwoSevenComp_holds
    hperf hα7 hα1 hmarked (isComponentOf_subgroupOf_ggAutFixed hdN hJK hJd)
  exact (not_e6_seven_label_of_row_III_le hrow le_rfl ⟨labJ, hmem,
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) hlabelJ⟩).elim

theorem k2At_of_e8_seven_component_label
    {X : Type} [Group X] [Finite X] {n : ℕ}
    {ψ : (ggU .E8 n 1).K →* X} {G₀ A B₁ D J L K V : Subgroup X} {e r : X}
    (hcfg : RCKRP.RCKCompConfig .E8 n 1 ψ 7 G₀ A B₁ D J L K e)
    (hrow : GGSixRCKJRow .III J) (hFour : FourAt J V r)
    (hCore : CoreCommAt J V r) (hShort : ShortAt J r)
    {lab : LargeEvenLabel} (hmem : lab ∈ [⟨.E6, 0, 1⟩, ⟨.A, 2, 1⟩, ⟨.triD4, 0, 1⟩])
    (hlabel : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K)) : K2At K V r := by
  rcases List.mem_cons.mp hmem with rfl | hsmall
  · exact k2At_of_e8_seven_e6_label_compConfig hcfg hrow hFour hCore hShort hlabel
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, hJK, -⟩ := hcfg
    exact (not_e6_seven_label_of_row_III_le hrow hJK ⟨lab, hsmall, hlabel⟩).elim


theorem k2At_of_e8_seven_compConfig
    {X : Type} [Group X] [Finite X] {n : ℕ}
    {ψ : (ggU .E8 n 1).K →* X} {G₀ A B₁ D J L K V : Subgroup X} {e r : X}
    (hcfg : RCKRP.RCKCompConfig .E8 n 1 ψ 7 G₀ A B₁ D J L K e)
    (hrow : GGSixRCKJRow .III J) (hFour : FourAt J V r)
    (hCore : CoreCommAt J V r) (hShort : ShortAt J r) : K2At K V r := by
  obtain ⟨lab, hmem, hlabel⟩ := e8_seven_compConfig_has_component_label hcfg
  have hmem' : lab ∈ [⟨.E6, 0, 1⟩, ⟨.A, 2, 1⟩, ⟨.triD4, 0, 1⟩] := by
    simpa [or_comm, or_left_comm, or_assoc] using hmem
  exact k2At_of_e8_seven_component_label hcfg hrow hFour hCore hShort hmem' hlabel

end CFSG.StandardType.RCKC1
