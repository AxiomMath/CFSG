module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKDefs
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLin
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

private theorem rckl_label_eq_L32 {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : ggSixRCKLabelRow lab = .L32) : lab = ⟨.A, 2, 1⟩ := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag
  · dsimp only [ggSixRCKLabelRow] at h
    have hc1 : ¬ 2 ≤ n := by
      intro hc1; rw [if_pos hc1] at h; exact absurd h (by decide)
    have hc2 : rank ≠ 3 := by
      intro hc2; rw [if_neg hc1, if_pos hc2] at h; exact absurd h (by decide)
    have hc3 : ¬ 4 ≤ rank := by
      intro hc3; rw [if_neg hc1, if_neg hc2, if_pos hc3] at h; exact absurd h (by decide)
    dsimp only [LargeEvenInLambda2] at hlab
    obtain ⟨hn1, hr1, hr2⟩ := hlab
    have hn : n = 1 := by omega
    have hr : rank = 2 := by
      have hrle : rank ≤ 2 := by omega
      by_contra hne
      have hr1' : rank = 1 := by omega
      have := hr2 hr1'
      omega
    subst hn; subst hr; rfl
  all_goals
    dsimp only [ggSixRCKLabelRow] at h
    first
      | (split_ifs at h <;> exact absurd h (by decide))
      | exact absurd h (by decide)

private theorem rckl_marking_statedClassicalModel {X : Type} [Group X] {J : Subgroup X}
    (h : GGSixRCKJRow .L32 J) :
    commutator ↥J = ⊤ ∧ StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 1 := by
  unfold GGSixRCKJRow LargeEvenMarking at h
  obtain ⟨hJ, lab, hlab, hraw⟩ := h
  obtain ⟨R₀, _, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  dsimp only at hQ₀
  obtain ⟨-, hrowlab⟩ := hQ₀.2.2
  have hlab_eq : lab = ⟨.A, 2, 1⟩ := rckl_label_eq_L32 hlab hrowlab
  rw [hlab_eq] at hraw
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, hKfield, hKfinite, hKcard, hQproj⟩ := hraw
  dsimp only at hQproj
  obtain ⟨θ, -⟩ := hQproj.2.2
  refine ⟨hJ, ?_⟩
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  have hadm : StatedLieAdmissible .PSL 3 2 1 :=
    ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩
  exact statedClassicalModel_of_mulEquiv' θ.symm
    (statedClassicalModel_linear 3 1 (by simpa using hKcard) hadm)

theorem not_jRow_L32_of_hA {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {B₁ D J : Subgroup X} (hB : IsElemAbelian p B₁) (hD : Nat.card D = p ^ 2)
    (hBN : B₁ ≤ Subgroup.normalizer (J : Set X)) (hC : B₁ ⊓ Subgroup.centralizer (J : Set X) = D)
    (h4 : p ^ 4 ≤ Nat.card B₁) : ¬ GGSixRCKJRow .L32 J := by
  intro hrow
  obtain ⟨hJ, hSC⟩ := rckl_marking_statedClassicalModel hrow
  let Y := ↥J ⧸ Subgroup.center ↥J
  haveI : Finite Y := inferInstance
  have hBp : IsPGroup p ↥B₁ := CFSG.Open.IsElemAbelian.isPGroup hB
  let ψ : ↥B₁ →* MulAut ↥J :=
    (Subgroup.normalizerMonoidHom J).comp (Subgroup.inclusion hBN)
  let ρ : ↥B₁ →* MulAut Y :=
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥J).comp ψ
  have hker_le : Nat.card ρ.ker ≤ p ^ 2 := by
    haveI : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJ
    have hkermap : ρ.ker.map B₁.subtype ≤ B₁ ⊓ Subgroup.centralizer (J : Set X) := by
      rintro x ⟨b, hb, rfl⟩
      have hbρ : ρ b = 1 := hb
      have hψ : ψ b = 1 := by
        apply CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective ↥J
        rw [map_one]
        change ρ b = 1
        rw [hbρ]
      have hcent : (b : X) ∈ Subgroup.centralizer (J : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro j hj
        have hfix : ψ b ⟨j, hj⟩ = ⟨j, hj⟩ := by simp [hψ]
        have hval : (b : X) * j * (b : X)⁻¹ = j := congrArg Subtype.val hfix
        exact (mul_inv_eq_iff_eq_mul.mp hval).symm
      exact ⟨b.2, hcent⟩
    calc Nat.card ρ.ker = Nat.card (ρ.ker.map B₁.subtype) :=
          (Subgroup.card_map_of_injective B₁.subtype_injective).symm
      _ ≤ Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) := Subgroup.card_le_of_le hkermap
      _ = Nat.card ↥D := by rw [hC]
      _ = p ^ 2 := by rw [hD]
  have hcard : Nat.card ρ.ker * Nat.card ρ.range = Nat.card ↥B₁ :=
    Subgroup.card_ker_mul_card_range ρ
  have hrange_ge : p ^ 2 ≤ Nat.card ρ.range := by
    have hpos : 0 < p ^ 2 := pow_pos hp.pos 2
    by_contra hlt
    have hlt : Nat.card ρ.range < p ^ 2 := not_le.mp hlt
    have : Nat.card ρ.ker * Nat.card ρ.range < p ^ 2 * p ^ 2 :=
      lt_of_le_of_lt (Nat.mul_le_mul_right _ hker_le) (Nat.mul_lt_mul_of_pos_left hlt hpos)
    have h44 : p ^ 2 * p ^ 2 = p ^ 4 := by ring
    omega
  have hPp_range : IsPGroup p ρ.range :=
    hBp.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hout : CFSG.AGLEmbedding.ParabAutIrr.OutPInner Y p :=
    CFSG.AGLEmbedding.ParabAutIrr.outPInner_psl_two hSC hp hp2
  have hle : ρ.range ≤ CFSG.AGLEmbedding.ParabAutIrr.inn Y := hout ρ.range hPp_range
  have hdvd1 : Nat.card ρ.range ∣ Nat.card (CFSG.AGLEmbedding.ParabAutIrr.inn Y) :=
    Subgroup.card_dvd_of_le hle
  have hdvd2 : Nat.card (CFSG.AGLEmbedding.ParabAutIrr.inn Y) ∣ Nat.card Y :=
    Subgroup.card_range_dvd (MulAut.conj : Y →* MulAut Y)
  have hp2_dvd_range : p ^ 2 ∣ Nat.card ρ.range := by
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Finite ρ.range := inferInstance
    obtain ⟨k, hk⟩ := hPp_range.exists_card_eq
    have hk2 : 2 ≤ k := by
      by_contra hk2
      push Not at hk2
      have hle : p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
      rw [hk] at hrange_ge
      simp only [pow_one] at hle
      have hp2le : p ^ 2 ≤ p := le_trans hrange_ge hle
      nlinarith [hp.two_le, sq_nonneg (p : ℤ)]
    rw [hk]
    exact pow_dvd_pow p hk2
  have hp2dvdY : p ^ 2 ∣ Nat.card Y := dvd_trans (dvd_trans hp2_dvd_range hdvd1) hdvd2
  have hYdvd : Nat.card Y ∣ 168 := by
    obtain ⟨K', hK'F, hK'Fin, hK'card, ⟨e⟩⟩ :=
      CFSG.AGLEmbedding.ParabAutIrr.exists_equiv_projectiveSL hSC
    letI : Field K' := hK'F
    letI : Finite K' := hK'Fin
    have hdvd : Nat.card Y ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) K') := by
      rw [Nat.card_congr e.toEquiv]
      rw [← Subgroup.index_eq_card]
      exact Subgroup.index_dvd_card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 K')
    have hK2 : Nat.card K' = 2 := by simpa using hK'card
    have h168 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) K') = 168 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hK2]
      decide
    rw [h168] at hdvd
    exact hdvd
  have hp2dvd168 : p ^ 2 ∣ 168 := dvd_trans hp2dvdY hYdvd
  have hp_le : p ≤ 12 := by
    by_contra h
    push Not at h
    have h1 : 13 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (by omega : 13 ≤ p) 2
    have h2 : p ^ 2 ≤ 168 := Nat.le_of_dvd (by norm_num) hp2dvd168
    norm_num at h1
    omega
  interval_cases p <;> norm_num at *

end CFSG.StandardType
