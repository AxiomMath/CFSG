module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAutKCore
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.RankThree.PartOne.MB3.OddOutLinear
public import CFSG.RankThree.PartOne.MB3.OddOutSymplectic
public import CFSG.RankThree.PartOne.MB3.OddOutOrthogonal
public import CFSG.RankThree.PartOne.S11d.OddOutPSL2
public import CFSG.RankThree.PartOne.AUTSL.SpTwoAut
import CFSG.Models.Blueprint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import CFSG.Blueprint.LieModelAPI
import CFSG.Models.Transport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.OutStructure

theorem ggNot_prime_dvd_pow_sub_one {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) : ¬ p ∣ p ^ e - 1 := by
  intro h
  have h1 : p ∣ p ^ e := dvd_pow_self p (by omega)
  have h2 : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
  have h3 : p ∣ p ^ e - (p ^ e - 1) := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self h2] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)

theorem ggNot_prime_dvd_pow_add_one {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) : ¬ p ∣ p ^ e + 1 := by
  intro h
  have h1 : p ∣ p ^ e := dvd_pow_self p (by omega)
  exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp h))

theorem ggStatedClassicalModel_of_lieModel {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (h : CFSG.Models.LieModel G t n p f) : StatedClassicalModel G t n p f :=
  CFSG.Models.LieModel.statedClassicalModel h
    (by rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

theorem ggLieOutRankTwoAt_A (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A r q).Valid) (h : 2 ≤ r ∨ 5 ≤ q.p) :
    GGLieOutRankTwoAt ⟨.A r q, hv⟩ := by
  refine ggLieOutRankTwoAt_of_char (TauCeti.LieTypeIndex.characteristic_A r q) fun hp2 => ?_
  have hm := ggStatedClassicalModel_of_lieModel (Or.inl rfl)
    (CFSG.Models.lieModel_A (G := (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group) r q hv
      (MulEquiv.refl _))
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  by_cases hr2 : 2 ≤ r
  · refine (outPNice_PSL_ge_three_odd q.prime_p hp2 (by omega) hm fun hdvd => ?_).toChain
    exact ggNot_prime_dvd_pow_sub_one q.prime_p q.exponent_pos
      (hdvd.trans (Nat.gcd_dvd_right _ _))
  · have hr1 : r = 1 := by have := hr.1; omega
    subst hr1
    have hp5 : 5 ≤ q.p := h.resolve_left hr2
    exact (outPNice_PSL_two_odd q.prime_p (by omega) hp2 hm).toChain

theorem ggLieOutRankTwoAt_twistedA (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) :
    GGLieOutRankTwoAt ⟨.twistedA r q, hv⟩ := by
  refine ggLieOutRankTwoAt_of_char (TauCeti.LieTypeIndex.characteristic_twistedA r q)
    fun _ => ?_
  have hm := ggStatedClassicalModel_of_lieModel (Or.inr (Or.inl rfl))
    (CFSG.Models.lieModel_twistedA (G := (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group) r q
      hv (MulEquiv.refl _))
  rw [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.LieTypeIndex.characteristic_twistedA,
    TauCeti.ValidLieTypeIndex.fieldExponent, TauCeti.LieTypeIndex.fieldExponent_twistedA] at hm
  refine (outPNice_PSU_odd q.prime_p hm fun hdvd => ?_).toChain
  exact ggNot_prime_dvd_pow_add_one q.prime_p q.exponent_pos (hdvd.trans (Nat.gcd_dvd_right _ _))

theorem ggOutPNice_PSp_ge_three_odd {X : Type} [Group X] {r ℓ f p : ℕ} (hr : 3 ≤ r)
    (hp : p.Prime) (hp2 : p ≠ 2) (h : StatedClassicalModel X .PSp r ℓ f) : OutPNice p X := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
  exact OutPNice.of_mulEquiv e (outPNice_StatedSp_odd hr hp hp2)

theorem ggLieOutRankTwoAt_C (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.C r q).Valid) : GGLieOutRankTwoAt ⟨.C r q, hv⟩ := by
  refine ggLieOutRankTwoAt_of_char (TauCeti.LieTypeIndex.characteristic_C r q) fun hp2 => ?_
  have hm := ggStatedClassicalModel_of_lieModel (Or.inr (Or.inr (Or.inl rfl)))
    (CFSG.Models.lieModel_C (G := (TauCeti.CFSGIndex.lie ⟨.C r q, hv⟩).Group) r q hv
      (MulEquiv.refl _))
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  exact (ggOutPNice_PSp_ge_three_odd hr.1 q.prime_p hp2 hm).toChain

theorem ggLieOutRankTwoAt_B (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (h : r = 2 ∨ 5 ≤ q.p) :
    GGLieOutRankTwoAt ⟨.B r q, hv⟩ := by
  refine ggLieOutRankTwoAt_of_char (TauCeti.LieTypeIndex.characteristic_B r q) fun hp2 => ?_
  rcases CFSG.Models.lieModel_B (G := (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group) r q hv
      (MulEquiv.refl _) with hm | hm
  · have hm' := ggStatedClassicalModel_of_lieModel (Or.inr (Or.inr (Or.inl rfl))) hm
    by_cases hr : r = 2
    · subst hr
      exact (CFSG.RankThree.PartOne.AUTSL.SpTwo.outPNice_PSp_two_odd q.prime_p hp2 hp2
        hm').toChain
    · have hr3 : 3 ≤ r := by
        have := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
          ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
        omega
      exact (ggOutPNice_PSp_ge_three_odd hr3 q.prime_p hp2 hm').toChain
  · have hm' := ggStatedClassicalModel_of_lieModel (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hm
    have hp5 : 5 ≤ q.p := by
      rcases h with rfl | h
      · exact absurd hm'.1.2.2.1 (by norm_num)
      · exact h
    exact (outPNice_POmegaOdd_gen q.prime_p hp5 hm').toChain

theorem ggLieOutRankTwoAt_D (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D r q).Valid) (hp5 : 5 ≤ q.p) :
    GGLieOutRankTwoAt ⟨.D r q, hv⟩ := by
  refine ggLieOutRankTwoAt_of_char (TauCeti.LieTypeIndex.characteristic_D r q) fun _ => ?_
  have hm := ggStatedClassicalModel_of_lieModel (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (CFSG.Models.lieModel_D (G := (TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩).Group) r q hv
      (MulEquiv.refl _))
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  by_cases hr5 : 5 ≤ r
  · exact (outPNice_POmegaPlus_gen_ge_five q.prime_p hp5 hr5 hm).toChain
  · have hr4 : r = 4 := by omega
    subst hr4
    exact outPChain_POmegaPlus_four_gen q.prime_p hp5 hm

theorem ggLieOutRankTwoAt_twistedD (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) (hp5 : 5 ≤ q.p) :
    GGLieOutRankTwoAt ⟨.twistedD r q, hv⟩ := by
  refine ggLieOutRankTwoAt_of_char (TauCeti.LieTypeIndex.characteristic_twistedD r q) fun _ => ?_
  have hm := ggStatedClassicalModel_of_lieModel (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    (CFSG.Models.lieModel_twistedD (G := (TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group) r q
      hv (MulEquiv.refl _))
  exact (outPNice_POmegaMinus_gen q.prime_p hp5 hm).toChain

end CFSG.StandardType
