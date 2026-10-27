module

public import CFSG.Quasithin.Background.RonanE114J4Aut
public import CFSG.Quasithin.Background.RonanE114J4Quot
public import CFSG.Quasithin.Background.RonanE114C5M22
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4Cz0
public import CFSG.Quasithin.EmptyFaithful.E22NJ4
public import CFSG.Monster.B.TwoA.Fischer.M22Aut
public import CFSG.Goldschmidt.StatementsG2
public import CFSG.Goldschmidt.StatementsG3
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteCore
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSquareProd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTop
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTwist
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperCommutingImages
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SmallerRecognitionDischarge
public import CFSG.Quasithin.Background.RonanE114ClausesL52He
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParMain
public import CFSG.Quasithin.EmptyFaithful.SzN15Good
public import CFSG.Quasithin.H13.QRCBenderAmbient
public import CFSG.Quasithin.H13.QRCBenderPairModel
public import CFSG.Quasithin.SteinbergCCPrimeWitness
public import CFSG.Quasithin.Vol2.Ch3E213MP6BC
public import CFSG.Quasithin.Vol2.Ch3E213MP6BD

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin CFSG.Quasithin.E2P

theorem nParam_mulAut_M22_le_two :
    E1.nParam (⊤ : Subgroup (MulAut ↥CFSG.Blueprint.NativeSporadic.M22)) ≤ 2 := by
  obtain ⟨-, -, hsimple⟩ := CFSG.Sporadic.Mathieu.fam_m22_simplicity
  obtain ⟨-, hout, -⟩ := CFSG.Monster.B.TwoA.Fischer.catalog_M22_full_automorphism_order
  have hnc : ∃ x y : ↥CFSG.Blueprint.NativeSporadic.M22, x * y ≠ y * x := by
    by_contra hcomm
    push Not at hcomm
    haveI : IsMulCommutative ↥CFSG.Blueprint.NativeSporadic.M22 := ⟨⟨fun a b => hcomm a b⟩⟩
    have hcard22 : Nat.card ↥CFSG.Blueprint.NativeSporadic.M22 = 443520 :=
      CFSG.Sporadic.Mathieu.card_M22
    have hp := Group.is_simple_iff_prime_card.1 hsimple
    rw [hcard22] at hp
    norm_num at hp
  obtain ⟨T', hT', hgen, -, ⟨e⟩⟩ := exists_data_mulAut hnc hout
  exact_mod_cast C5.M22.nParam_le_two_of_isM22 ⟨e.symm⟩ (quasithinIsSylowTwo_of_isSylowIn hT')
    hgen

theorem nParam_centralizer_z0_le_two :
    E1.nParam (Subgroup.centralizer ({eta uJ 11 1131} : Set J)) ≤ 2 := by
  have hM := j4Facts.mat
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J j4Facts]; norm_num)
  have hz : eta uJ 11 1131 ∈ Eg uJ 11 := eta_mem_Eg 11 le_rfl 1131
  have hz1 : eta uJ 11 1131 ≠ 1 := by
    intro h
    have h0 : eta uJ 11 1131 = eta uJ 11 0 := h.trans (eta_zero _ _).symm
    have := eta_inj hM 1131 (by norm_num) 0 (by norm_num) h0
    omega
  have hfix : ∀ t ∈ P0, t * eta uJ 11 1131 = eta uJ 11 1131 * t := by
    intro t ht
    have h := J4Two.P0_le_centralizer ht
    rw [Subgroup.mem_centralizer_singleton_iff] at h
    exact h
  obtain ⟨-, -, -, hquot, -⟩ := J4L4.isTypeJ4Centralizer_of_fixed hz hz1 hfix
  obtain ⟨Z, hZn, hZc, -, -, -, -, -, θ, -, -, -, hθs, hθk, -⟩ := hquot
  set C : Subgroup J := Subgroup.centralizer ({eta uJ 11 1131} : Set J)
  haveI : Finite ↥C := inferInstance
  haveI : Z.Normal := hZn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥C) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hRs : Group.IsSolvable ↥(CFSG.pCore 2 ↥C) := by
    have := hR2.isNilpotent
    infer_instance
  have hZp : IsPGroup 3 ↥Z := IsPGroup.of_card (n := 1) (by simpa using hZc)
  have hZs : Group.IsSolvable ↥Z := by
    have := hZp.isNilpotent
    infer_instance
  let e : ((↥C ⧸ CFSG.pCore 2 ↥C) ⧸ Z) ≃* MulAut ↥CFSG.Blueprint.NativeSporadic.M22 :=
    (QuotientGroup.quotientMulEquivOfEq hθk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective θ hθs)
  have hA := nParam_mulAut_M22_le_two
  have h1 : E1.nParam (⊤ : Subgroup (↥C ⧸ CFSG.pCore 2 ↥C)) ≤ ((2 : ℕ) : ℕ∞) :=
    nParam_top_le_of_equiv_quotient (i := 2) (by norm_num) Z hZs e (by exact_mod_cast hA)
  have := nParam_le_of_equiv_quotient (i := 2) (by norm_num) C (CFSG.pCore 2 ↥C) hRs
    (MulEquiv.refl _) h1
  exact_mod_cast this

end CFSG.Quasithin.RonanE114
