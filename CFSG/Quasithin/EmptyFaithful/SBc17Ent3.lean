module

public import CFSG.Quasithin.EmptyFaithful.SBc17Ent2
public import CFSG.Quasithin.EmptyFaithful.SBc11List
public import CFSG.Quasithin.Recognition.CertU33AutBound
public import CFSG.Timmesfeld.Final.PSU33
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import Certificates.Certificate19953
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14113Layer
public import CFSG.Quasithin.EmptyFaithful.S1469Sev
public import CFSG.Quasithin.EmptyFaithful.S1469Three
public import CFSG.Quasithin.EmptyFaithful.S146F16
public import CFSG.Quasithin.EmptyFaithful.S146zMComp
public import CFSG.Quasithin.EmptyFaithful.S146zQLists
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S152Y15
public import CFSG.Quasithin.EmptyFaithful.S152Y19
public import CFSG.Quasithin.EmptyFaithful.SBc15R3G
public import CFSG.Quasithin.EmptyFaithful.SBc16SComp
public import CFSG.Quasithin.EmptyFaithful.SBc16SWr
public import CFSG.Quasithin.EmptyFaithful.T1515Der2
public import CFSG.Quasithin.EmptyFaithful.T1515Der3
public import CFSG.Quasithin.SteinbergOuterPrimeControl
public import CFSG.Sporadic.Schreier.J4SThree
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate8026Base

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace SBc17

theorem nonempty_mulEquiv_PSU3_of_isPSU {X : Type} [Group X] (h : IsPSU 3 3 1 X) :
    Nonempty (X ≃* CFSG.Open.PSU3 3 1) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (GaloisField 3 (2 * 1))
  have hc : Fintype.card K = Fintype.card (GaloisField 3 (2 * 1)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      CFSG.Timmesfeld.Final.GF9.card]
  obtain ⟨e'⟩ := CFSG.Timmesfeld.Final.nonempty_statedProj_statedSU_equiv_PSU3
  exact ⟨e.trans ((CFSG.Fischer.Classification.Recognition.statedProjSUEquiv
    (FiniteField.ringEquivOfCardEq hc) 3 (3 ^ 1)).trans e')⟩

theorem factOut5U33 :
    FactOut5U33 := by
  intro X _ h
  obtain ⟨e⟩ := nonempty_mulEquiv_PSU3_of_isPSU h
  have hcard := SBc11.card_of_isPSU_three_three h
  have hfin : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hA : Nat.card (MulAut X) ≤ 4 * Nat.card X := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv, hcard]
    have := card_mulAut_psu3_le
    omega
  exact out5Inner_of_card_mulAut_le (SBc11.center_eq_bot_of_list (Or.inr (Or.inr h))) hA

end SBc17

theorem stages14613_to_14617_of_SBc17D_cert_noUK_solDec
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h2 : Stage1461Two) (h5 : Stage1461Five) (h12 : Stage14612PartP) (h4 : Stage1463Four)
    (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (iA : Input14613AP) (iB1 : Input14613B1P) (iB2 : Input14613B2P)
    (i14b : Input14614SolDec) (i14c : Input14614Shape)
    (iSF : Input14615SetupFourP) (iFix : SBc17.Input14615FixR)
    (iOD : SBc17.Input14615ContraOuterD) (iIB : SBc17.Input14615ContraInnerB)
    (iWeak : Input14616Weak) (iF : Input14617FstarK) :
    Stage14613LabP ∧ Stage14614 ∧ Stage14615 ∧ Stage14616 ∧ Stage14617 :=
  stages14613_to_14617_of_SBc17D_noUK_solDec SBc17.factOut5U33 hC27 h2 h5 h12 h4 h36 h38 iA iB1 iB2
    i14b i14c iSF iFix iOD iIB iWeak iF

end CFSG.Quasithin
