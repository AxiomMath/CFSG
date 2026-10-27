module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporAssemble
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.Quasithin.H13.J4Words
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate9124

public section

namespace CFSG.StandardType.SporadicShape

open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def SporKRestCoverPair (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
    (s = .M12 ∧ p = 3) ∨
    (s = .M22 ∧ p = 3) ∨
    (s = .M23 ∧ p = 3) ∨
    (s = .M24 ∧ p = 3) ∨
    (s = .J2 ∧ p = 3) ∨
    (s = .J2 ∧ p = 5) ∨
    (s = .J4 ∧ p = 3) ∨
    (s = .HS ∧ p = 3) ∨
    (s = .McL ∧ p = 3) ∨
    (s = .Suz ∧ p = 3) ∨
    (s = .Suz ∧ p = 5) ∨
    (s = .Ru ∧ p = 3) ∨
    (s = .Ru ∧ p = 5) ∨
    (s = .He ∧ p = 3) ∨
    (s = .He ∧ p = 5) ∨
    (s = .He ∧ p = 7) ∨
    (s = .Ly ∧ p = 3) ∨
    (s = .Ly ∧ p = 5) ∨
    (s = .ONan ∧ p = 3) ∨
    (s = .ONan ∧ p = 7) ∨
    (s = .Co1 ∧ p = 3) ∨
    (s = .Co1 ∧ p = 5) ∨
    (s = .Co1 ∧ p = 7) ∨
    (s = .Co2 ∧ p = 3) ∨
    (s = .Co2 ∧ p = 5) ∨
    (s = .Co3 ∧ p = 3) ∨
    (s = .Co3 ∧ p = 5) ∨
    (s = .Fi22 ∧ p = 3) ∨
    (s = .Fi23 ∧ p = 3) ∨
    (s = .Fi23 ∧ p = 5) ∨
    (s = .Fi24Prime ∧ p = 3) ∨
    (s = .Fi24Prime ∧ p = 5) ∨
    (s = .Fi24Prime ∧ p = 7) ∨
    (s = .HN ∧ p = 3) ∨
    (s = .HN ∧ p = 5) ∨
    (s = .Th ∧ p = 3) ∨
    (s = .Th ∧ p = 5) ∨
    (s = .Th ∧ p = 7)

@[expose] def SporKRestBadPair (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
    (s = .M11 ∧ p = 3) ∨
    (s = .HS ∧ p = 5) ∨
    (s = .McL ∧ p = 5) ∨
    (s = .J3 ∧ p = 3) ∨
    (s = .J4 ∧ p = 11)

@[expose] def SporKRestExcPair (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  s = .Fi22 ∧ p = 5

private theorem ggSporKRestPairs_finite_sporadic (hP2 : SporadicP2Table)
    (s : TauCeti.SporadicName) : Finite (TauCeti.CFSGIndex.sporadic s).Group := by
  apply Nat.finite_of_card_ne_zero
  intro h0
  have hp : Nat.Prime 17 := by norm_num
  have hdvd : 17 ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic s).Group := by
    rw [h0]; exact dvd_zero _
  have h := hP2 s 17 hp (by norm_num) hdvd
  simp [CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicOnePair, B3SporRestPair] at h

private theorem ggSporKRestPairs_card_mulAut (K : Type*) [Group K]
    (hcen : Subgroup.center K = ⊥) :
    Nat.card (MulAut K) = Nat.card (Outer K) * Nat.card K := by
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    intro a b hab
    have h1 : b⁻¹ * a ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 : a * g * a⁻¹ = b * g * b⁻¹ := by
        have := congrArg (fun φ : MulAut K => φ g) hab
        simpa [MulAut.conj_apply] using this
      calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
        _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [h2]
        _ = (b⁻¹ * a) * g := by group
    rw [hcen, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1.symm
  have hInn : Nat.card (inner K) = Nat.card K :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hcard := (inner K).card_eq_card_quotient_mul_card_subgroup
  rw [hInn] at hcard
  exact hcard

private theorem ggSporKRestPairs_sq_dvd (K : Type*) [Group K] [Finite K]
    (hcen : Subgroup.center K = ⊥) (hO : Nat.card (Outer K) ≤ 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ^ 2 ∣ Nat.card (MulAut K)) :
    p ^ 2 ∣ Nat.card K := by
  rw [ggSporKRestPairs_card_mulAut K hcen] at h
  have hn0 : Nat.card (Outer K) ≠ 0 := Nat.card_pos.ne'
  have hcop' : Nat.Coprime p (Nat.card (Outer K)) := coprime_of_le_two hp hp2 hn0 hO
  have hcop : Nat.Coprime (p ^ 2) (Nat.card (Outer K)) := hcop'.pow_left 2
  exact hcop.dvd_of_dvd_mul_left h

private theorem ggSporKRestPairs_implication (s : TauCeti.SporadicName) (hB : s ≠ .B)
    (hM : s ≠ .M) (p : ℕ)
    (h : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicOnePair s p ∨ B3SporRestPair s p) :
    SporKRestCoverPair s p ∨ SporKRestBadPair s p ∨ SporKRestExcPair s p := by
  revert hB hM
  cases s <;>
    (intro hB hM
     first
       | exact absurd rfl hB
       | exact absurd rfl hM
       | (unfold CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicOnePair B3SporRestPair at h
          unfold SporKRestCoverPair SporKRestBadPair SporKRestExcPair
          rcases h with
            (⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩) | (⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩)
          all_goals simp_all))

theorem ggSporKRest_pairs_list (hOut : SporadicOuterLeTwo) (hP2 : SporadicP2Table)
    (s : TauCeti.SporadicName) (hB : s ≠ .B) (hM : s ≠ .M)
    (hS : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group)
    (hN : ∃ a b : (TauCeti.CFSGIndex.sporadic s).Group, a * b ≠ b * a)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ^ 2 ∣ Nat.card (MulAut (TauCeti.CFSGIndex.sporadic s).Group)) :
    SporKRestCoverPair s p ∨ SporKRestBadPair s p ∨ SporKRestExcPair s p := by
  haveI hfin : Finite (TauCeti.CFSGIndex.sporadic s).Group :=
    ggSporKRestPairs_finite_sporadic hP2 s
  have hcen : Subgroup.center (TauCeti.CFSGIndex.sporadic s).Group = ⊥ :=
    center_eq_bot_of_isSimpleGroup hN
  have hO : Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group) ≤ 2 :=
    hOut (TauCeti.CFSGIndex.sporadic s).Group hS hN s ⟨MulEquiv.refl _⟩
  have hsq : p ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic s).Group :=
    ggSporKRestPairs_sq_dvd _ hcen hO hp hp2 h
  rcases hP2 s p hp hp2 hsq with h1 | h1
  · exact ggSporKRestPairs_implication s hB hM p (Or.inl h1)
  · exact ggSporKRestPairs_implication s hB hM p (Or.inr h1)

end CFSG.StandardType.SporadicShape
