module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.HardMathSupport.Lang.TwE6Step3.SylowTorusSix
public import CFSG.LieType.SeitzGeneration.ExcTorusRankTw
public import CFSG.LieType.SeitzGeneration.ExcTwistedClasses
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.CTP.SeitzFineG2
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType

namespace ExcFrames

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge Polynomial
open scoped Matrix
open CFSG.HardMathSupport.Timmesfeld.CrossChar (sylowTorus_twistedE6_of_blocks_of_three_lt
  not_dvd_div_of_720 eq_of_three_le_degCountTw)

section TorusTw


theorem sylowTorus_twistedE6_one {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (h5 : 5 ≤ p) (hpq : ¬ p ∣ ℓ ^ f)
    (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 1) :
    SylowTorus (twistedE6RootGroup K σ) p 4 := by
  have hp3 : 3 < p := by omega
  have he' := orderOf_neg_natCast_zmod hp (by omega) hpq he
  rw [show ennola 1 = 2 by decide] at he'
  have hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6OneWord) • x =
      toMat TwistTag.E6.tag.rank twE6OneMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
    rw [wordProd_smul_eq_wordMat_mulVec, twE6One_wordMat, toMat_lmul, permLattice_E6_eq,
      Matrix.mulVec_mulVec]
  have hΦ : ∀ x : ℤ, ((cyclotomic 2 ℤ).eval (-x)).natAbs =
      ((cyclotomic 1 ℤ).eval x).natAbs := fun x => by
    rw [cyclotomic_two, cyclotomic_one, eval_add, eval_sub, eval_X, eval_one, eval_X, eval_one,
      show -x + 1 = -(x - 1) by ring, Int.natAbs_neg]
  have hdeg : ∀ d ∈ degreesE Tag.E6, 2 ∣ d → ¬ p ∣ d / 2 := by
    intro d hd hd2
    refine CFSG.LieType.SeitzGeneration.not_dvd_small hp h5 ?_
    have hd' : d ∈ [2, 5, 6, 8, 9, 12] := by simpa [degreesE] using hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'
    rcases hd' with rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | (exfalso; omega)
  have h : SylowTorus (twistedE6RootGroup K σ) p ([1, 1, 1, 1, 2, 2].count 1) :=
    sylowTorus_twistedE6_of_blocks_of_three_lt hℓ hf K hK σ hσ hp hp3 hpq _ hv
      [1, 1, 1, 1, 2, 2] twE6One_charpoly (by norm_num) twE6One_pow (Or.inr (by decide)) he he'
      hΦ (by decide) hdeg (by decide)
  exact h

theorem sylowTorus_twistedE6_two {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (h7 : 7 ≤ p) (hpq : ¬ p ∣ ℓ ^ f)
    (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 2) :
    SylowTorus (twistedE6RootGroup K σ) p 6 := by
  have hp3 : 3 < p := by omega
  have he' := orderOf_neg_natCast_zmod hp (by omega) hpq he
  rw [show ennola 2 = 1 by decide] at he'
  have hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6TwoWord) • x =
      toMat TwistTag.E6.tag.rank twE6TwoMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
    rw [wordProd_smul_eq_wordMat_mulVec, twE6Two_wordMat, toMat_lmul, permLattice_E6_eq,
      Matrix.mulVec_mulVec]
  have hΦ : ∀ x : ℤ, ((cyclotomic 1 ℤ).eval (-x)).natAbs =
      ((cyclotomic 2 ℤ).eval x).natAbs := fun x => by
    rw [cyclotomic_two, cyclotomic_one, eval_add, eval_sub, eval_X, eval_one, eval_X, eval_one,
      show -x - 1 = -(x + 1) by ring, Int.natAbs_neg]
  have h : SylowTorus (twistedE6RootGroup K σ) p ([2, 2, 2, 2, 2, 2].count 2) :=
    sylowTorus_twistedE6_of_blocks_of_three_lt hℓ hf K hK σ hσ hp hp3 hpq _ hv
      [2, 2, 2, 2, 2, 2] twE6Two_charpoly (by norm_num) twE6Two_pow (Or.inr (by decide)) he he'
      hΦ (by decide) (not_dvd_div_of_720 hp h7 (by decide)) (by decide)
  exact h

theorem orderOf_eq_one_of_four_le_card_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hpq : ¬ p ∣ ℓ ^ f)
    (hpq1 : ¬ p ∣ ℓ ^ f + 1) {A : Subgroup (twistedE6RootGroup K σ)} (hA : IsElemAbelian p A)
    (hAc : p ^ 4 ≤ Nat.card A) : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : p ^ 1 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  have hp2' : p ^ 2 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  have hp3' : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  obtain ⟨e, he⟩ : ∃ e, orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e := ⟨_, rfl⟩
  rw [he]
  by_contra hne1
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpq
  have hlt : e < p := orderOf_lt_prime hp hpq he
  have hne2 : e ≠ 2 := by
    intro h2
    rw [h2] at he
    have hx2 : (((ℓ ^ f : ℕ)) : ZMod p) ^ 2 = 1 := by
      have := pow_orderOf_eq_one (((ℓ ^ f : ℕ)) : ZMod p)
      rwa [he] at this
    have hfac : ((((ℓ ^ f : ℕ)) : ZMod p) - 1) * ((((ℓ ^ f : ℕ)) : ZMod p) + 1) = 0 := by
      have : ((((ℓ ^ f : ℕ)) : ZMod p) - 1) * ((((ℓ ^ f : ℕ)) : ZMod p) + 1) =
          (((ℓ ^ f : ℕ)) : ZMod p) ^ 2 - 1 := by ring
      rw [this, hx2, sub_self]
    rcases mul_eq_zero.1 hfac with h | h
    · rw [sub_eq_zero.1 h, orderOf_one] at he
      omega
    · refine hpq1 ((ZMod.natCast_eq_zero_iff _ _).1 ?_)
      rw [Nat.cast_add, Nat.cast_one]
      exact h
  by_cases hc : 3 ≤ degCountTw e
  · rcases eq_of_three_le_degCountTw hc with rfl | rfl | rfl
    · exact hne1 rfl
    · exact hne2 rfl
    · have h7 : 7 ≤ p := by omega
      have hT := CFSG.HardMathSupport.Lang.TwE6Step3.sylowTorus_twistedE6_six hℓ hf K hK σ hσ hp
        h7 hpq he
      have := hT.rank_le hp hA
      omega
  · by_cases h1c : degCountTw e ≤ 1
    · have hle := rankLE1_twistedE6 hℓ hf K hK σ hσ hp hpq (by rw [he]; exact h1c) A hA
      rw [pow_one] at hp1
      omega
    · have h2c : degCountTw e = 2 := by omega
      rcases degCountTw_eq_two h2c with rfl | rfl
      · have hle := (sylowTorus_twistedE6_three hℓ hf K hK σ hσ hp he).rankLE2 hp le_rfl A hA
        omega
      · have hle := (sylowTorus_twistedE6_four hℓ hf K hK σ hσ hp he).rankLE2 hp le_rfl A hA
        omega

theorem orderOf_eq_one_of_four_le_card_graphFixed {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {θ : K →+* K} (hθ : σ.toRingHom = θ) {p : ℕ}
    (hp : p.Prime) (h5 : 5 ≤ p) (hpq : ¬ p ∣ ℓ ^ f) (hpq1 : ¬ p ∣ ℓ ^ f + 1)
    {A : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K θ)} (hA : IsElemAbelian p A)
    (hAc : p ^ 4 ≤ Nat.card A) : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 1 := by
  subst hθ
  exact orderOf_eq_one_of_four_le_card_twistedE6 hℓ hf K hK σ hσ hp h5 hpq hpq1 hA hAc

end TorusTw

section DataTw


theorem sylowData_twistedE6_one {f p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (he : orderOf (((2 ^ f : ℕ)) : ZMod p) = 1) :
    ∀ f₀ : ℕ, 1 ≤ f₀ → ∀ (K₀ : Type) [Field K₀] [Finite K₀], Nat.card K₀ = (2 ^ f₀) ^ 2 →
      ∀ σ₀ : K₀ ≃+* K₀, (∀ c, σ₀ c = c ^ 2 ^ f₀) →
        ((2 ^ f₀ : ℕ) : ZMod p) = ((2 ^ f : ℕ) : ZMod p) →
          SylowTorus ↥(twistedE6RootGroup K₀ σ₀) p 4 := by
  intro f₀ hf₀ K₀ _ _ hK₀ σ₀ hσ₀ hres
  have : Fact p.Prime := ⟨hp⟩
  have hx : ((2 ^ f₀ : ℕ) : ZMod p) = 1 := by
    rw [hres]
    exact orderOf_eq_one_iff.1 he
  have hpq₀ : ¬ p ∣ 2 ^ f₀ := fun hd => by
    have h0 := (ZMod.natCast_eq_zero_iff _ _).2 hd
    rw [hx] at h0
    exact one_ne_zero h0
  exact sylowTorus_twistedE6_one Nat.prime_two hf₀ K₀ hK₀ σ₀ hσ₀ hp h5 hpq₀
    (by rw [hres]; exact he)

theorem sylowData_twistedE6_two {f p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p)
    (he : orderOf (((2 ^ f : ℕ)) : ZMod p) = 2) :
    ∀ f₀ : ℕ, 1 ≤ f₀ → ∀ (K₀ : Type) [Field K₀] [Finite K₀], Nat.card K₀ = (2 ^ f₀) ^ 2 →
      ∀ σ₀ : K₀ ≃+* K₀, (∀ c, σ₀ c = c ^ 2 ^ f₀) →
        ((2 ^ f₀ : ℕ) : ZMod p) = ((2 ^ f : ℕ) : ZMod p) →
          SylowTorus ↥(twistedE6RootGroup K₀ σ₀) p 6 := by
  intro f₀ hf₀ K₀ _ _ hK₀ σ₀ hσ₀ hres
  have hpq₀ : ¬ p ∣ 2 ^ f₀ := by
    have := not_dvd_of_orderOf_pos hp (he : orderOf (((2 ^ f : ℕ)) : ZMod p) = 2)
      (by norm_num)
    intro hd
    apply this
    have : Fact p.Prime := ⟨hp⟩
    have h0 := (ZMod.natCast_eq_zero_iff _ _).2 hd
    rw [hres] at h0
    exact (ZMod.natCast_eq_zero_iff _ _).1 h0
  exact sylowTorus_twistedE6_two Nat.prime_two hf₀ K₀ hK₀ σ₀ hσ₀ hp h7 hpq₀
    (by rw [hres]; exact he)

end DataTw

end ExcFrames

end CFSG.StandardType
