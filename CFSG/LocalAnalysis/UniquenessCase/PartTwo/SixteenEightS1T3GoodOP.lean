module

public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3GoodConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3GoodOrthPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3GoodOrthTrans
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.CGT.Foote82.T66.Basic
public import CFSG.CGT.PushingUp.BenderBridge
public import CFSG.CGT.PushingUpLit.BHS7.BlockComm
public import CFSG.CGT.PushingUpLit.BHS7.SevenThree
public import CFSG.CGT.PushingUpLit.BHS7.VFacts
public import CFSG.CGT.PushingUpLit.Glue.ModuleTrivial
public import CFSG.CGT.PushingUpLit.SolK.ModData
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.GroupTheory.SteinbergCBFTCores
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenGivenNatural
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenSplit
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.TwoGroupExtension
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Odd
public import CFSG.Holt.Centralizer
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairFacts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.FixedBlock
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightBridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightModuleAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SLModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SpModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCFoote
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.StronglyEmbedded.BenderNormalSeries
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

private lemma s16t3_dot_plusA_plusA {m : ℕ} {K : Type} [Field K] {i j : Fin m}
    (hij : i ≠ j) : plusA i ⬝ᵥ (plusM m K *ᵥ plusA j) = 0 := by
  have h1 : plusA i ⬝ᵥ (plusM m K *ᵥ Pi.single (Sum.inl j) 1) = plusA i (Sum.inr j) := by
    simpa using dot_plusM_single (K := K) (n := m) (Sum.inr j) (plusA i)
  have h2 : plusA i ⬝ᵥ (plusM m K *ᵥ Pi.single (Sum.inr j) 1) = plusA i (Sum.inl j) := by
    simpa using dot_plusM_single (K := K) (n := m) (Sum.inl j) (plusA i)
  have hsplit : plusM m K *ᵥ plusA j
      = plusM m K *ᵥ Pi.single (Sum.inl j) 1 + plusM m K *ᵥ Pi.single (Sum.inr j) 1 := by
    rw [plusA, Matrix.mulVec_add]
  rw [hsplit, dotProduct_add, h1, h2]
  simp [plusA, Pi.single_apply, hij, hij.symm]

private lemma s16t3_dot_plusA_plusB {m : ℕ} {K : Type} [Field K] {i j k : Fin m}
    (hki : k ≠ i) (hkj : k ≠ j) : plusA k ⬝ᵥ (plusM m K *ᵥ plusB i j) = 0 := by
  have h1 : plusA k ⬝ᵥ (plusM m K *ᵥ Pi.single (Sum.inl i) 1) = plusA k (Sum.inr i) := by
    simpa using dot_plusM_single (K := K) (n := m) (Sum.inr i) (plusA k)
  have h2 : plusA k ⬝ᵥ (plusM m K *ᵥ Pi.single (Sum.inl j) 1) = plusA k (Sum.inr j) := by
    simpa using dot_plusM_single (K := K) (n := m) (Sum.inr j) (plusA k)
  have h3 : plusA k ⬝ᵥ (plusM m K *ᵥ Pi.single (Sum.inr j) 1) = plusA k (Sum.inl j) := by
    simpa using dot_plusM_single (K := K) (n := m) (Sum.inl j) (plusA k)
  have hsplit : plusM m K *ᵥ plusB i j
      = plusM m K *ᵥ Pi.single (Sum.inl i) 1 + plusM m K *ᵥ Pi.single (Sum.inl j) 1
        + plusM m K *ᵥ Pi.single (Sum.inr j) 1 := by
    rw [plusB, Matrix.mulVec_add, Matrix.mulVec_add]
  rw [hsplit, dotProduct_add, dotProduct_add, h1, h2, h3]
  simp [plusA, Pi.single_apply, hki, hkj, hki.symm, hkj.symm]

private lemma s16t3_dot_plusA_plusB_same {m : ℕ} {K : Type} [Field K] [CharP K 2]
    {i j : Fin m} (hij : i ≠ j) : plusA j ⬝ᵥ (plusM m K *ᵥ plusB i j) = 0 := by
  have h1 : plusA j ⬝ᵥ (plusM m K *ᵥ Pi.single (Sum.inl i) 1) = plusA j (Sum.inr i) := by
    simpa using dot_plusM_single (K := K) (n := m) (Sum.inr i) (plusA j)
  have h2 : plusA j ⬝ᵥ (plusM m K *ᵥ Pi.single (Sum.inl j) 1) = plusA j (Sum.inr j) := by
    simpa using dot_plusM_single (K := K) (n := m) (Sum.inr j) (plusA j)
  have h3 : plusA j ⬝ᵥ (plusM m K *ᵥ Pi.single (Sum.inr j) 1) = plusA j (Sum.inl j) := by
    simpa using dot_plusM_single (K := K) (n := m) (Sum.inl j) (plusA j)
  have hsplit : plusM m K *ᵥ plusB i j
      = plusM m K *ᵥ Pi.single (Sum.inl i) 1 + plusM m K *ᵥ Pi.single (Sum.inl j) 1
        + plusM m K *ᵥ Pi.single (Sum.inr j) 1 := by
    rw [plusB, Matrix.mulVec_add, Matrix.mulVec_add]
  rw [hsplit, dotProduct_add, dotProduct_add, h1, h2, h3]
  have hsum : plusA j (Sum.inr i) + plusA j (Sum.inr j) + plusA j (Sum.inl j) = (0 : K) := by
    have h0 : plusA j (Sum.inr i) = (0 : K) := by simp [plusA, Pi.single_apply, hij, hij.symm]
    have h4 : plusA j (Sum.inr j) = (1 : K) := by simp [plusA, Pi.single_apply]
    have h5 : plusA j (Sum.inl j) = (1 : K) := by simp [plusA, Pi.single_apply]
    rw [h0, h4, h5, zero_add]
    exact CharTwo.add_self_eq_zero 1
  exact hsum

private lemma s16t3_dot_plusB_plusA {m : ℕ} {K : Type} [Field K] [CharP K 2]
    {i j : Fin m} (hij : i ≠ j) : plusB i j ⬝ᵥ (plusM m K *ᵥ plusA j) = 0 := by
  have h1 : plusB i j ⬝ᵥ (plusM m K *ᵥ Pi.single (Sum.inl j) 1) = plusB i j (Sum.inr j) := by
    simpa using dot_plusM_single (K := K) (n := m) (Sum.inr j) (plusB i j)
  have h2 : plusB i j ⬝ᵥ (plusM m K *ᵥ Pi.single (Sum.inr j) 1) = plusB i j (Sum.inl j) := by
    simpa using dot_plusM_single (K := K) (n := m) (Sum.inl j) (plusB i j)
  have hsplit : plusM m K *ᵥ plusA j
      = plusM m K *ᵥ Pi.single (Sum.inl j) 1 + plusM m K *ᵥ Pi.single (Sum.inr j) 1 := by
    rw [plusA, Matrix.mulVec_add]
  rw [hsplit, dotProduct_add, h1, h2]
  have hsum : plusB i j (Sum.inr j) + plusB i j (Sum.inl j) = (0 : K) := by
    have h3 : plusB i j (Sum.inr j) = (1 : K) := by simp [plusB, Pi.single_apply]
    have h4 : plusB i j (Sum.inl j) = (1 : K) := by simp [plusB, Pi.single_apply, hij, hij.symm]
    rw [h3, h4]
    exact CharTwo.add_self_eq_zero 1
  exact hsum

private lemma s16t3_dot_plusB_plusB_swap {m : ℕ} {K : Type} [Field K] [CharP K 2]
    {i j : Fin m} (hij : i ≠ j) : plusB i j ⬝ᵥ (plusM m K *ᵥ plusB j i) = 0 := by
  have h1 : plusB i j ⬝ᵥ (plusM m K *ᵥ Pi.single (Sum.inl j) 1) = plusB i j (Sum.inr j) := by
    simpa using dot_plusM_single (K := K) (n := m) (Sum.inr j) (plusB i j)
  have h2 : plusB i j ⬝ᵥ (plusM m K *ᵥ Pi.single (Sum.inl i) 1) = plusB i j (Sum.inr i) := by
    simpa using dot_plusM_single (K := K) (n := m) (Sum.inr i) (plusB i j)
  have h3 : plusB i j ⬝ᵥ (plusM m K *ᵥ Pi.single (Sum.inr i) 1) = plusB i j (Sum.inl i) := by
    simpa using dot_plusM_single (K := K) (n := m) (Sum.inl i) (plusB i j)
  have hsplit : plusM m K *ᵥ plusB j i
      = plusM m K *ᵥ Pi.single (Sum.inl j) 1 + plusM m K *ᵥ Pi.single (Sum.inl i) 1
        + plusM m K *ᵥ Pi.single (Sum.inr i) 1 := by
    rw [plusB, Matrix.mulVec_add, Matrix.mulVec_add]
  rw [hsplit, dotProduct_add, dotProduct_add, h1, h2, h3]
  have hsum : plusB i j (Sum.inr j) + plusB i j (Sum.inr i) + plusB i j (Sum.inl i) = (0 : K) := by
    have h4 : plusB i j (Sum.inr j) = (1 : K) := by simp [plusB, Pi.single_apply]
    have h5 : plusB i j (Sum.inr i) = (0 : K) := by simp [plusB, Pi.single_apply, hij, hij.symm]
    have h6 : plusB i j (Sum.inl i) = (1 : K) := by simp [plusB, Pi.single_apply, hij, hij.symm]
    rw [h4, h5, h6, add_zero]
    exact CharTwo.add_self_eq_zero 1
  exact hsum

theorem s16t3_good_nat_op {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 3 ≤ m) (x : Fin m ⊕ Fin m → K) :
    ∃ F : Subgroup ↥(StatedOmega (StatedQuadPlus m K)), IsPGroup 3 ↥F ∧ ¬ IsCyclic ↥F ∧
      ∀ γ ∈ F, ((γ : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).mulVec x = x := by
  classical
  haveI hprime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hchar : CharP K 2 := by
    let _ := Fintype.ofFinite K
    exact charP_of_card_eq_prime (p := 2) (Nat.card_eq_fintype_card.symm.trans hK)
  haveI hF2 : CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2 K :=
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2.of_natCard_eq_two hK
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  let i2 : Fin m := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  let a : Fin m ⊕ Fin m → K := plusA i0
  let b : Fin m ⊕ Fin m → K := plusB i0 i1
  let c : Fin m ⊕ Fin m → K := plusA i1
  let d : Fin m ⊕ Fin m → K := plusB i1 i0
  have ha : StatedQuadPlus m K a = 1 := Q_plusA i0
  have hb : StatedQuadPlus m K b = 1 := Q_plusB h01
  have hc : StatedQuadPlus m K c = 1 := Q_plusA i1
  have hd : StatedQuadPlus m K d = 1 := Q_plusB h01.symm
  have hab : a ⬝ᵥ (plusM m K *ᵥ b) = 1 := B_plus h01
  have hcd : c ⬝ᵥ (plusM m K *ᵥ d) = 1 := B_plus h01.symm
  have hac : a ⬝ᵥ (plusM m K *ᵥ c) = 0 := s16t3_dot_plusA_plusA h01
  have had : a ⬝ᵥ (plusM m K *ᵥ d) = 0 := s16t3_dot_plusA_plusB_same h01.symm
  have hbc : b ⬝ᵥ (plusM m K *ᵥ c) = 0 := s16t3_dot_plusB_plusA h01
  have hbd : b ⬝ᵥ (plusM m K *ᵥ d) = 0 := s16t3_dot_plusB_plusB_swap h01
  obtain ⟨F₀, hF₀Om, hF₀p, hF₀nc, hF₀fix⟩ :=
    s16t3_exists_pair_omega isQuadWith_plus ha hb hc hd hab hcd hac had hbc hbd
  have hsa : (Pi.single (Sum.inl i2) 1 : Fin m ⊕ Fin m → K) ⬝ᵥ (plusM m K *ᵥ a) = 0 := by
    rw [single_dot_plusM (K := K) (n := m)]
    exact plusA_apply_eq_zero (i := i0) (r := Sum.inr i2)
      (by simpa [plusIdx] using h02.symm)
  have hsb : (Pi.single (Sum.inl i2) 1 : Fin m ⊕ Fin m → K) ⬝ᵥ (plusM m K *ᵥ b) = 0 := by
    rw [single_dot_plusM (K := K) (n := m)]
    exact plusB_apply_eq_zero (i := i0) (j := i1) (r := Sum.inr i2)
      (by simpa [plusIdx] using h02.symm) (by simpa [plusIdx] using h12.symm)
  have hsc : (Pi.single (Sum.inl i2) 1 : Fin m ⊕ Fin m → K) ⬝ᵥ (plusM m K *ᵥ c) = 0 := by
    rw [single_dot_plusM (K := K) (n := m)]
    exact plusA_apply_eq_zero (i := i1) (r := Sum.inr i2)
      (by simpa [plusIdx] using h12.symm)
  have hsd : (Pi.single (Sum.inl i2) 1 : Fin m ⊕ Fin m → K) ⬝ᵥ (plusM m K *ᵥ d) = 0 := by
    rw [single_dot_plusM (K := K) (n := m)]
    exact plusB_apply_eq_zero (i := i1) (j := i0) (r := Sum.inr i2)
      (by simpa [plusIdx] using h12.symm) (by simpa [plusIdx] using h02.symm)
  have hAa : plusA i2 ⬝ᵥ (plusM m K *ᵥ a) = 0 := s16t3_dot_plusA_plusA h02.symm
  have hAc : plusA i2 ⬝ᵥ (plusM m K *ᵥ c) = 0 := s16t3_dot_plusA_plusA h12.symm
  have hAb : plusA i2 ⬝ᵥ (plusM m K *ᵥ b) = 0 :=
    s16t3_dot_plusA_plusB h02.symm h12.symm
  have hAd : plusA i2 ⬝ᵥ (plusM m K *ᵥ d) = 0 :=
    s16t3_dot_plusA_plusB (i := i1) (j := i0) h12.symm h02.symm
  have hfixs : ∀ f ∈ F₀, ((f : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).mulVec (Pi.single (Sum.inl i2) 1) =
        Pi.single (Sum.inl i2) 1 :=
    fun f hf => hF₀fix _ hsa hsb hsc hsd f hf
  have hfixn : ∀ f ∈ F₀, ((f : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).mulVec (plusA i2) = plusA i2 :=
    fun f hf => hF₀fix _ hAa hAb hAc hAd f hf
  have hQ : ⇑(CFSG.LieType.Universal.Spin.quadPlus m K) = StatedQuadPlus m K :=
    CFSG.LieType.Universal.Spin.coe_quadPlus m K
  have hnd : (QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadPlus m K)).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus m K
  have hdim : 4 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have hE : ⁅TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadPlus m K),
      TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadPlus m K)⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup
        (CFSG.LieType.Universal.Spin.quadPlus m K) :=
    CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus (K := K) (n := m) hm
  by_cases hx : x = 0
  · refine s16t3_good_conj hF₀Om hF₀p hF₀nc (x₀ := (0 : Fin m ⊕ Fin m → K))
      (fun f _ => by simp) (g := 1) (Subgroup.one_mem _) ?_
    rw [hx]
    simp
  · rcases CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2.eq_zero_or_one
      (StatedQuadPlus m K x) with hQx | hQx
    · have hx0ne : (Pi.single (Sum.inl i2) 1 : Fin m ⊕ Fin m → K) ≠ 0 := by
        intro h
        have h1 := congrFun h (Sum.inl i2)
        simpa using h1
      have hxy : StatedQuadPlus m K (Pi.single (Sum.inl i2) 1) = StatedQuadPlus m K x := by
        rw [Q_single, hQx]
      obtain ⟨g, hg, hgx⟩ := s16t3_statedOmega_trans hK hQ hnd hdim hE hx0ne hx hxy
      exact s16t3_good_conj hF₀Om hF₀p hF₀nc (x₀ := Pi.single (Sum.inl i2) 1) hfixs hg hgx
    · have hx0ne : plusA i2 ≠ (0 : Fin m ⊕ Fin m → K) := by
        intro h
        have h1 := congrFun h (Sum.inl i2)
        simpa [plusA] using h1
      have hxy : StatedQuadPlus m K (plusA i2) = StatedQuadPlus m K x := by
        rw [Q_plusA, hQx]
      obtain ⟨g, hg, hgx⟩ := s16t3_statedOmega_trans hK hQ hnd hdim hE hx0ne hx hxy
      exact s16t3_good_conj hF₀Om hF₀p hF₀nc (x₀ := plusA i2) hfixn hg hgx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo