module

public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3GoodConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3GoodOrthPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3GoodOrthTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAPairOmMainA
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Bridge
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
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

private lemma s16t3_dot_single_inl {m : ℕ} {K : Type} [Field K] (i : Fin (m - 1))
    (y : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) :
    (Pi.single (Sum.inl i) 1 : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ⬝ᵥ
      (minusM m K 1 *ᵥ y) = y (Sum.inr (Sum.inl i)) := by
  rw [single_dotProduct, one_mul]
  simpa [minusEmb] using minusM_mulVec_emb (n := m) (b := 1) y (Sum.inr i)

private lemma s16t3_dot_single_inr {m : ℕ} {K : Type} [Field K] (i : Fin (m - 1))
    (y : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) :
    (Pi.single (Sum.inr (Sum.inl i)) 1 : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ⬝ᵥ
      (minusM m K 1 *ᵥ y) = y (Sum.inl i) := by
  rw [single_dotProduct, one_mul]
  simpa [minusEmb] using minusM_mulVec_emb (n := m) (b := 1) y (Sum.inl i)

private lemma s16t3_dot_minusA_minusB {m : ℕ} {K : Type} [Field K] {i j k : Fin (m - 1)}
    (hij : i ≠ j) (hik : i ≠ k) :
    minusA m K i ⬝ᵥ (minusM m K 1 *ᵥ minusB m K j k) = 0 := by
  simp only [minusA, minusB]
  simp only [dotProduct_add, add_dotProduct, Matrix.mulVec_add, s16t3_dot_single_inl,
    s16t3_dot_single_inr, Pi.single_apply]
  simp [hij, hik]

theorem s16t3_good_nat_om {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 4 ≤ m) {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (x : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) :
    ∃ F : Subgroup ↥(StatedOmega (StatedQuadMinus m K b c)), IsPGroup 3 ↥F ∧ ¬ IsCyclic ↥F ∧
      ∀ γ ∈ F, ((γ : Matrix.GeneralLinearGroup (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) :
        Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).mulVec
          x = x := by
  classical
  haveI hprime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hchar : CharP K 2 := by
    let _ := Fintype.ofFinite K
    exact charP_of_card_eq_prime (p := 2) (Nat.card_eq_fintype_card.symm.trans hK)
  haveI hF2 : CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2 K :=
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2.of_natCard_eq_two hK
  have hc : c = 1 := by
    apply CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2.eq_one_of_ne_zero
    intro hc0
    apply hbc 0
    rw [hc0]
    ring
  obtain rfl : c = 1 := hc
  have hb : b = 1 := by
    apply CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2.eq_one_of_ne_zero
    intro hb0
    apply hbc 1
    rw [hb0, one_pow, zero_mul, add_zero]
    exact CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2.one_add_one
  obtain rfl : b = 1 := hb
  let i0 : Fin (m - 1) := ⟨0, by omega⟩
  let i1 : Fin (m - 1) := ⟨1, by omega⟩
  let i2 : Fin (m - 1) := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  let a : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K := minusA m K i0
  let b : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K := minusB m K i0 i1
  let c : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K := minusA m K i1
  let d : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K := minusB m K i1 i0
  have hd_eq : d = s16c13bcA_minusD m K i0 i1 := by
    change minusB m K i1 i0 = s16c13bcA_minusD m K i0 i1
    simp only [minusB, s16c13bcA_minusD]
    abel
  have ha : StatedQuadMinus m K 1 1 a = 1 := by
    simpa [a] using Q_minusA (n := m) (1 : K) (1 : K) i0
  have hb : StatedQuadMinus m K 1 1 b = 1 := by
    simpa [b] using Q_minusB (n := m) (1 : K) (1 : K) h01
  have hc : StatedQuadMinus m K 1 1 c = 1 := by
    simpa [c] using Q_minusA (n := m) (1 : K) (1 : K) i1
  have hd : StatedQuadMinus m K 1 1 d = 1 := by
    rw [hd_eq]
    exact s16c13bcA_Q_minusD (n := m) (1 : K) (1 : K) h01
  have hab : a ⬝ᵥ (minusM m K 1 *ᵥ b) = 1 := by
    simpa [a, b] using B_minusB (n := m) (1 : K) h01
  have hcd : c ⬝ᵥ (minusM m K 1 *ᵥ d) = 1 := by
    rw [hd_eq]
    simpa [c] using s16c13bcA_B_minusD (n := m) (1 : K) h01
  have hac : a ⬝ᵥ (minusM m K 1 *ᵥ c) = 0 := by
    simpa [a, c] using s16c13bcA_dot_minusA_minusA (n := m) (1 : K) h01
  have had : a ⬝ᵥ (minusM m K 1 *ᵥ d) = 0 := by
    rw [hd_eq]
    simpa [a] using s16c13bcA_dot_minusA_minusD (n := m) (1 : K) h01
  have h_bc : b ⬝ᵥ (minusM m K 1 *ᵥ c) = 0 := by
    simpa [b, c] using s16c13bcA_dot_minusB_minusA (n := m) (1 : K) h01
  have hbd : b ⬝ᵥ (minusM m K 1 *ᵥ d) = 0 := by
    rw [hd_eq]
    simpa [b] using s16c13bcA_dot_minusB_minusD (n := m) (1 : K) h01
  have hQ : IsQuadWith (StatedQuadMinus m K 1 1) (minusM m K 1) :=
    isQuadWith_minus (n := m) (1 : K) (1 : K)
  obtain ⟨F₀, hF₀Om, hF₀p, hF₀nc, hF₀fix⟩ :=
    s16t3_exists_pair_omega (Q := StatedQuadMinus m K 1 1) (M := minusM m K 1)
      (a := a) (b := b) (c := c) (d := d) hQ ha hb hc hd hab hcd hac had h_bc hbd
  have hsa : (Pi.single (Sum.inl i2) 1 : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ⬝ᵥ
      (minusM m K 1 *ᵥ a) = 0 := by
    rw [s16t3_dot_single_inl (i := i2) (y := a)]
    simpa [a, minusEmb] using minusA_apply_eq_zero (n := m) (i := i0) (r := Sum.inr i2)
      (by simpa [minusIdx] using h02.symm)
  have hsb : (Pi.single (Sum.inl i2) 1 : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ⬝ᵥ
      (minusM m K 1 *ᵥ b) = 0 := by
    rw [s16t3_dot_single_inl (i := i2) (y := b)]
    simpa [b, minusEmb] using s16c13bcA_minusB_apply_eq_zero (n := m) (i := i0) (j := i1)
      (r := Sum.inr i2) (by simpa [minusIdx] using h02.symm)
      (by simpa [minusIdx] using h12.symm)
  have hsc : (Pi.single (Sum.inl i2) 1 : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ⬝ᵥ
      (minusM m K 1 *ᵥ c) = 0 := by
    rw [s16t3_dot_single_inl (i := i2) (y := c)]
    simpa [c, minusEmb] using minusA_apply_eq_zero (n := m) (i := i1) (r := Sum.inr i2)
      (by simpa [minusIdx] using h12.symm)
  have hsd : (Pi.single (Sum.inl i2) 1 : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ⬝ᵥ
      (minusM m K 1 *ᵥ d) = 0 := by
    rw [s16t3_dot_single_inl (i := i2) (y := d)]
    simpa [d, minusEmb] using s16c13bcA_minusB_apply_eq_zero (n := m) (i := i1) (j := i0)
      (r := Sum.inr i2) (by simpa [minusIdx] using h12.symm)
      (by simpa [minusIdx] using h02.symm)
  have hAa : minusA m K i2 ⬝ᵥ (minusM m K 1 *ᵥ a) = 0 := by
    simpa [a] using s16c13bcA_dot_minusA_minusA (n := m) (1 : K) h02.symm
  have hAb : minusA m K i2 ⬝ᵥ (minusM m K 1 *ᵥ b) = 0 := by
    simpa [b] using s16t3_dot_minusA_minusB (m := m) (K := K) (i := i2) (j := i0) (k := i1)
      h02.symm h12.symm
  have hAc : minusA m K i2 ⬝ᵥ (minusM m K 1 *ᵥ c) = 0 := by
    simpa [c] using s16c13bcA_dot_minusA_minusA (n := m) (1 : K) h12.symm
  have hAd : minusA m K i2 ⬝ᵥ (minusM m K 1 *ᵥ d) = 0 := by
    simpa [d] using s16t3_dot_minusA_minusB (m := m) (K := K) (i := i2) (j := i1) (k := i0)
      h12.symm h02.symm
  have hfixs : ∀ f ∈ F₀, ((f : Matrix.GeneralLinearGroup
      (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) :
      Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).mulVec
        (Pi.single (Sum.inl i2) 1) = Pi.single (Sum.inl i2) 1 :=
    fun f hf => hF₀fix _ hsa hsb hsc hsd f hf
  have hfixn : ∀ f ∈ F₀, ((f : Matrix.GeneralLinearGroup
      (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) :
      Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).mulVec
        (minusA m K i2) = minusA m K i2 :=
    fun f hf => hF₀fix _ hAa hAb hAc hAd f hf
  have hQcoe : ⇑(CFSG.LieType.Universal.Spin.quadMinus m K 1 1) =
      StatedQuadMinus m K 1 1 :=
    CFSG.LieType.Universal.Spin.coe_quadMinus (n := m) (K := K) 1 1
  have hnd : (QuadraticMap.polarBilin
      (CFSG.LieType.Universal.Spin.quadMinus m K 1 1)).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite
      (n := m) (K := K) hbc
  have hdim : 4 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
    rw [CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.finrank_minus (m := m) (K := K)
      (by omega)]
    omega
  have hE : ⁅TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadMinus m K 1 1),
      TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadMinus m K 1 1)⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup
        (CFSG.LieType.Universal.Spin.quadMinus m K 1 1) :=
    commutator_orthogonalGroup_eq_of_isometry_minus
      (Q := CFSG.LieType.Universal.Spin.quadMinus m K 1 1) (m := m) (by omega)
      (LinearEquiv.refl K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)) (fun _ => rfl)
  by_cases hx : x = 0
  · refine s16t3_good_conj hF₀Om hF₀p hF₀nc
      (x₀ := (0 : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)) (fun f _ => by simp) (g := 1)
      (Subgroup.one_mem _) ?_
    rw [hx]
    simp
  · rcases CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2.eq_zero_or_one
      (StatedQuadMinus m K 1 1 x) with hQx | hQx
    · have hx0ne : (Pi.single (Sum.inl i2) 1 : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ≠ 0 := by
        intro h
        have h1 := congrFun h (Sum.inl i2)
        simpa using h1
      have hxy : StatedQuadMinus m K 1 1 (Pi.single (Sum.inl i2) 1) =
          StatedQuadMinus m K 1 1 x := by
        rw [show StatedQuadMinus m K 1 1 (Pi.single (Sum.inl i2) 1) = 0 from by
          simpa [minusEmb] using Q_minusSingle (n := m) (1 : K) (1 : K) (Sum.inl i2), hQx]
      obtain ⟨g, hg, hgx⟩ := s16t3_statedOmega_trans hK hQcoe hnd hdim hE hx0ne hx hxy
      exact s16t3_good_conj hF₀Om hF₀p hF₀nc (x₀ := Pi.single (Sum.inl i2) 1) hfixs hg hgx
    · have hx0ne : minusA m K i2 ≠ (0 : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
        intro h
        have h1 := congrFun h (Sum.inl i2)
        simpa [minusA] using h1
      have hxy : StatedQuadMinus m K 1 1 (minusA m K i2) = StatedQuadMinus m K 1 1 x := by
        rw [show StatedQuadMinus m K 1 1 (minusA m K i2) = 1 from
          Q_minusA (n := m) (1 : K) (1 : K) i2, hQx]
      obtain ⟨g, hg, hgx⟩ := s16t3_statedOmega_trans hK hQcoe hnd hdim hE hx0ne hx hxy
      exact s16t3_good_conj hF₀Om hF₀p hF₀nc (x₀ := minusA m K i2) hfixn hg hgx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
