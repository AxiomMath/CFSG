module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldTwist
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import CFSG.RankThree.PartOne.KC.OrthogonalPrimarySummands

public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.Assembly.Subnormal
public import CFSG.RankThree.SteinbergR3ECALinearPrimaryBlocks
public import CFSG.RankThree.PartOne.KC.LinearPlaneBlocks
public import CFSG.LieType.SeitzGeneration.OrthManyPieces
public import CFSG.LocalAnalysis.StandardType.GGF4N2RootCharts
public import CFSG.RankThree.PartOne.FOC.PSLDecomp
public import CFSG.RankThree.PartOne.KF.R6LeviA
public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusBlockAuxComp
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UGroup
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearGen
public import CFSG.LieType.Steinberg.CentralExt.SUThreeOrder

public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock

public import CFSG.RankThree.PartOne.KC.LinearCAAdapter
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.GH74.GLS.Stage2.Final.LayerFDerive
public import CFSG.GH74.Statements
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.SeitzGeneration.UnitaryNonsplit
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenE6
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTField
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldNormalizePSL
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterPSUPSp
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFieldComponentBasic
public import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigiditySelfDual
public import CFSG.RankThree.PartOne.KF.R7Final
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.KFOUT3.KtyD8
public import CFSG.RankThree.PartOne.KFOUT3.KtyWCtx
public import CFSG.RankThree.PartOne.S12.InputsKF2
public import CFSG.RankThree.PartOne.S12.Sec1322Inputs
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.StandardType

open CFSG
open Polynomial
open CFSG.RankThree.CALinearPrimary
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCUnitary
open scoped BigOperators

noncomputable section

def sl6End (F : Type) [Field F] (a : Matrix.SpecialLinearGroup (Fin 6) F) :
    Module.End F (Fin 6 → F) :=
  ((slGL 6 F a : LinearMap.GeneralLinearGroup F (Fin 6 → F)) : Module.End F (Fin 6 → F))

private lemma sl6End_pow_five {F : Type} [Field F]
    {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5) :
    sl6End F a ^ 5 = 1 := by
  have ha5 : a ^ 5 = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  have h1 : (slGL 6 F a) ^ 5 = 1 := by
    rw [← map_pow, ha5, map_one]
  simpa [sl6End] using congrArg
    (fun u : LinearMap.GeneralLinearGroup F (Fin 6 → F) =>
      (u : Module.End F (Fin 6 → F))) h1

private lemma sl6End_minpoly_dvd {F : Type} [Field F]
    {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5) :
    minpoly F (sl6End F a) ∣ (X : F[X]) ^ 5 - 1 := by
  refine minpoly.dvd F (sl6End F a) ?_
  simpa [sl6End_pow_five ha] using (aeval_sub (sl6End F a) ((X : F[X]) ^ 5) 1)

private lemma zmod5_four_eq_neg_one : (4 : ZMod 5) = -1 := by decide

private lemma zmod5_neg_one_sq : (-1 : ZMod 5) ^ 2 = 1 := by decide

private lemma zmod5_neg_one_ne_one : (-1 : ZMod 5) ≠ 1 := by decide

private lemma zmod5_orderOf_four : orderOf ((4 : ℕ) : ZMod 5) = 2 := by
  have h4 : (4 : ZMod 5) = -1 := zmod5_four_eq_neg_one
  have hneg : orderOf (-1 : ZMod 5) = 2 :=
    orderOf_eq_prime zmod5_neg_one_sq zmod5_neg_one_ne_one
  rw [show ((4 : ℕ) : ZMod 5) = (4 : ZMod 5) by norm_num, h4, hneg]

private lemma five_ne_zero (F : Type) [Field F] [CharP F 2] : (5 : F) ≠ 0 :=
  CharP.cast_ne_zero_of_ne_of_prime (R := F) (p := 2) (q := 5) (by norm_num) (by norm_num)

private lemma sl6End_squarefree {F : Type} [Field F] [CharP F 2]
    {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5) :
    Squarefree (minpoly F (sl6End F a)) := by
  have ha5 : a ^ 5 = 1 := by
    rw [← ha]
    exact pow_orderOf_eq_one a
  simpa [sl6End] using
    CFSG.RankThree.CALinearPrimary.squarefree_minpoly_slGL
      (n := 6) (k := F) (p := 5) (five_ne_zero F) ha5

private lemma primaryMultiplicity_pos {F : Type} [Field F] [CharP F 2]
    {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5)
    {h : F[X]} (hh : h ∈ primaryFactors (sl6End F a)) :
    0 < primaryMultiplicity (sl6End F a) h := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hsq : Squarefree (minpoly F (sl6End F a)) := sl6End_squarefree ha
  have hne : primaryComponent (sl6End F a) h ≠ ⊥ := primaryComponent_ne_bot hsq hh
  haveI : Nontrivial (primaryComponent (sl6End F a) h) :=
    Submodule.nontrivial_iff_ne_bot.mpr hne
  exact Module.finrank_pos

private lemma exists_primaryMultiplicity_ge_two {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5) :
    ∃ h ∈ primaryFactors (sl6End F a),
      2 ≤ primaryMultiplicity (sl6End F a) h := by
  classical
  let S := primaryFactors (sl6End F a)
  have hsq : Squarefree (minpoly F (sl6End F a)) := sl6End_squarefree ha
  have hsum := finrank_eq_sum_degree_mul_multiplicity (K := F) (V := Fin 6 → F)
    (x := sl6End F a) hsq
  have hsum' : 6 = ∑ b : S,
      (b : F[X]).natDegree * primaryMultiplicity (sl6End F a) (b : F[X]) := by
    simpa [S, Module.finrank_fin_fun] using hsum
  by_contra hcon
  push Not at hcon
  have hle : (∑ b : S,
      (b : F[X]).natDegree * primaryMultiplicity (sl6End F a) (b : F[X])) ≤
      ∑ b : S, (b : F[X]).natDegree := by
    refine Finset.sum_le_sum fun b _ => ?_
    have hm : primaryMultiplicity (sl6End F a) (b : F[X]) ≤ 1 := by
      have := hcon b b.2
      omega
    simpa using Nat.mul_le_mul_left (b : F[X]).natDegree hm
  have hprod : (∏ b : S, (b : F[X])) = minpoly F (sl6End F a) := by
    rw [Finset.prod_coe_sort (s := S) (f := fun b : F[X] => b)]
    simpa [S] using prod_primaryFactors (K := F) (V := Fin 6 → F)
      (x := sl6End F a) hsq
  have hdeg_sum : (∑ b : S, (b : F[X]).natDegree) = (minpoly F (sl6End F a)).natDegree := by
    rw [← hprod, natDegree_prod]
    intro b _
    exact (monic_of_mem_primaryFactors b.2).ne_zero
  have hmin_le5 : (minpoly F (sl6End F a)).natDegree ≤ 5 := by
    have hdvd : minpoly F (sl6End F a) ∣ (X : F[X]) ^ 5 - 1 := sl6End_minpoly_dvd ha
    have hnat : ((X : F[X]) ^ 5 - 1).natDegree = 5 := by
      simpa using (natDegree_X_pow_sub_C (R := F) (n := 5) (r := 1))
    have hzero : ((X : F[X]) ^ 5 - 1) ≠ 0 := by
      intro h0
      rw [h0, natDegree_zero] at hnat
      norm_num at hnat
    exact (natDegree_le_of_dvd hdvd hzero).trans_eq hnat
  have h6le5 : 6 ≤ 5 := by
    calc
      6 = ∑ b : S,
          (b : F[X]).natDegree * primaryMultiplicity (sl6End F a) (b : F[X]) := hsum'
      _ ≤ ∑ b : S, (b : F[X]).natDegree := hle
      _ = (minpoly F (sl6End F a)).natDegree := hdeg_sum
      _ ≤ 5 := hmin_le5
  omega

private lemma primaryFactor_degree_of_orderFive {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5)
    {h : F[X]} (hh : h ∈ primaryFactors (sl6End F a)) :
    h = X - 1 ∨ (h ≠ X - 1 ∧ h.natDegree = 2) := by
  by_cases h1 : h = X - 1
  · exact Or.inl h1
  · right
    refine ⟨h1, ?_⟩
    have hirr : Irreducible h := irreducible_of_mem_primaryFactors hh
    have hmon : h.Monic := monic_of_mem_primaryFactors hh
    have hdvd : h ∣ (X : F[X]) ^ 5 - 1 :=
      (mem_primaryFactors.mp hh).2.2.trans (sl6End_minpoly_dvd ha)
    have hpl : (5 : ℕ) ≠ ringChar F := by
      rw [ringChar.eq (R := F) 2]
      norm_num
    have hord : orderOf ((Nat.card F : ℕ) : ZMod 5) = 2 := by
      rw [hF, zmod5_orderOf_four]
    calc
      h.natDegree =
          orderOf ((Nat.card F : ℕ) : ZMod 5) :=
        CFSG.LieType.SeitzGeneration.natDegree_eq_orderOf_of_dvd
          (K := F) (p := 5) (by norm_num) hpl hmon hirr hdvd h1
      _ = 2 := hord

def sl6FixedMultiplicity (F : Type) [Field F]
    (a : Matrix.SpecialLinearGroup (Fin 6) F) : ℕ := by
  classical
  exact ∑ b : primaryFactors (sl6End F a),
    if (b : F[X]) = X - 1 then primaryMultiplicity (sl6End F a) (b : F[X]) else 0

def sl6QuadraticMultiplicity (F : Type) [Field F]
    (a : Matrix.SpecialLinearGroup (Fin 6) F) : ℕ := by
  classical
  exact ∑ b : primaryFactors (sl6End F a),
    if (b : F[X]) ≠ X - 1 then primaryMultiplicity (sl6End F a) (b : F[X]) else 0

private lemma sl6QuadraticMultiplicity_pos {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5) :
    0 < sl6QuadraticMultiplicity F a := by
  classical
  let S := primaryFactors (sl6End F a)
  let m := primaryMultiplicity (sl6End F a)
  have hsq : Squarefree (minpoly F (sl6End F a)) := sl6End_squarefree ha
  have hprod : (∏ b : S, (b : F[X])) = minpoly F (sl6End F a) := by
    rw [Finset.prod_coe_sort (s := S) (f := fun b : F[X] => b)]
    simpa [S] using prod_primaryFactors (K := F) (V := Fin 6 → F)
      (x := sl6End F a) hsq
  by_contra hMpos
  have hM0 : sl6QuadraticMultiplicity F a = 0 := by omega
  have hno : ∀ b : S, (b : F[X]) = X - 1 := by
    intro b
    by_contra hb
    have htermpos : 0 < (if (b : F[X]) ≠ X - 1 then m (b : F[X]) else 0) := by
      simpa [hb] using primaryMultiplicity_pos ha b.2
    have hle : (if (b : F[X]) ≠ X - 1 then m (b : F[X]) else 0) ≤
        sl6QuadraticMultiplicity F a := by
      simpa [sl6QuadraticMultiplicity, S, m] using
        (Finset.single_le_sum (s := (Finset.univ : Finset S))
          (f := fun b : S => if (b : F[X]) ≠ X - 1 then m (b : F[X]) else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))
    omega
  have hdeg_sum : (∑ b : S, (b : F[X]).natDegree) =
      (minpoly F (sl6End F a)).natDegree := by
    rw [← hprod, natDegree_prod]
    intro b _
    exact (monic_of_mem_primaryFactors b.2).ne_zero
  have hSne : S.Nonempty := by
    by_contra hSempty
    rw [Finset.not_nonempty_iff_eq_empty] at hSempty
    have hsum0 : (∑ b : S, (b : F[X]).natDegree) = 0 := by simp [hSempty]
    have hdegpos : 0 < (minpoly F (sl6End F a)).natDegree :=
      minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral (sl6End F a))
    omega
  have hsingle : S = {X - 1} := by
    refine Finset.eq_singleton_iff_nonempty_unique_mem.mpr ⟨hSne, ?_⟩
    intro b hb
    exact hno ⟨b, hb⟩
  have hprod_single : (∏ b : S, (b : F[X])) = X - 1 := by
    rw [hsingle]
    simp
  have hmin : minpoly F (sl6End F a) = X - 1 := by
    rw [← hprod, hprod_single]
  have hx1 : sl6End F a = 1 := by
    have h0 : aeval (sl6End F a) (X - 1 : F[X]) = 0 := by
      rw [← hmin]
      exact minpoly.aeval F (sl6End F a)
    simpa [sub_eq_zero] using h0
  have hgl : slGL 6 F a = 1 := Units.ext hx1
  have ha1 : a = 1 := slGL_injective (n := 6) (k := F) (by rw [hgl, map_one])
  rw [ha1, orderOf_one] at ha
  norm_num at ha

private lemma primaryFactor_card_of_orderFive {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5)
    {h : F[X]} (hh : h ∈ primaryFactors (sl6End F a)) :
    Nat.card (AdjoinRoot h) = 4 ∨ Nat.card (AdjoinRoot h) = 16 := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hcard : Nat.card (AdjoinRoot h) = Nat.card F ^ h.natDegree :=
    CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot (K := F) h
  rcases primaryFactor_degree_of_orderFive hF ha hh with h1 | ⟨hne, hdeg⟩
  · left
    have hdeg1 : (X - 1 : F[X]).natDegree = 1 := by
      simpa using natDegree_X_sub_C (1 : F)
    rw [hcard, h1, hF, hdeg1]
    norm_num
  · right
    rw [hcard, hdeg, hF]
    norm_num

theorem primaryDimensionData_of_orderFive {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5) :
    6 = sl6FixedMultiplicity F a + 2 * sl6QuadraticMultiplicity F a ∧
      sl6FixedMultiplicity F a ≤ 4 ∧
      sl6QuadraticMultiplicity F a ≤ 3 ∧
      (∀ h ∈ primaryFactors (sl6End F a), h ≠ X - 1 →
        primaryMultiplicity (sl6End F a) h ≤ 3) := by
  classical
  let S := primaryFactors (sl6End F a)
  let m := primaryMultiplicity (sl6End F a)
  have hsq : Squarefree (minpoly F (sl6End F a)) := sl6End_squarefree ha
  have hsum := finrank_eq_sum_degree_mul_multiplicity (K := F) (V := Fin 6 → F)
    (x := sl6End F a) hsq
  have hsum' : 6 = ∑ b : S,
      (b : F[X]).natDegree * m (b : F[X]) := by
    simpa [S, m, Module.finrank_fin_fun] using hsum
  have hpoint : ∀ b : S,
      (b : F[X]).natDegree * m (b : F[X]) =
        (if (b : F[X]) = X - 1 then m (b : F[X]) else 0) +
          2 * (if (b : F[X]) ≠ X - 1 then m (b : F[X]) else 0) := by
    intro b
    by_cases hp : (b : F[X]) = X - 1
    · have hdeg : (X - 1 : F[X]).natDegree = 1 := by
        simpa using natDegree_X_sub_C (1 : F)
      simp [hp, hdeg]
    · have hdeg : (b : F[X]).natDegree = 2 := by
        exact (primaryFactor_degree_of_orderFive hF ha b.2).resolve_left hp |>.2
      simp [hp, hdeg]
  have hsplit : 6 = (∑ b : S,
      if (b : F[X]) = X - 1 then m (b : F[X]) else 0) +
      2 * (∑ b : S, if (b : F[X]) ≠ X - 1 then m (b : F[X]) else 0) := by
    calc
      6 = ∑ b : S, (b : F[X]).natDegree * m (b : F[X]) := hsum'
      _ = ∑ b : S,
          ((if (b : F[X]) = X - 1 then m (b : F[X]) else 0) +
            2 * (if (b : F[X]) ≠ X - 1 then m (b : F[X]) else 0)) :=
            Finset.sum_congr rfl fun b _ => hpoint b
      _ = (∑ b : S, if (b : F[X]) = X - 1 then m (b : F[X]) else 0) +
          2 * (∑ b : S, if (b : F[X]) ≠ X - 1 then m (b : F[X]) else 0) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hdim : 6 = sl6FixedMultiplicity F a + 2 * sl6QuadraticMultiplicity F a := by
    simpa [sl6FixedMultiplicity, sl6QuadraticMultiplicity, S, m] using hsplit
  have hMpos : 0 < sl6QuadraticMultiplicity F a := sl6QuadraticMultiplicity_pos hF ha
  have hf4 : sl6FixedMultiplicity F a ≤ 4 := by omega
  have hMle : sl6QuadraticMultiplicity F a ≤ 3 := by omega
  refine ⟨hdim, hf4, hMle, ?_⟩
  intro h hh hne
  let b : S := ⟨h, by simpa [S] using hh⟩
  have hsingle : (if (b : F[X]) ≠ X - 1 then m (b : F[X]) else 0) ≤
      sl6QuadraticMultiplicity F a := by
    simpa [sl6QuadraticMultiplicity, S, m] using
      (Finset.single_le_sum (s := (Finset.univ : Finset S))
        (f := fun b : S => if (b : F[X]) ≠ X - 1 then m (b : F[X]) else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))
  have hbne : (b : F[X]) ≠ X - 1 := by simpa [b] using hne
  have hle : m h ≤ sl6QuadraticMultiplicity F a := by
    simpa [b, hbne] using hsingle
  exact hle.trans hMle

theorem sl6FixedMultiplicity_eq_of_fixed {F : Type} [Field F] [Finite F] [CharP F 2]
    {a : Matrix.SpecialLinearGroup (Fin 6) F} {h : F[X]}
    (hh : h ∈ primaryFactors (sl6End F a)) (hp : h = X - 1) :
    sl6FixedMultiplicity F a = primaryMultiplicity (sl6End F a) h := by
  classical
  let b0 : primaryFactors (sl6End F a) := ⟨h, hh⟩
  have hb0 : (b0 : F[X]) = X - 1 := hp
  change (Finset.sum (Finset.univ : Finset (primaryFactors (sl6End F a)))
    (fun b : primaryFactors (sl6End F a) =>
      (if (b : F[X]) = X - 1 then
        (primaryMultiplicity (sl6End F a) (b : F[X]) : ℕ) else (0 : ℕ)))) =
    primaryMultiplicity (sl6End F a) h
  have hsum : (∑ b : primaryFactors (sl6End F a),
      (if (b : F[X]) = X - 1 then
        (primaryMultiplicity (sl6End F a) (b : F[X]) : ℕ) else (0 : ℕ))) =
      (if (b0 : F[X]) = X - 1 then
        (primaryMultiplicity (sl6End F a) (b0 : F[X]) : ℕ) else (0 : ℕ)) := by
    refine Finset.sum_eq_single (s := (Finset.univ : Finset (primaryFactors (sl6End F a))))
      (f := fun b : primaryFactors (sl6End F a) =>
        (if (b : F[X]) = X - 1 then
          (primaryMultiplicity (sl6End F a) (b : F[X]) : ℕ) else (0 : ℕ))) b0 ?_ ?_
    · intro b _ hbne
      have hbne' : (b : F[X]) ≠ X - 1 := by
        intro hb
        apply hbne
        apply Subtype.ext
        rw [hb, hb0]
      simp [hbne']
    · intro hb0not
      exact (hb0not (Finset.mem_univ b0)).elim
  simpa [b0, hp] using hsum

private lemma seven_dvd_gl_centralizer_of_seven_dvd_centralizer
    {F Q : Type} [Field F] [Finite F] [CharP F 2] [Group Q] [Finite Q]
    (hF : Nat.card F = 4)
    (ψ : Matrix.SpecialLinearGroup (Fin 6) F →* Q)
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) F))
    {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5)
    {H : Subgroup Q} (hH : H ≤ Subgroup.centralizer ({ψ a} : Set Q))
    (h7 : 7 ∣ Nat.card H) :
    7 ∣ Nat.card (gl_centralizer (slGL 6 F a)) := by
  classical
  let X := Matrix.SpecialLinearGroup (Fin 6) F
  let C : Subgroup X := Subgroup.centralizer ({a} : Set X)
  let G := LinearMap.GeneralLinearGroup F (Fin 6 → F)
  let CG : Subgroup G := gl_centralizer (slGL 6 F a)
  have hrange : ψ.range = ⊤ := MonoidHom.range_eq_top.mpr hψ
  have hCeq : Subgroup.centralizer ({ψ a} : Set Q) = C.map ψ :=
    sl6_centralizer_eq_map_of_orderFive hF ψ hker hrange ha
  have hHC : H ≤ C.map ψ := hH.trans (le_of_eq hCeq)
  have h7C : 7 ∣ Nat.card C := by
    have h1 : 7 ∣ Nat.card (C.map ψ) := h7.trans (Subgroup.card_dvd_of_le hHC)
    exact h1.trans (by
      have hdvd := Subgroup.card_range_dvd (ψ.comp C.subtype)
      simpa [MonoidHom.range_comp, Subgroup.range_subtype] using hdvd)
  let ρ : C →* G := (slGL 6 F).comp C.subtype
  have hinj : Function.Injective ρ := by
    intro x y h
    apply Subtype.ext
    exact slGL_injective (n := 6) (k := F) (by simpa [ρ] using h)
  have hρle : ρ.range ≤ CG := by
    rintro _ ⟨c, rfl⟩
    change ρ c ∈ Subgroup.centralizer ({slGL 6 F a} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : Commute (c : X) a := Subgroup.mem_centralizer_singleton_iff.mp c.2
    exact hc.map (slGL 6 F)
  have hcard : Nat.card ρ.range = Nat.card C :=
    (Nat.card_congr (Equiv.ofInjective ρ hinj)).symm
  have h7range : 7 ∣ Nat.card ρ.range := by rwa [hcard]
  exact h7range.trans (Subgroup.card_dvd_of_le hρle)

private lemma natCard_blockGL_eq_generalLinear
    {F : Type} [Field F] [Finite F] {x : Module.End F (Fin 6 → F)}
    {h : F[X]} [Fact (Irreducible h)] :
    Nat.card (blockGL x h) =
      Nat.card (Matrix.GeneralLinearGroup
        (Fin (primaryMultiplicity x h)) (AdjoinRoot h)) := by
  classical
  let b : Module.Basis (Fin (primaryMultiplicity x h)) (AdjoinRoot h)
      (primaryComponent x h) :=
    Module.finBasisOfFinrankEq (AdjoinRoot h) (primaryComponent x h) rfl
  exact Nat.card_congr ((LinearMap.GeneralLinearGroup.congrLinearEquiv b.equivFun).trans
    Matrix.GeneralLinearGroup.toLin.symm).toEquiv

private lemma not_seven_dvd_card_generalLinear_small
    (E : Type) [Field E] [Finite E]
    (hE : Nat.card E = 4 ∨ Nat.card E = 16) {d : ℕ} (hd : d ≤ 2) :
    ¬ 7 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin d) E) := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  rw [Matrix.card_GL_field]
  rcases hE with h4 | h16
  · have hcard : Fintype.card E = 4 := by rwa [← Nat.card_eq_fintype_card]
    rw [hcard]
    interval_cases d <;>
      simp [Fin.prod_univ_zero, Fin.prod_univ_one, Fin.prod_univ_two] <;> norm_num
  · have hcard : Fintype.card E = 16 := by rwa [← Nat.card_eq_fintype_card]
    rw [hcard]
    interval_cases d <;>
      simp [Fin.prod_univ_zero, Fin.prod_univ_one, Fin.prod_univ_two] <;> norm_num

private lemma seven_dvd_gl_centralizer_dichotomy
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5)
    (h7 : 7 ∣ Nat.card (gl_centralizer (slGL 6 F a))) :
    sl6FixedMultiplicity F a = 4 ∨
      (sl6FixedMultiplicity F a = 0 ∧ Irreducible (minpoly F (sl6End F a)) ∧
        (minpoly F (sl6End F a)).natDegree = 2) := by
  classical
  let u : LinearMap.GeneralLinearGroup F (Fin 6 → F) := slGL 6 F a
  let x : Module.End F (Fin 6 → F) := sl6End F a
  let S := primaryFactors x
  have hsq : Squarefree (minpoly F x) := sl6End_squarefree ha
  have hsq' : Squarefree (minpoly F (u : Module.End F (Fin 6 → F))) := by
    change Squarefree (minpoly F (sl6End F a))
    exact hsq
  have hcardpi : Nat.card (gl_centralizer u) =
      ∏ b : S, Nat.card (blockGL x (b : F[X])) := by
    calc
      Nat.card (gl_centralizer u) =
          Nat.card ((b : primaryFactors (u : Module.End F (Fin 6 → F))) →
            blockGL (u : Module.End F (Fin 6 → F)) (b : F[X])) :=
        Nat.card_congr (glCentralizerEquivPi hsq').toEquiv
      _ = ∏ b : primaryFactors (u : Module.End F (Fin 6 → F)),
            Nat.card (blockGL (u : Module.End F (Fin 6 → F)) (b : F[X])) :=
        Nat.card_pi
      _ = ∏ b : S, Nat.card (blockGL x (b : F[X])) := by rfl
  have h7prod : 7 ∣ ∏ b : S, Nat.card (blockGL x (b : F[X])) := by
    rwa [hcardpi] at h7
  have h7prod' : (7 : ℕ) ∣ (Finset.univ : Finset S).prod
      (fun b : S => Nat.card (blockGL x (b : F[X]))) := by
    simpa using h7prod
  obtain ⟨b, -, h7b⟩ :=
    (Nat.prime_iff.mp (by norm_num : Nat.Prime 7)).dvd_finsetProd_iff
      (fun b : S => Nat.card (blockGL x (b : F[X]))) |>.mp h7prod'
  have hbaf : (b : F[X]) ∈ primaryFactors (sl6End F a) := by
    simpa [S, x] using b.2
  have hm3 : 3 ≤ primaryMultiplicity (sl6End F a) (b : F[X]) := by
    by_contra hlt
    have hmle : primaryMultiplicity (sl6End F a) (b : F[X]) ≤ 2 := by omega
    have hEcard : Nat.card (AdjoinRoot (b : F[X])) = 4 ∨
        Nat.card (AdjoinRoot (b : F[X])) = 16 :=
      primaryFactor_card_of_orderFive hF ha hbaf
    have hnot : ¬ 7 ∣ Nat.card (Matrix.GeneralLinearGroup
        (Fin (primaryMultiplicity (sl6End F a) (b : F[X])))
        (AdjoinRoot (b : F[X]))) :=
      not_seven_dvd_card_generalLinear_small (AdjoinRoot (b : F[X])) hEcard hmle
    have hblock := natCard_blockGL_eq_generalLinear
      (x := sl6End F a) (h := (b : F[X]))
    have h7b' : 7 ∣ Nat.card (blockGL (sl6End F a) (b : F[X])) := by
      simpa [x] using h7b
    exact hnot (by rwa [hblock] at h7b')
  have hdata := primaryDimensionData_of_orderFive hF ha
  by_cases hb1 : (b : F[X]) = X - 1
  · left
    have hfixeq : sl6FixedMultiplicity F a =
        primaryMultiplicity (sl6End F a) (b : F[X]) :=
      sl6FixedMultiplicity_eq_of_fixed hbaf hb1
    have hdim := hdata.1
    rw [hfixeq] at hdim
    have hle4 := hdata.2.1
    rw [hfixeq] at hle4
    omega
  · right
    have hm_eq3 : primaryMultiplicity (sl6End F a) (b : F[X]) = 3 := by
      have hle := hdata.2.2.2 (b : F[X]) hbaf hb1
      omega
    have hM3 : sl6QuadraticMultiplicity F a = 3 := by
      have hMle := hdata.2.2.1
      have hsingle : primaryMultiplicity (sl6End F a) (b : F[X]) ≤
          sl6QuadraticMultiplicity F a := by
        have h := Finset.single_le_sum (s := (Finset.univ : Finset S))
          (f := fun c : S => if (c : F[X]) ≠ X - 1 then
            primaryMultiplicity x (c : F[X]) else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
        simpa [sl6QuadraticMultiplicity, S, x, hb1] using h
      omega
    have hfixed0 : sl6FixedMultiplicity F a = 0 := by
      have hdim := hdata.1
      omega
    have hpf : primaryFactors (sl6End F a) = {(b : F[X])} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hbaf, ?_⟩
      intro c hc
      by_contra hcb
      by_cases hc1 : c = X - 1
      · have hfix := sl6FixedMultiplicity_eq_of_fixed hc hc1
        have hpos := primaryMultiplicity_pos ha hc
        rw [hfixed0] at hfix
        omega
      · let cS : S := ⟨c, by simpa [x] using hc⟩
        have hbne : b ≠ cS := by
          intro h
          apply hcb
          exact (congrArg Subtype.val h).symm
        have hpair : primaryMultiplicity (sl6End F a) (b : F[X]) +
            primaryMultiplicity (sl6End F a) c ≤ sl6QuadraticMultiplicity F a := by
          have hsub : ({b, cS} : Finset S) ⊆ Finset.univ := Finset.subset_univ _
          have hsumle := Finset.sum_le_sum_of_subset_of_nonneg
            (s := ({b, cS} : Finset S)) (t := Finset.univ)
            (f := fun d : S => if (d : F[X]) ≠ X - 1 then
              primaryMultiplicity x (d : F[X]) else 0)
            hsub (fun _ _ _ => Nat.zero_le _)
          rw [Finset.sum_pair hbne] at hsumle
          simpa [sl6QuadraticMultiplicity, S, x, hb1, hc1, cS] using hsumle
        have hposc : 0 < primaryMultiplicity (sl6End F a) c :=
          primaryMultiplicity_pos ha hc
        omega
    have hprod : (∏ c : primaryFactors (sl6End F a), (c : F[X])) =
        minpoly F (sl6End F a) := by
      rw [Finset.prod_coe_sort (s := primaryFactors (sl6End F a))
        (f := fun c : F[X] => c)]
      exact prod_primaryFactors (K := F) (V := Fin 6 → F) (x := sl6End F a) hsq
    have hsingle : (∏ c : primaryFactors (sl6End F a), (c : F[X])) =
        (b : F[X]) := by
      refine Finset.prod_eq_single
        (s := (Finset.univ : Finset (primaryFactors (sl6End F a))))
        (f := fun c : primaryFactors (sl6End F a) => (c : F[X])) b ?_ ?_
      · intro c _ hcb'
        have hc : (c : F[X]) ∈ ({(b : F[X])} : Finset F[X]) := by
          rw [← hpf]
          exact c.2
        exact absurd (by simpa using hc) hcb'
      · intro hbnot
        exact absurd (Finset.mem_univ b) hbnot
    have hmin : minpoly F (sl6End F a) = (b : F[X]) := hprod.symm.trans hsingle
    refine ⟨hfixed0, ?_, ?_⟩
    · rw [hmin]
      exact irreducible_of_mem_primaryFactors b.2
    · rw [hmin]
      exact (primaryFactor_degree_of_orderFive hF ha hbaf).resolve_left hb1 |>.2

theorem sl6_fixedMultiplicity_eq_four_or_irreducible_minpoly_of_seven_dvd
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) {a : Matrix.SpecialLinearGroup (Fin 6) F}
    (ha : orderOf a = 5)
    (h7 : 7 ∣ Nat.card (Subgroup.centralizer
      ({a} : Set (Matrix.SpecialLinearGroup (Fin 6) F)))) :
    sl6FixedMultiplicity F a = 4 ∨
      (sl6FixedMultiplicity F a = 0 ∧ Irreducible (minpoly F (sl6End F a)) ∧
        (minpoly F (sl6End F a)).natDegree = 2) := by
  classical
  let X := Matrix.SpecialLinearGroup (Fin 6) F
  have h7gl : 7 ∣ Nat.card (gl_centralizer (slGL 6 F a)) :=
    seven_dvd_gl_centralizer_of_seven_dvd_centralizer hF (MonoidHom.id X)
      Function.surjective_id (by rw [MonoidHom.ker_id]; exact bot_le) ha
      (H := Subgroup.centralizer ({a} : Set X)) le_rfl h7
  exact seven_dvd_gl_centralizer_dichotomy hF ha h7gl

theorem exists_primaryBlock_component_of_orderFive {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5) :
    ∃ (h : F[X]) (H : Subgroup (Matrix.SpecialLinearGroup (Fin 6) F)),
      h ∈ primaryFactors (sl6End F a) ∧
      2 ≤ primaryMultiplicity (sl6End F a) h ∧
      (Nat.card (AdjoinRoot h) = 4 ∨ Nat.card (AdjoinRoot h) = 16) ∧
      ((h = X - 1 ∧ primaryMultiplicity (sl6End F a) h ≤ 4) ∨
        (h ≠ X - 1 ∧ primaryMultiplicity (sl6End F a) h ≤ 3)) ∧
      H = (linearSpecialBlock (slGL 6 F a) h).comap (slGL 6 F) ∧
      CFSG.Assembly.IsComponentOf H
        (Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin 6) F))) := by
  classical
  obtain ⟨h, hh, hm⟩ := exists_primaryMultiplicity_ge_two hF ha
  let B : Subgroup (LinearMap.GeneralLinearGroup F (Fin 6 → F)) :=
    linearSpecialBlock (slGL 6 F a) h
  let H : Subgroup (Matrix.SpecialLinearGroup (Fin 6) F) := B.comap (slGL 6 F)
  let C : Subgroup (Matrix.SpecialLinearGroup (Fin 6) F) :=
    Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin 6) F))
  have hsq : Squarefree (minpoly F (sl6End F a)) := sl6End_squarefree ha
  have hsq' : Squarefree (minpoly F ((slGL 6 F a :
      LinearMap.GeneralLinearGroup F (Fin 6 → F)) : Module.End F (Fin 6 → F))) := by
    simpa [sl6End] using hsq
  have hcard : Nat.card (AdjoinRoot h) = 4 ∨ Nat.card (AdjoinRoot h) = 16 :=
    primaryFactor_card_of_orderFive hF ha hh
  have hgood : 3 ≤ primaryMultiplicity (sl6End F a) h ∨
      (2 ≤ primaryMultiplicity (sl6End F a) h ∧ 4 ≤ Nat.card (AdjoinRoot h)) := by
    right
    refine ⟨hm, ?_⟩
    rcases hcard with h4 | h16 <;> omega
  have hBq : CFSG.IsQuasisimple B := by
    exact CFSG.RankThree.CALinearPrimary.isQuasisimple_linearSpecialBlock
      (x := slGL 6 F a) (V := Fin 6 → F) hsq' hh hgood
  have hBle : B ≤ (slGL 6 F).range :=
    CFSG.RankThree.CALinearPrimary.linearSpecialBlock_le_range_slGL
      (n := 6) (k := F) (a := a) hsq' hh
  have hmap : H.map (slGL 6 F) = B := by
    dsimp [H]
    rw [Subgroup.map_comap_eq, inf_eq_right]
    exact hBle
  let e : H ≃* B :=
    (Subgroup.equivMapOfInjective H (slGL 6 F) (slGL_injective (n := 6) (k := F))).trans
      (MulEquiv.subgroupCongr hmap)
  have hHq : CFSG.IsQuasisimple H :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hBq
  have hHle : H ≤ C := by
    dsimp [H, C, B]
    exact CFSG.RankThree.CALinearPrimary.comap_linearSpecialBlock_le_centralizer
      (n := 6) (k := F) (a := a) (h := h)
  have hCnorm : C ≤ Subgroup.normalizer H := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact CFSG.RankThree.CALinearPrimary.conj_mem_comap_linearSpecialBlock
        (n := 6) (k := F) (a := a) (h := h) hc hn
    · intro hn
      have hc' : c⁻¹ ∈ C := C.inv_mem hc
      have h := CFSG.RankThree.CALinearPrimary.conj_mem_comap_linearSpecialBlock
        (n := 6) (k := F) (a := a) (h := h) hc' hn
      dsimp [H]
      simpa [mul_assoc] using h
  have hHnormalC : (H.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHle).mpr hCnorm
  have hHsub : CFSG.Assembly.IsSubnormal H C :=
    (CFSG.Assembly.IsSubnormal.iff_subgroupOf hHle).mpr hHnormalC.isSubnormal
  have hHqA : CFSG.Assembly.IsQuasisimple H :=
    ⟨hHq.1.commutator_eq_top, hHq.2.1⟩
  have hdata := primaryDimensionData_of_orderFive hF ha
  rcases hdata with ⟨hdim, hf4, hMle, hquad⟩
  have hbound : (h = X - 1 ∧ primaryMultiplicity (sl6End F a) h ≤ 4) ∨
      (h ≠ X - 1 ∧ primaryMultiplicity (sl6End F a) h ≤ 3) := by
    by_cases hp : h = X - 1
    · left
      refine ⟨hp, ?_⟩
      let b : primaryFactors (sl6End F a) := ⟨h, hh⟩
      have hsingle : primaryMultiplicity (sl6End F a) h ≤ sl6FixedMultiplicity F a := by
        have hle := Finset.single_le_sum (s := (Finset.univ : Finset (primaryFactors (sl6End F a))))
          (f := fun b : primaryFactors (sl6End F a) =>
            if (b : F[X]) = X - 1 then primaryMultiplicity (sl6End F a) (b : F[X]) else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
        simpa [sl6FixedMultiplicity, b, hp] using hle
      exact hsingle.trans hf4
    · right
      exact ⟨hp, hquad h hh hp⟩
  refine ⟨h, H, hh, hm, hcard, hbound, ?_, ?_⟩
  · rfl
  · exact ⟨hHle, hHsub, hHqA⟩

end

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG
open Polynomial CFSG.RankThree.PartOne.KCPrimary

private lemma sl6End_eq_FOC {F : Type} [Field F]
    (a : Matrix.SpecialLinearGroup (Fin 6) F) :
    sl6End F a = CFSG.RankThree.PartOne.FOC.slEnd a := rfl

theorem sl6_exists_centralCover_component
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    {Q : Type} [Group Q] [Finite Q]
    (ψ : Matrix.SpecialLinearGroup (Fin 6) F →* Q)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) F))
    (hrange : ψ.range = ⊤)
    {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5)
    {H : Subgroup Q}
    (hH : CFSG.Assembly.IsComponentOf H
      (Subgroup.centralizer ({ψ a} : Set Q))) :
    ∃ K : Subgroup ↥(Subgroup.centralizer
        ({a} : Set (Matrix.SpecialLinearGroup (Fin 6) F))),
      CFSG.Assembly.IsComponentOf K ⊤ ∧
        K.map (ψ.comp (Subgroup.centralizer
          ({a} : Set (Matrix.SpecialLinearGroup (Fin 6) F))).subtype) = H := by
  classical
  let X := Matrix.SpecialLinearGroup (Fin 6) F
  let C : Subgroup X := Subgroup.centralizer ({a} : Set X)
  let CQ : Subgroup Q := Subgroup.centralizer ({ψ a} : Set Q)
  let ψC : ↥C →* Q := ψ.comp C.subtype
  have hCeq : CQ = C.map ψ :=
    CFSG.StandardType.sl6_centralizer_eq_map_of_orderFive hF ψ hker hrange ha
  have hrangeC : ψC.range = CQ := by
    dsimp [ψC]
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hCeq.symm
  have hkerC : ψC.ker ≤ Subgroup.center ↥C := by
    intro z hz
    have hz1 : ψ (z : X) = 1 := by
      have h := MonoidHom.mem_ker.mp hz
      simpa [ψC] using h
    have hzX : (z : X) ∈ Subgroup.center X := hker (MonoidHom.mem_ker.mpr hz1)
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hzX (y : X)
  have hHrange : CFSG.Assembly.IsComponentOf H ψC.range := by
    rw [hrangeC]
    exact hH
  obtain ⟨K, hK, hKmap⟩ :=
    CFSG.exists_isComponentOf_map_eq_of_ker_le_center hkerC hHrange
  exact ⟨K, hK, hKmap⟩

theorem sl6_exists_goodProjectiveBlock_of_component
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5)
    (hsqFOC : Squarefree (minpoly F (CFSG.RankThree.PartOne.FOC.slEnd a)))
    {K : Subgroup (Matrix.SpecialLinearGroup (Fin 6) F)}
    (hK : CFSG.Assembly.IsComponentOf K
      (Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin 6) F)))) :
    ∃ b : primaryFactors (CFSG.RankThree.PartOne.FOC.slEnd a),
      CFSG.RankThree.PartOne.KCLinPlane.GoodBlock b ∧
        K.map (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F) =
          CFSG.RankThree.PartOne.FOC.Qb hsqFOC b := by
  classical
  let X := Matrix.SpecialLinearGroup (Fin 6) F
  let C : Subgroup X := Subgroup.centralizer ({a} : Set X)
  have hscalars : Nat.card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 6 F) = 3 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center,
      CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 6 (by norm_num), hF]
    norm_num
  have hKprojOpen : CFSG.Open.IsComponentOf
      (K.map (QuotientGroup.mk'
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 6 F)))
      (Subgroup.centralizer
        ({(QuotientGroup.mk'
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 6 F)) a} :
          Set (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 6 F))) :=
    by
      simpa using
        (CFSG.StandardType.TableCRes.isComponentOf_map_centralizer_central
          (Z := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 6 F)
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_le_center 6 F)
          ({a} : Set X) (CFSG.Assembly.isComponentOf_iff_open.mp hK))
  have hKproj : CFSG.Assembly.IsComponentOf
      (K.map (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F))
      (Subgroup.centralizer
        ({(CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F) a} :
          Set (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 6 F))) := by
    refine CFSG.Assembly.isComponentOf_iff_open.mpr ?_
    simpa [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj] using hKprojOpen
  have hKprojRT : CFSG.RankThree.PartOne.IsComponentOf
      (Subgroup.centralizer
        ({(CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F) a} :
          Set (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 6 F)))
      (K.map (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F)) :=
    ⟨hKproj.1,
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hKproj.2.2,
      (CFSG.Assembly.IsSubnormal.iff_subgroupOf hKproj.1).mp hKproj.2.1⟩
  have hZ : ¬ 5 ∣ Nat.card
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 6 F) := by
    rw [hscalars]
    norm_num
  have hAp : a ^ 5 = 1 := by
    rw [← ha, pow_orderOf_eq_one]
  obtain ⟨b, hbgood, hbimg⟩ :=
    CFSG.RankThree.PartOne.FOC.exists_good_block_of_component
      (n := 6) (K := F) (A := a) (p := 5) (by norm_num) hZ hAp hsqFOC hKprojRT
  refine ⟨b, hbgood, ?_⟩
  simpa [hsqFOC] using hbimg

theorem sl6_primaryFactor_type_of_good
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5)
    {b : primaryFactors (CFSG.RankThree.PartOne.FOC.slEnd a)}
    (hgood : CFSG.RankThree.PartOne.KCLinPlane.GoodBlock b) :
    ((b : F[X]) = X - 1 ∧
        (primaryMultiplicity (CFSG.RankThree.PartOne.FOC.slEnd a) b = 2 ∨
          primaryMultiplicity (CFSG.RankThree.PartOne.FOC.slEnd a) b = 4) ∧
        Nat.card (AdjoinRoot (b : F[X])) = 4) ∨
      ((b : F[X]) ≠ X - 1 ∧
        (primaryMultiplicity (CFSG.RankThree.PartOne.FOC.slEnd a) b = 2 ∨
          primaryMultiplicity (CFSG.RankThree.PartOne.FOC.slEnd a) b = 3) ∧
        Nat.card (AdjoinRoot (b : F[X])) = 16) := by
  classical
  let mF : ℕ := primaryMultiplicity (CFSG.RankThree.PartOne.FOC.slEnd a) b
  let mS : ℕ := primaryMultiplicity (sl6End F a) (b : F[X])
  have hhS : (b : F[X]) ∈ primaryFactors (sl6End F a) := by
    simpa [sl6End_eq_FOC] using b.2
  have hm_eq : mF = mS := by
    dsimp [mF, mS]
    rw [sl6End_eq_FOC]
  have hm2F : 2 ≤ mF := by
    have hgood' : 3 ≤ mF ∨ (2 ≤ mF ∧ 3 < Nat.card (AdjoinRoot (b : F[X]))) := by
      simpa [CFSG.RankThree.PartOne.KCLinPlane.GoodBlock,
        CFSG.RankThree.PartOne.KCLinComm.mult,
        CFSG.RankThree.PartOne.KCLinComm.Efac, mF] using hgood
    omega
  have hdeg := primaryFactor_degree_of_orderFive hF ha hhS
  haveI : Fact (Irreducible (b : F[X])) :=
    ⟨irreducible_of_mem_primaryFactors b.2⟩
  have hcard := CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot
    (K := F) (b : F[X])
  by_cases hp : (b : F[X]) = X - 1
  · left
    have hm3 : mF ≠ 3 := by
      intro hm3
      have hf_eq : sl6FixedMultiplicity F a = mS :=
        sl6FixedMultiplicity_eq_of_fixed hhS hp
      have hdim := (primaryDimensionData_of_orderFive hF ha).1
      omega
    have hm2 : mF = 2 ∨ mF = 4 := by
      have hf4 := (primaryDimensionData_of_orderFive hF ha).2.1
      have hf_eq : sl6FixedMultiplicity F a = mS :=
        sl6FixedMultiplicity_eq_of_fixed hhS hp
      omega
    have hdeg1 : (b : F[X]).natDegree = 1 := by
      rw [hp]
      simpa using natDegree_X_sub_C (1 : F)
    have hcard4 : Nat.card (AdjoinRoot (b : F[X])) = 4 := by
      rw [hcard, hdeg1, hF]
      norm_num
    exact ⟨hp, hm2, hcard4⟩
  · right
    have hm3 : mF = 2 ∨ mF = 3 := by
      have hq := (primaryDimensionData_of_orderFive hF ha).2.2.2 (b : F[X]) hhS hp
      omega
    have hdeg2 : (b : F[X]).natDegree = 2 :=
      (hdeg.resolve_left hp).2
    have hcard16 : Nat.card (AdjoinRoot (b : F[X])) = 16 := by
      rw [hcard, hdeg2, hF]
      norm_num
    exact ⟨hp, hm3, hcard16⟩

private lemma scalars_six_card {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) :
    Nat.card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 6 F) = 3 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center,
    CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 6 (by norm_num), hF]
  norm_num

private lemma blkSL_card_eq_SL_six {F : Type} [Field F] [Finite F]
    {a : Matrix.SpecialLinearGroup (Fin 6) F}
    (hsq : Squarefree (minpoly F (CFSG.RankThree.PartOne.FOC.slEnd a)))
    {b : primaryFactors (CFSG.RankThree.PartOne.FOC.slEnd a)}
    (hbgood : CFSG.RankThree.PartOne.KCLinPlane.GoodBlock b) :
    Nat.card (CFSG.RankThree.PartOne.FOC.blkSL hsq b) =
      Nat.card (Matrix.SpecialLinearGroup
        (Fin (CFSG.RankThree.PartOne.KCLinComm.mult
          (CFSG.RankThree.PartOne.FOC.slEnd a) b))
        (CFSG.RankThree.PartOne.KCLinComm.Efac
          (CFSG.RankThree.PartOne.FOC.slEnd a) b)) := by
  calc
    Nat.card (CFSG.RankThree.PartOne.FOC.blkSL hsq b) =
        Nat.card ((CFSG.RankThree.PartOne.FOC.blkSL hsq b).map
          Matrix.SpecialLinearGroup.toGL) :=
      (Subgroup.card_map_of_injective
        Matrix.SpecialLinearGroup.toGL_injective).symm
    _ = Nat.card (CFSG.RankThree.PartOne.KCLinComm.blockImage hsq b) := by
      rw [CFSG.RankThree.PartOne.FOC.blkSL_map hbgood]
    _ = Nat.card (Matrix.SpecialLinearGroup
        (Fin (CFSG.RankThree.PartOne.KCLinComm.mult
          (CFSG.RankThree.PartOne.FOC.slEnd a) b))
        (CFSG.RankThree.PartOne.KCLinComm.Efac
          (CFSG.RankThree.PartOne.FOC.slEnd a) b)) :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.card_blockImage_eq hsq b

private lemma ker_proj_blkSL_card_dvd_three {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) {a : Matrix.SpecialLinearGroup (Fin 6) F}
    (hsq : Squarefree (minpoly F (CFSG.RankThree.PartOne.FOC.slEnd a)))
    (b : primaryFactors (CFSG.RankThree.PartOne.FOC.slEnd a)) :
    Nat.card ((CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F).comp
      (CFSG.RankThree.PartOne.FOC.blkSL hsq b).subtype).ker ∣ 3 := by
  let φ : ↥(CFSG.RankThree.PartOne.FOC.blkSL hsq b) →*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 6 F :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F).comp
      (CFSG.RankThree.PartOne.FOC.blkSL hsq b).subtype
  have hle : φ.ker.map (CFSG.RankThree.PartOne.FOC.blkSL hsq b).subtype ≤
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 6 F := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    have hk1 : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F (k :
        Matrix.SpecialLinearGroup (Fin 6) F) = 1 := by
      simpa [φ] using hk
    exact (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_eq_one_iff).mp hk1
  have hdvd : Nat.card φ.ker ∣ 3 := by
    have hcardmap : Nat.card (φ.ker.map
        (CFSG.RankThree.PartOne.FOC.blkSL hsq b).subtype) = Nat.card φ.ker :=
      Subgroup.card_map_of_injective (CFSG.RankThree.PartOne.FOC.blkSL hsq b).subtype_injective
    rw [← hcardmap]
    have h := Subgroup.card_dvd_of_le hle
    rwa [scalars_six_card hF] at h
  exact hdvd

private lemma odd_card_ker_proj_blkSL_six {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) {a : Matrix.SpecialLinearGroup (Fin 6) F}
    (hsq : Squarefree (minpoly F (CFSG.RankThree.PartOne.FOC.slEnd a)))
    (b : primaryFactors (CFSG.RankThree.PartOne.FOC.slEnd a)) :
    Odd (Nat.card ((CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F).comp
      (CFSG.RankThree.PartOne.FOC.blkSL hsq b).subtype).ker) := by
  exact Odd.of_dvd_nat (by norm_num) (ker_proj_blkSL_card_dvd_three hF hsq b)

private lemma Qb_two_seven_of_m_four_field_four {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) {a : Matrix.SpecialLinearGroup (Fin 6) F}
    (hsq : Squarefree (minpoly F (CFSG.RankThree.PartOne.FOC.slEnd a)))
    {b : primaryFactors (CFSG.RankThree.PartOne.FOC.slEnd a)}
    (hbgood : CFSG.RankThree.PartOne.KCLinPlane.GoodBlock b)
    (hm : CFSG.RankThree.PartOne.KCLinComm.mult
      (CFSG.RankThree.PartOne.FOC.slEnd a) b = 4)
    (hE : Nat.card (CFSG.RankThree.PartOne.KCLinComm.Efac
      (CFSG.RankThree.PartOne.FOC.slEnd a) b) = 4) :
    2 ^ 7 ∣ Nat.card (CFSG.RankThree.PartOne.FOC.Qb hsq b) := by
  let φ : ↥(CFSG.RankThree.PartOne.FOC.blkSL hsq b) →*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 6 F :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F).comp
      (CFSG.RankThree.PartOne.FOC.blkSL hsq b).subtype
  have hrange : φ.range = CFSG.RankThree.PartOne.FOC.Qb hsq b := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hfac := Subgroup.card_ker_mul_card_range φ
  rw [hrange] at hfac
  have h2SL : 2 ^ 7 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 4)
      (CFSG.RankThree.PartOne.KCLinComm.Efac
        (CFSG.RankThree.PartOne.FOC.slEnd a) b)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq
      (K := CFSG.RankThree.PartOne.KCLinComm.Efac
        (CFSG.RankThree.PartOne.FOC.slEnd a) b) (n := 4) (by norm_num), hE]
    exact dvd_mul_of_dvd_left (by norm_num : 2 ^ 7 ∣ 4 ^ 6) _
  have h2blk : 2 ^ 7 ∣ Nat.card (CFSG.RankThree.PartOne.FOC.blkSL hsq b) := by
    rw [blkSL_card_eq_SL_six hsq hbgood, hm]
    exact h2SL
  have h2mul : 2 ^ 7 ∣ Nat.card φ.ker *
      Nat.card (CFSG.RankThree.PartOne.FOC.Qb hsq b) := by
    rw [hfac]
    exact h2blk
  have hodd := odd_card_ker_proj_blkSL_six hF hsq b
  have hcop : Nat.Coprime (2 ^ 7) (Nat.card φ.ker) :=
    (Nat.coprime_two_left.mpr hodd).pow_left 7
  exact hcop.dvd_of_dvd_mul_left h2mul

private lemma Qb_two_seven_of_m_three_field_sixteen {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) {a : Matrix.SpecialLinearGroup (Fin 6) F}
    (hsq : Squarefree (minpoly F (CFSG.RankThree.PartOne.FOC.slEnd a)))
    {b : primaryFactors (CFSG.RankThree.PartOne.FOC.slEnd a)}
    (hbgood : CFSG.RankThree.PartOne.KCLinPlane.GoodBlock b)
    (hm : CFSG.RankThree.PartOne.KCLinComm.mult
      (CFSG.RankThree.PartOne.FOC.slEnd a) b = 3)
    (hE : Nat.card (CFSG.RankThree.PartOne.KCLinComm.Efac
      (CFSG.RankThree.PartOne.FOC.slEnd a) b) = 16) :
    2 ^ 7 ∣ Nat.card (CFSG.RankThree.PartOne.FOC.Qb hsq b) := by
  let φ : ↥(CFSG.RankThree.PartOne.FOC.blkSL hsq b) →*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 6 F :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F).comp
      (CFSG.RankThree.PartOne.FOC.blkSL hsq b).subtype
  have hrange : φ.range = CFSG.RankThree.PartOne.FOC.Qb hsq b := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hfac := Subgroup.card_ker_mul_card_range φ
  rw [hrange] at hfac
  have h2SL : 2 ^ 7 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3)
      (CFSG.RankThree.PartOne.KCLinComm.Efac
        (CFSG.RankThree.PartOne.FOC.slEnd a) b)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq
      (K := CFSG.RankThree.PartOne.KCLinComm.Efac
        (CFSG.RankThree.PartOne.FOC.slEnd a) b) (n := 3) (by norm_num), hE]
    exact dvd_mul_of_dvd_left (by norm_num : 2 ^ 7 ∣ 16 ^ 3) _
  have h2blk : 2 ^ 7 ∣ Nat.card (CFSG.RankThree.PartOne.FOC.blkSL hsq b) := by
    rw [blkSL_card_eq_SL_six hsq hbgood, hm]
    exact h2SL
  have h2mul : 2 ^ 7 ∣ Nat.card φ.ker *
      Nat.card (CFSG.RankThree.PartOne.FOC.Qb hsq b) := by
    rw [hfac]
    exact h2blk
  have hodd := odd_card_ker_proj_blkSL_six hF hsq b
  have hcop : Nat.Coprime (2 ^ 7) (Nat.card φ.ker) :=
    (Nat.coprime_two_left.mpr hodd).pow_left 7
  exact hcop.dvd_of_dvd_mul_left h2mul

private lemma Qb_not_two_six_of_m_two_field_four {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) {a : Matrix.SpecialLinearGroup (Fin 6) F}
    (hsq : Squarefree (minpoly F (CFSG.RankThree.PartOne.FOC.slEnd a)))
    {b : primaryFactors (CFSG.RankThree.PartOne.FOC.slEnd a)}
    (hbgood : CFSG.RankThree.PartOne.KCLinPlane.GoodBlock b)
    (hm : CFSG.RankThree.PartOne.KCLinComm.mult
      (CFSG.RankThree.PartOne.FOC.slEnd a) b = 2)
    (hE : Nat.card (CFSG.RankThree.PartOne.KCLinComm.Efac
      (CFSG.RankThree.PartOne.FOC.slEnd a) b) = 4) :
    ¬ 2 ^ 6 ∣ Nat.card (CFSG.RankThree.PartOne.FOC.Qb hsq b) := by
  intro hQ
  let φ : ↥(CFSG.RankThree.PartOne.FOC.blkSL hsq b) →*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 6 F :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F).comp
      (CFSG.RankThree.PartOne.FOC.blkSL hsq b).subtype
  have hrange : φ.range = CFSG.RankThree.PartOne.FOC.Qb hsq b := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hfac := Subgroup.card_ker_mul_card_range φ
  rw [hrange] at hfac
  have h2blk : 2 ^ 6 ∣ Nat.card (CFSG.RankThree.PartOne.FOC.blkSL hsq b) := by
    have h := dvd_mul_of_dvd_right hQ (Nat.card φ.ker)
    have h' : 2 ^ 6 ∣ Nat.card φ.ker * Nat.card
        (CFSG.RankThree.PartOne.FOC.Qb hsq b) := by
      simpa [mul_comm] using h
    rwa [hfac] at h' 
  have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2)
      (CFSG.RankThree.PartOne.KCLinComm.Efac
        (CFSG.RankThree.PartOne.FOC.slEnd a) b)) = 60 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq
      (K := CFSG.RankThree.PartOne.KCLinComm.Efac
        (CFSG.RankThree.PartOne.FOC.slEnd a) b) (n := 2) (by norm_num), hE]
    norm_num
  have h2SLnot : ¬ 2 ^ 6 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2)
      (CFSG.RankThree.PartOne.KCLinComm.Efac
        (CFSG.RankThree.PartOne.FOC.slEnd a) b)) := by
    rw [hcardSL]
    norm_num
  rw [blkSL_card_eq_SL_six hsq hbgood, hm] at h2blk
  exact h2SLnot h2blk

private lemma Qb_not_two_six_of_m_two_field_sixteen {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) {a : Matrix.SpecialLinearGroup (Fin 6) F}
    (hsq : Squarefree (minpoly F (CFSG.RankThree.PartOne.FOC.slEnd a)))
    {b : primaryFactors (CFSG.RankThree.PartOne.FOC.slEnd a)}
    (hbgood : CFSG.RankThree.PartOne.KCLinPlane.GoodBlock b)
    (hm : CFSG.RankThree.PartOne.KCLinComm.mult
      (CFSG.RankThree.PartOne.FOC.slEnd a) b = 2)
    (hE : Nat.card (CFSG.RankThree.PartOne.KCLinComm.Efac
      (CFSG.RankThree.PartOne.FOC.slEnd a) b) = 16) :
    ¬ 2 ^ 6 ∣ Nat.card (CFSG.RankThree.PartOne.FOC.Qb hsq b) := by
  intro hQ
  let φ : ↥(CFSG.RankThree.PartOne.FOC.blkSL hsq b) →*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 6 F :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F).comp
      (CFSG.RankThree.PartOne.FOC.blkSL hsq b).subtype
  have hrange : φ.range = CFSG.RankThree.PartOne.FOC.Qb hsq b := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hfac := Subgroup.card_ker_mul_card_range φ
  rw [hrange] at hfac
  have h2blk : 2 ^ 6 ∣ Nat.card (CFSG.RankThree.PartOne.FOC.blkSL hsq b) := by
    have h := dvd_mul_of_dvd_right hQ (Nat.card φ.ker)
    have h' : 2 ^ 6 ∣ Nat.card φ.ker * Nat.card
        (CFSG.RankThree.PartOne.FOC.Qb hsq b) := by
      simpa [mul_comm] using h
    rwa [hfac] at h' 
  have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2)
      (CFSG.RankThree.PartOne.KCLinComm.Efac
        (CFSG.RankThree.PartOne.FOC.slEnd a) b)) = 4080 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq
      (K := CFSG.RankThree.PartOne.KCLinComm.Efac
        (CFSG.RankThree.PartOne.FOC.slEnd a) b) (n := 2) (by norm_num), hE]
    norm_num
  have h2SLnot : ¬ 2 ^ 6 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2)
      (CFSG.RankThree.PartOne.KCLinComm.Efac
        (CFSG.RankThree.PartOne.FOC.slEnd a) b)) := by
    rw [hcardSL]
    norm_num
  rw [blkSL_card_eq_SL_six hsq hbgood, hm] at h2blk
  exact h2SLnot h2blk

private lemma odd_card_ker_of_map_le_odd {G X P : Type*} [Group G] [Finite G]
    [Group X] [Group P] (φ : G →* P) (ι : G →* X) (hι : Function.Injective ι)
    {Z : Subgroup X} (hodd : Odd (Nat.card Z)) (hle : φ.ker.map ι ≤ Z) :
    Odd (Nat.card φ.ker) := by
  have hcard : Nat.card (φ.ker.map ι) = Nat.card φ.ker :=
    Subgroup.card_map_of_injective hι
  have hdvd : Nat.card φ.ker ∣ Nat.card Z := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hle
  exact hodd.of_dvd_nat hdvd

theorem sl6_component_not_card_62400
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    {Q : Type} [Group Q]
    (ψ : Matrix.SpecialLinearGroup (Fin 6) F →* Q)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) F))
    (hrange : ψ.range = ⊤)
    {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5)
    {H : Subgroup Q}
    (hH : CFSG.Assembly.IsComponentOf H
      (Subgroup.centralizer ({ψ a} : Set Q)))
    (hHcard : Nat.card H = 62400) : False := by
  classical
  haveI : Finite Q := Finite.of_surjective ψ (MonoidHom.range_eq_top.mp hrange)
  let X := Matrix.SpecialLinearGroup (Fin 6) F
  let C : Subgroup X := Subgroup.centralizer ({a} : Set X)
  let ψC : ↥C →* Q := ψ.comp C.subtype
  obtain ⟨K, hK, hKmap⟩ :=
    sl6_exists_centralCover_component hF ψ hker hrange ha hH
  let KX : Subgroup X := K.map C.subtype
  have hKX : CFSG.Assembly.IsComponentOf KX C := by
    refine ⟨Subgroup.map_subtype_le K, ?_, ?_⟩
    · have h := CFSG.Assembly.IsSubnormal.map C.subtype hK.2.1
      simpa [KX, Subgroup.map_top, Subgroup.range_subtype] using h
    · have hq : CFSG.IsQuasisimple KX :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv
          (Subgroup.equivMapOfInjective K C.subtype C.subtype_injective)
          ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
            hK.2.2)
      exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq
  let hsqFOC : Squarefree (minpoly F (CFSG.RankThree.PartOne.FOC.slEnd a)) := by
    simpa [sl6End_eq_FOC] using sl6End_squarefree ha
  obtain ⟨b, hbgood, hbimg⟩ :=
    sl6_exists_goodProjectiveBlock_of_component hF ha hsqFOC hKX
  have htype := sl6_primaryFactor_type_of_good hF ha hbgood
  let φH : K →* H :=
    { toFun := fun k => ⟨ψC (k : C), by
        have hmem : ψC (k : C) ∈ K.map ψC := Subgroup.mem_map_of_mem ψC k.2
        rwa [hKmap] at hmem⟩
      map_one' := by
        apply Subtype.ext
        exact map_one ψC
      map_mul' := by
        intro x y
        apply Subtype.ext
        exact map_mul ψC (x : C) (y : C) }
  have hφHsurj : Function.Surjective φH := by
    intro h
    have hh : (h : Q) ∈ K.map ψC := by
      rw [hKmap]
      exact h.2
    obtain ⟨k, hk, hkmap⟩ := Subgroup.mem_map.mp hh
    refine ⟨⟨k, hk⟩, ?_⟩
    apply Subtype.ext
    exact hkmap
  let φP : K →* CFSG.RankThree.PartOne.FOC.Qb hsqFOC b :=
    { toFun := fun k => ⟨CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F (k : X), by
        have hmem : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F (k : X) ∈
            KX.map (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F) :=
          Subgroup.mem_map_of_mem (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F)
            (Subgroup.mem_map_of_mem C.subtype k.2)
        rwa [hbimg] at hmem⟩
      map_one' := by
        apply Subtype.ext
        exact map_one (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F)
      map_mul' := by
        intro x y
        apply Subtype.ext
        exact map_mul (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F) (x : X) (y : X) }
  have hφPsurj : Function.Surjective φP := by
    intro q
    have hq : (q : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 6 F) ∈
        KX.map (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F) := by
      rw [hbimg]
      exact q.2
    obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp hq
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hx
    refine ⟨⟨k, hk⟩, ?_⟩
    apply Subtype.ext
    calc
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F ((k : C) : X) =
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F x := by
            rw [show ((k : C) : X) = x from hkx]
      _ = (q : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 6 F) := hxq
  have hfacH := Subgroup.card_ker_mul_card_of_surjective (f := φH) hφHsurj
  have hfacP := Subgroup.card_ker_mul_card_of_surjective (f := φP) hφPsurj
  have hcenterCard : Nat.card (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 6) F)) = 3 := by
    rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 6 (by norm_num), hF]
    norm_num
  have hoddψker : Odd (Nat.card ψ.ker) := by
    have hdvd3 : Nat.card ψ.ker ∣ 3 := by
      have h := Subgroup.card_dvd_of_le hker
      rwa [hcenterCard] at h
    exact (by norm_num : Odd 3).of_dvd_nat hdvd3
  have hoddH : Odd (Nat.card φH.ker) := by
    refine odd_card_ker_of_map_le_odd φH (C.subtype.comp K.subtype)
      (C.subtype_injective.comp K.subtype_injective) hoddψker ?_
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    have hk1 : ψ ((k : C) : X) = 1 := by
      have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
      simpa [φH, ψC] using h
    exact hk1
  have hoddscalars : Odd (Nat.card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 6 F)) := by
    rw [scalars_six_card hF]
    norm_num
  have hoddP : Odd (Nat.card φP.ker) := by
    refine odd_card_ker_of_map_le_odd φP (C.subtype.comp K.subtype)
      (C.subtype_injective.comp K.subtype_injective) hoddscalars ?_
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    have hk1 : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F ((k : C) : X) = 1 := by
      have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
      simpa [φP] using h
    exact (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_eq_one_iff).mp hk1
  have finish_seven : (2 ^ 7 ∣ Nat.card (CFSG.RankThree.PartOne.FOC.Qb hsqFOC b)) → False := by
    intro hQb
    have h2K : 2 ^ 7 ∣ Nat.card K := by
      have h := dvd_mul_of_dvd_right hQb (Nat.card φP.ker)
      have h' : 2 ^ 7 ∣ Nat.card φP.ker *
          Nat.card (CFSG.RankThree.PartOne.FOC.Qb hsqFOC b) := by
        simpa [mul_comm] using h
      rwa [hfacP] at h'
    have hcopH : Nat.Coprime (2 ^ 7) (Nat.card φH.ker) :=
      (Nat.coprime_two_left.mpr hoddH).pow_left 7
    have h2H : 2 ^ 7 ∣ Nat.card H := by
      have h : 2 ^ 7 ∣ Nat.card φH.ker * Nat.card H := by
        rw [hfacH]
        exact h2K
      exact hcopH.dvd_of_dvd_mul_left h
    rw [hHcard] at h2H
    norm_num at h2H
  have finish_six : (¬ 2 ^ 6 ∣ Nat.card (CFSG.RankThree.PartOne.FOC.Qb hsqFOC b)) → False := by
    intro hQb
    have h2H : 2 ^ 6 ∣ Nat.card H := by
      rw [hHcard]
      norm_num
    have h2K : 2 ^ 6 ∣ Nat.card K := by
      have h : 2 ^ 6 ∣ Nat.card φH.ker * Nat.card H := by
        have h0 := dvd_mul_of_dvd_right h2H (Nat.card φH.ker)
        simpa [mul_comm] using h0
      rwa [hfacH] at h
    have hcopP : Nat.Coprime (2 ^ 6) (Nat.card φP.ker) :=
      (Nat.coprime_two_left.mpr hoddP).pow_left 6
    have h2Qb : 2 ^ 6 ∣ Nat.card (CFSG.RankThree.PartOne.FOC.Qb hsqFOC b) := by
      have h : 2 ^ 6 ∣ Nat.card φP.ker *
          Nat.card (CFSG.RankThree.PartOne.FOC.Qb hsqFOC b) := by
        rw [hfacP]
        exact h2K
      exact hcopP.dvd_of_dvd_mul_left h
    exact hQb h2Qb
  rcases htype with ⟨-, hm | hm, hcardE⟩ | ⟨-, hm | hm, hcardE⟩
  · have hm' : CFSG.RankThree.PartOne.KCLinComm.mult
        (CFSG.RankThree.PartOne.FOC.slEnd a) b = 2 := by
      simpa [CFSG.RankThree.PartOne.KCLinComm.mult] using hm
    have hE : Nat.card (CFSG.RankThree.PartOne.KCLinComm.Efac
        (CFSG.RankThree.PartOne.FOC.slEnd a) b) = 4 := by
      simpa [CFSG.RankThree.PartOne.KCLinComm.Efac] using hcardE
    exact finish_six (Qb_not_two_six_of_m_two_field_four hF hsqFOC hbgood hm' hE)
  · have hm' : CFSG.RankThree.PartOne.KCLinComm.mult
        (CFSG.RankThree.PartOne.FOC.slEnd a) b = 4 := by
      simpa [CFSG.RankThree.PartOne.KCLinComm.mult] using hm
    have hE : Nat.card (CFSG.RankThree.PartOne.KCLinComm.Efac
        (CFSG.RankThree.PartOne.FOC.slEnd a) b) = 4 := by
      simpa [CFSG.RankThree.PartOne.KCLinComm.Efac] using hcardE
    exact finish_seven (Qb_two_seven_of_m_four_field_four hF hsqFOC hbgood hm' hE)
  · have hm' : CFSG.RankThree.PartOne.KCLinComm.mult
        (CFSG.RankThree.PartOne.FOC.slEnd a) b = 2 := by
      simpa [CFSG.RankThree.PartOne.KCLinComm.mult] using hm
    have hE : Nat.card (CFSG.RankThree.PartOne.KCLinComm.Efac
        (CFSG.RankThree.PartOne.FOC.slEnd a) b) = 16 := by
      simpa [CFSG.RankThree.PartOne.KCLinComm.Efac] using hcardE
    exact finish_six (Qb_not_two_six_of_m_two_field_sixteen hF hsqFOC hbgood hm' hE)
  · have hm' : CFSG.RankThree.PartOne.KCLinComm.mult
        (CFSG.RankThree.PartOne.FOC.slEnd a) b = 3 := by
      simpa [CFSG.RankThree.PartOne.KCLinComm.mult] using hm
    have hE : Nat.card (CFSG.RankThree.PartOne.KCLinComm.Efac
        (CFSG.RankThree.PartOne.FOC.slEnd a) b) = 16 := by
      simpa [CFSG.RankThree.PartOne.KCLinComm.Efac] using hcardE
    exact finish_seven (Qb_two_seven_of_m_three_field_sixteen hF hsqFOC hbgood hm' hE)

open CFSG.RankThree.CALinearPrimary

private lemma Qb_thirteen_m_three_sixteen
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    {a : Matrix.SpecialLinearGroup (Fin 6) F}
    (hsq : Squarefree (minpoly F (CFSG.RankThree.PartOne.FOC.slEnd a)))
    {b : primaryFactors (CFSG.RankThree.PartOne.FOC.slEnd a)}
    (hbgood : CFSG.RankThree.PartOne.KCLinPlane.GoodBlock b)
    (hm : CFSG.RankThree.PartOne.KCLinComm.mult
      (CFSG.RankThree.PartOne.FOC.slEnd a) b = 3)
    (hE : Nat.card (CFSG.RankThree.PartOne.KCLinComm.Efac
      (CFSG.RankThree.PartOne.FOC.slEnd a) b) = 16) :
    13 ∣ Nat.card (CFSG.RankThree.PartOne.FOC.Qb hsq b) := by
  let φ : ↥(CFSG.RankThree.PartOne.FOC.blkSL hsq b) →*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 6 F :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F).comp
      (CFSG.RankThree.PartOne.FOC.blkSL hsq b).subtype
  have hrange : φ.range = CFSG.RankThree.PartOne.FOC.Qb hsq b := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hfac := Subgroup.card_ker_mul_card_range φ
  rw [hrange] at hfac
  have h13SL : 13 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3)
      (CFSG.RankThree.PartOne.KCLinComm.Efac
        (CFSG.RankThree.PartOne.FOC.slEnd a) b)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq
      (K := CFSG.RankThree.PartOne.KCLinComm.Efac
        (CFSG.RankThree.PartOne.FOC.slEnd a) b) (n := 3) (by norm_num), hE]
    rw [show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide]
    norm_num
  have h13blk : 13 ∣ Nat.card (CFSG.RankThree.PartOne.FOC.blkSL hsq b) := by
    rw [blkSL_card_eq_SL_six hsq hbgood, hm]
    exact h13SL
  have h13mul : 13 ∣ Nat.card φ.ker * Nat.card
      (CFSG.RankThree.PartOne.FOC.Qb hsq b) := by
    rw [hfac]
    exact h13blk
  have hker3 : Nat.card φ.ker ∣ 3 :=
    ker_proj_blkSL_card_dvd_three hF hsq b
  have h13ker : ¬ 13 ∣ Nat.card φ.ker := by
    intro h13
    have h133 : 13 ∣ 3 := h13.trans hker3
    norm_num at h133
  have hcop : Nat.Coprime 13 (Nat.card φ.ker) :=
    (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 13)).mpr h13ker
  exact hcop.dvd_of_dvd_mul_left h13mul

private lemma card_SL4_field_four_two_six_not_thirteen
    {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : Nat.card F₀ = 4) :
    2 ^ 6 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 4) F₀) ∧
      ¬ 13 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 4) F₀) := by
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 4) F₀) =
      4 ^ 6 * (4 ^ 2 - 1) * (4 ^ 3 - 1) * (4 ^ 4 - 1) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq
      (K := F₀) (n := 4) (by norm_num), hF₀]
    rw [show Finset.Icc 2 4 = ({2, 3, 4} : Finset ℕ) by decide]
    norm_num [Finset.prod_insert]
  constructor
  · rw [hcard]
    norm_num
  · rw [hcard]
    norm_num

theorem ggF4N2K_fixedMultiplicity_of_actualSL4_component
    {F F₀ Q : Type} [Field F] [Finite F] [CharP F 2]
    [Field F₀] [Finite F₀] [CharP F₀ 2]
    [Group Q]
    (hF : Nat.card F = 4) (hF₀ : Nat.card F₀ = 4)
    (ψ : Matrix.SpecialLinearGroup (Fin 6) F →* Q)
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) F))
    {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5)
    {H : Subgroup Q}
    (hH : CFSG.Assembly.IsComponentOf H
      (Subgroup.centralizer ({ψ a} : Set Q)))
    (eH : ↥H ≃* Matrix.SpecialLinearGroup (Fin 4) F₀) :
    sl6FixedMultiplicity F a = 4 := by
  classical
  haveI : Finite Q := Finite.of_surjective ψ hψ
  have hrange : ψ.range = ⊤ := MonoidHom.range_eq_top.mpr hψ
  let X := Matrix.SpecialLinearGroup (Fin 6) F
  let C : Subgroup X := Subgroup.centralizer ({a} : Set X)
  have ha5 : a ^ 5 = 1 := by
    rw [← ha, pow_orderOf_eq_one]
  have hfive : (5 : F) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := F) (p := 2) (q := 5)
      (by norm_num) (by norm_num)
  have hsq0 : Squarefree (minpoly F
      ((slGL 6 F a : LinearMap.GeneralLinearGroup F (Fin 6 → F)) :
        Module.End F (Fin 6 → F))) :=
    CFSG.RankThree.CALinearPrimary.squarefree_minpoly_slGL
      (n := 6) (k := F) (p := 5) hfive ha5
  have hsqFOC : Squarefree (minpoly F (CFSG.RankThree.PartOne.FOC.slEnd a)) := by
    have hsq : Squarefree (minpoly F (sl6End F a)) := by
      simpa [sl6End] using hsq0
    simpa [sl6End_eq_FOC] using hsq
  obtain ⟨K, hK, hKmap⟩ :=
    sl6_exists_centralCover_component hF ψ hker hrange ha hH
  let KX : Subgroup X := K.map C.subtype
  have hKX : CFSG.Assembly.IsComponentOf KX C := by
    refine ⟨Subgroup.map_subtype_le K, ?_, ?_⟩
    · have h := CFSG.Assembly.IsSubnormal.map C.subtype hK.2.1
      simpa [KX, Subgroup.map_top, Subgroup.range_subtype] using h
    · have hq : CFSG.IsQuasisimple KX :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv
          (Subgroup.equivMapOfInjective K C.subtype C.subtype_injective)
          ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
            hK.2.2)
      exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq
  obtain ⟨b, hbgood, hbimg⟩ :=
    sl6_exists_goodProjectiveBlock_of_component hF ha hsqFOC hKX
  have htype := sl6_primaryFactor_type_of_good hF ha hbgood
  have hcardH : Nat.card H = Nat.card (Matrix.SpecialLinearGroup (Fin 4) F₀) :=
    Nat.card_congr eH.toEquiv
  have hH2 : 2 ^ 6 ∣ Nat.card H := by
    rw [hcardH]
    exact (card_SL4_field_four_two_six_not_thirteen hF₀).1
  have hH13 : ¬ 13 ∣ Nat.card H := by
    rw [hcardH]
    exact (card_SL4_field_four_two_six_not_thirteen hF₀).2
  let ψK : KX →* Q := ψ.comp KX.subtype
  have hKXmapH : KX.map ψ = H := by
    dsimp [KX]
    rw [Subgroup.map_map]
    exact hKmap
  have hmap_subtype : (⊤ : Subgroup KX).map KX.subtype = KX := by
    rw [Subgroup.map_top]
    exact Subgroup.range_subtype KX
  have hψKrange : ψK.range = H := by
    rw [MonoidHom.range_eq_map]
    have hmap : (⊤ : Subgroup KX).map ψK = H := by
      rw [show ψK = ψ.comp KX.subtype from rfl,
        ← Subgroup.map_map (K := (⊤ : Subgroup KX)) ψ KX.subtype, hmap_subtype]
      exact hKXmapH
    exact hmap
  have hψKker3 : Nat.card ψK.ker ∣ 3 := by
    have hle : ψK.ker.map KX.subtype ≤ ψ.ker := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
      exact MonoidHom.mem_ker.mpr (by simpa [ψK] using hk)
    have hmapcard : Nat.card (ψK.ker.map KX.subtype) = Nat.card ψK.ker :=
      Subgroup.card_map_of_injective KX.subtype_injective
    have hψker3 : Nat.card ψ.ker ∣ 3 := by
      have h := Subgroup.card_dvd_of_le hker
      rwa [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center,
        scalars_six_card hF] at h
    rw [← hmapcard] at *
    exact (Subgroup.card_dvd_of_le hle).trans hψker3
  have hfacH := Subgroup.card_ker_mul_card_range ψK
  rw [hψKrange] at hfacH
  have hKXcardH : Nat.card KX = Nat.card ψK.ker * Nat.card H := hfacH.symm
  let φP : KX →* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 6 F :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F).comp KX.subtype
  have hφPrange : φP.range = CFSG.RankThree.PartOne.FOC.Qb hsqFOC b := by
    rw [MonoidHom.range_eq_map]
    have hmap : (⊤ : Subgroup KX).map φP =
        CFSG.RankThree.PartOne.FOC.Qb hsqFOC b := by
      rw [show φP = (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F).comp
        KX.subtype from rfl,
        ← Subgroup.map_map (K := (⊤ : Subgroup KX))
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F) KX.subtype,
        hmap_subtype]
      exact hbimg
    exact hmap
  have hφPker3 : Nat.card φP.ker ∣ 3 := by
    have hle : φP.ker.map KX.subtype ≤
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 6 F := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
      have hk1 : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F
          (k : X) = 1 := by
        simpa [φP] using hk
      exact (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_eq_one_iff).mp hk1
    have hmapcard : Nat.card (φP.ker.map KX.subtype) = Nat.card φP.ker :=
      Subgroup.card_map_of_injective KX.subtype_injective
    have h := Subgroup.card_dvd_of_le hle
    rw [hmapcard, scalars_six_card hF] at h
    exact h
  have hfacQ := Subgroup.card_ker_mul_card_range φP
  rw [hφPrange] at hfacQ
  have hKXcardQ : Nat.card KX =
      Nat.card φP.ker * Nat.card (CFSG.RankThree.PartOne.FOC.Qb hsqFOC b) :=
    hfacQ.symm
  have h2KX : 2 ^ 6 ∣ Nat.card KX := by
    rw [hKXcardH]
    exact dvd_mul_of_dvd_right hH2 _
  have h2Qb : 2 ^ 6 ∣ Nat.card (CFSG.RankThree.PartOne.FOC.Qb hsqFOC b) := by
    have hcop : Nat.Coprime (2 ^ 6) (Nat.card φP.ker) := by
      have h2 : Nat.Coprime 2 (Nat.card φP.ker) :=
        (Nat.prime_two.coprime_iff_not_dvd).mpr (by
          intro h2d
          have h23 : 2 ∣ 3 := h2d.trans hφPker3
          norm_num at h23)
      exact h2.pow_left 6
    have h : 2 ^ 6 ∣ Nat.card φP.ker *
        Nat.card (CFSG.RankThree.PartOne.FOC.Qb hsqFOC b) := by
      rw [← hKXcardQ]
      exact h2KX
    exact hcop.dvd_of_dvd_mul_left h
  have h13KX : ¬ 13 ∣ Nat.card KX := by
    intro h13
    have h13ker : ¬ 13 ∣ Nat.card ψK.ker := by
      intro h13k
      have h133 : 13 ∣ 3 := h13k.trans hψKker3
      norm_num at h133
    have hcop : Nat.Coprime 13 (Nat.card ψK.ker) :=
      (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 13)).mpr h13ker
    have h : 13 ∣ Nat.card ψK.ker * Nat.card H := by
      rw [hKXcardH] at h13
      exact h13
    exact hH13 (hcop.dvd_of_dvd_mul_left h)
  have h13Qb : ¬ 13 ∣ Nat.card (CFSG.RankThree.PartOne.FOC.Qb hsqFOC b) := by
    intro h13
    have h : 13 ∣ Nat.card φP.ker *
        Nat.card (CFSG.RankThree.PartOne.FOC.Qb hsqFOC b) :=
      dvd_mul_of_dvd_right h13 _
    have h13KX' : 13 ∣ Nat.card KX := by
      rw [← hKXcardQ] at h
      exact h
    exact h13KX h13KX'
  rcases htype with ⟨hbX, hm24, hE4⟩ | ⟨hbne, hm23, hE16⟩
  · rcases hm24 with hm2 | hm4
    · have hm2' : CFSG.RankThree.PartOne.KCLinComm.mult
          (CFSG.RankThree.PartOne.FOC.slEnd a) b = 2 := by
        simpa [CFSG.RankThree.PartOne.KCLinComm.mult] using hm2
      have hE4' : Nat.card (CFSG.RankThree.PartOne.KCLinComm.Efac
          (CFSG.RankThree.PartOne.FOC.slEnd a) b) = 4 := by
        simpa [CFSG.RankThree.PartOne.KCLinComm.Efac] using hE4
      exact False.elim
        ((Qb_not_two_six_of_m_two_field_four hF hsqFOC hbgood hm2' hE4') h2Qb)
    · have hhS : (b : F[X]) ∈ primaryFactors (sl6End F a) := by
        simpa [sl6End_eq_FOC] using b.2
      have hmS : primaryMultiplicity (sl6End F a) (b : F[X]) = 4 := by
        simpa [sl6End_eq_FOC] using hm4
      rw [sl6FixedMultiplicity_eq_of_fixed hhS hbX, hmS]
  · rcases hm23 with hm2 | hm3
    · have hm2' : CFSG.RankThree.PartOne.KCLinComm.mult
          (CFSG.RankThree.PartOne.FOC.slEnd a) b = 2 := by
        simpa [CFSG.RankThree.PartOne.KCLinComm.mult] using hm2
      have hE16' : Nat.card (CFSG.RankThree.PartOne.KCLinComm.Efac
          (CFSG.RankThree.PartOne.FOC.slEnd a) b) = 16 := by
        simpa [CFSG.RankThree.PartOne.KCLinComm.Efac] using hE16
      exact False.elim
        ((Qb_not_two_six_of_m_two_field_sixteen hF hsqFOC hbgood hm2' hE16') h2Qb)
    · have hm3' : CFSG.RankThree.PartOne.KCLinComm.mult
          (CFSG.RankThree.PartOne.FOC.slEnd a) b = 3 := by
        simpa [CFSG.RankThree.PartOne.KCLinComm.mult] using hm3
      have hE16' : Nat.card (CFSG.RankThree.PartOne.KCLinComm.Efac
          (CFSG.RankThree.PartOne.FOC.slEnd a) b) = 16 := by
        simpa [CFSG.RankThree.PartOne.KCLinComm.Efac] using hE16
      exact False.elim
        (h13Qb (Qb_thirteen_m_three_sixteen hF hsqFOC hbgood hm3' hE16'))

private lemma primaryMultiplicity_le_sl6QuadraticMultiplicity
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {a : Matrix.SpecialLinearGroup (Fin 6) F} {h : F[X]}
    (hh : h ∈ primaryFactors (sl6End F a)) (hne : h ≠ X - 1) :
    primaryMultiplicity (sl6End F a) h ≤ sl6QuadraticMultiplicity F a := by
  classical
  let b : primaryFactors (sl6End F a) := ⟨h, hh⟩
  have hsingle := Finset.single_le_sum
    (s := (Finset.univ : Finset (primaryFactors (sl6End F a))))
    (f := fun b : primaryFactors (sl6End F a) =>
      if (b : F[X]) ≠ X - 1 then primaryMultiplicity (sl6End F a) (b : F[X]) else 0)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
  simpa [sl6QuadraticMultiplicity, b, hne] using hsingle

private lemma sl6_fixedBlock_isComponent
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5)
    (hh : (X - 1 : F[X]) ∈ primaryFactors (sl6End F a))
    (hm : primaryMultiplicity (sl6End F a) (X - 1) = 4) :
    CFSG.Assembly.IsComponentOf
      ((linearSpecialBlock (slGL 6 F a) (X - 1)).comap (slGL 6 F))
      (Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin 6) F))) := by
  classical
  let B : Subgroup (LinearMap.GeneralLinearGroup F (Fin 6 → F)) :=
    linearSpecialBlock (slGL 6 F a) (X - 1)
  let H : Subgroup (Matrix.SpecialLinearGroup (Fin 6) F) := B.comap (slGL 6 F)
  let C : Subgroup (Matrix.SpecialLinearGroup (Fin 6) F) :=
    Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin 6) F))
  have ha5 : a ^ 5 = 1 := by
    rw [← ha, pow_orderOf_eq_one]
  have hfive : (5 : F) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := F) (p := 2) (q := 5)
      (by norm_num) (by norm_num)
  have hsq0 : Squarefree (minpoly F
      ((slGL 6 F a : LinearMap.GeneralLinearGroup F (Fin 6 → F)) :
        Module.End F (Fin 6 → F))) :=
    CFSG.RankThree.CALinearPrimary.squarefree_minpoly_slGL
      (n := 6) (k := F) (p := 5) hfive ha5
  have hsq : Squarefree (minpoly F (sl6End F a)) := by
    simpa [sl6End] using hsq0
  have hsqGL : Squarefree (minpoly F
      ((slGL 6 F a : LinearMap.GeneralLinearGroup F (Fin 6 → F)) :
        Module.End F (Fin 6 → F))) := by
    simpa [sl6End] using hsq
  have hhGL : (X - 1 : F[X]) ∈ primaryFactors
      ((slGL 6 F a : LinearMap.GeneralLinearGroup F (Fin 6 → F)) :
        Module.End F (Fin 6 → F)) := by
    simpa [sl6End] using hh
  have hmGL : primaryMultiplicity
      ((slGL 6 F a : LinearMap.GeneralLinearGroup F (Fin 6 → F)) :
        Module.End F (Fin 6 → F)) (X - 1) = 4 := by
    simpa [sl6End] using hm
  haveI : Fact (Irreducible (X - 1 : F[X])) :=
    ⟨irreducible_of_mem_primaryFactors hh⟩
  have hcard : Nat.card (AdjoinRoot (X - 1 : F[X])) = 4 := by
    rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot (K := F) (X - 1)]
    have hdeg : (X - 1 : F[X]).natDegree = 1 := by
      simpa using natDegree_X_sub_C (1 : F)
    rw [hdeg, hF]
    norm_num
  have hgood : 3 ≤ primaryMultiplicity
      ((slGL 6 F a : LinearMap.GeneralLinearGroup F (Fin 6 → F)) :
        Module.End F (Fin 6 → F)) (X - 1) ∨
      (2 ≤ primaryMultiplicity
        ((slGL 6 F a : LinearMap.GeneralLinearGroup F (Fin 6 → F)) :
          Module.End F (Fin 6 → F)) (X - 1) ∧
        4 ≤ Nat.card (AdjoinRoot (X - 1 : F[X]))) := by
    left
    omega
  have hBq : CFSG.IsQuasisimple B := by
    dsimp [B]
    exact CFSG.RankThree.CALinearPrimary.isQuasisimple_linearSpecialBlock
      (x := slGL 6 F a) (V := Fin 6 → F) hsqGL hhGL hgood
  have hBle : B ≤ (slGL 6 F).range := by
    dsimp [B]
    exact CFSG.RankThree.CALinearPrimary.linearSpecialBlock_le_range_slGL
      (n := 6) (k := F) (a := a) hsqGL hhGL
  have hmap : H.map (slGL 6 F) = B := by
    dsimp [H, B]
    rw [Subgroup.map_comap_eq, inf_eq_right]
    exact hBle
  let e : H ≃* B :=
    (Subgroup.equivMapOfInjective H (slGL 6 F)
      (slGL_injective (n := 6) (k := F))).trans (MulEquiv.subgroupCongr hmap)
  have hHq : CFSG.IsQuasisimple H :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hBq
  have hHle : H ≤ C := by
    dsimp [H, B, C]
    exact CFSG.RankThree.CALinearPrimary.comap_linearSpecialBlock_le_centralizer
      (n := 6) (k := F) (a := a) (h := X - 1)
  have hCnorm : C ≤ Subgroup.normalizer H := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact CFSG.RankThree.CALinearPrimary.conj_mem_comap_linearSpecialBlock
        (n := 6) (k := F) (a := a) (h := X - 1) hc hn
    · intro hn
      have hc' : c⁻¹ ∈ C := C.inv_mem hc
      have h := CFSG.RankThree.CALinearPrimary.conj_mem_comap_linearSpecialBlock
        (n := 6) (k := F) (a := a) (h := X - 1) hc' hn
      dsimp [H, B]
      simpa [mul_assoc] using h
  have hHnormalC : (H.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHle).mpr hCnorm
  have hHsub : CFSG.Assembly.IsSubnormal H C :=
    (CFSG.Assembly.IsSubnormal.iff_subgroupOf hHle).mpr hHnormalC.isSubnormal
  have hHqA : CFSG.Assembly.IsQuasisimple H :=
    ⟨hHq.1.commutator_eq_top, hHq.2.1⟩
  have hres : CFSG.Assembly.IsComponentOf H C := ⟨hHle, hHsub, hHqA⟩
  simpa [H, B] using hres

theorem ggF4N2K_component_eq_fixedBlock_of_fixedMultiplicity
    {F Q : Type} [Field F] [Finite F] [CharP F 2]
    [Group Q]
    (hF : Nat.card F = 4)
    (ψ : Matrix.SpecialLinearGroup (Fin 6) F →* Q)
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) F))
    {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5)
    (hsf : sl6FixedMultiplicity F a = 4)
    {H : Subgroup Q}
    (hH : CFSG.Assembly.IsComponentOf H
      (Subgroup.centralizer ({ψ a} : Set Q))) :
    H = ((CFSG.RankThree.CALinearPrimary.linearSpecialBlock
      (CFSG.RankThree.CALinearPrimary.slGL 6 F a) (Polynomial.X - 1)).comap
        (CFSG.RankThree.CALinearPrimary.slGL 6 F)).map ψ := by
  classical
  haveI : Finite Q := Finite.of_surjective ψ hψ
  have hrange : ψ.range = ⊤ := MonoidHom.range_eq_top.mpr hψ
  let SLX := Matrix.SpecialLinearGroup (Fin 6) F
  let C : Subgroup SLX := Subgroup.centralizer ({a} : Set SLX)
  have ha5 : a ^ 5 = 1 := by
    rw [← ha, pow_orderOf_eq_one]
  have hfive : (5 : F) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := F) (p := 2) (q := 5)
      (by norm_num) (by norm_num)
  have hsq0 : Squarefree (minpoly F
      ((slGL 6 F a : LinearMap.GeneralLinearGroup F (Fin 6 → F)) :
        Module.End F (Fin 6 → F))) :=
    CFSG.RankThree.CALinearPrimary.squarefree_minpoly_slGL
      (n := 6) (k := F) (p := 5) hfive ha5
  have hsqFOC : Squarefree (minpoly F (CFSG.RankThree.PartOne.FOC.slEnd a)) := by
    have hsq : Squarefree (minpoly F (sl6End F a)) := by
      simpa [sl6End] using hsq0
    simpa [sl6End_eq_FOC] using hsq
  obtain ⟨K, hK, hKmap⟩ :=
    sl6_exists_centralCover_component hF ψ hker hrange ha hH
  let KX : Subgroup SLX := K.map C.subtype
  have hKX : CFSG.Assembly.IsComponentOf KX C := by
    refine ⟨Subgroup.map_subtype_le K, ?_, ?_⟩
    · have h := CFSG.Assembly.IsSubnormal.map C.subtype hK.2.1
      simpa [KX, Subgroup.map_top, Subgroup.range_subtype] using h
    · have hq : CFSG.IsQuasisimple KX :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv
          (Subgroup.equivMapOfInjective K C.subtype C.subtype_injective)
          ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
            hK.2.2)
      exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq
  obtain ⟨b, hbgood, hbimg⟩ :=
    sl6_exists_goodProjectiveBlock_of_component hF ha hsqFOC hKX
  have hKXmapH : KX.map ψ = H := by
    dsimp [KX]
    rw [Subgroup.map_map]
    exact hKmap
  have hquad : sl6QuadraticMultiplicity F a = 1 := by
    have hdim := (primaryDimensionData_of_orderFive hF ha).1
    omega
  have hbmem : (b : F[X]) ∈ primaryFactors (sl6End F a) := by
    simpa [sl6End_eq_FOC] using b.2
  have hge : 2 ≤ primaryMultiplicity (sl6End F a) (b : F[X]) := by
    have htype := sl6_primaryFactor_type_of_good hF ha hbgood
    rcases htype with ⟨_, hm, _⟩ | ⟨_, hm, _⟩ <;>
      simp only [sl6End_eq_FOC] <;> rcases hm with hm | hm <;> omega
  have hbX : (b : F[X]) = X - 1 := by
    by_contra hne
    have hle := primaryMultiplicity_le_sl6QuadraticMultiplicity hbmem hne
    omega
  have hm4 : primaryMultiplicity (CFSG.RankThree.PartOne.FOC.slEnd a) (b : F[X]) = 4 := by
    have hm := (sl6FixedMultiplicity_eq_of_fixed hbmem hbX).symm.trans hsf
    simpa [sl6End_eq_FOC] using hm
  have hm4F : CFSG.RankThree.PartOne.KCLinComm.mult
      (CFSG.RankThree.PartOne.FOC.slEnd a) b = 4 := by
    simpa [CFSG.RankThree.PartOne.KCLinComm.mult] using hm4
  have hbX' : (b : F[X]) = X - 1 := hbX
  have hhB : (X - 1 : F[X]) ∈ primaryFactors (sl6End F a) := by
    simpa [sl6End_eq_FOC, hbX'] using b.2
  have hmB : primaryMultiplicity (sl6End F a) (X - 1) = 4 := by
    simpa [sl6End_eq_FOC, hbX'] using hm4
  let B : Subgroup SLX :=
    (linearSpecialBlock (slGL 6 F a) (X - 1)).comap (slGL 6 F)
  have hBcomp : CFSG.Assembly.IsComponentOf B C := by
    have h := sl6_fixedBlock_isComponent (F := F) hF (a := a) ha hhB hmB
    simpa [B, X, C] using h
  have hhGL : (X - 1 : F[X]) ∈ primaryFactors
      ((slGL 6 F a : LinearMap.GeneralLinearGroup F (Fin 6 → F)) :
        Module.End F (Fin 6 → F)) := by
    simpa [sl6End] using hhB
  have hb_le : CFSG.RankThree.PartOne.FOC.blkSL hsqFOC b ≤ B := by
    intro g hg
    have hg' : Matrix.SpecialLinearGroup.toGL g ∈
        CFSG.RankThree.PartOne.KCLinComm.blockImage hsqFOC b :=
      (CFSG.RankThree.PartOne.FOC.mem_blkSL).mp hg
    have hmem := CFSG.RankThree.PartOne.toLin_mem_linearSpecialBlock_of_mem_blockImage
      (x := slGL 6 F a) hsqFOC b hg'
    have hmem' : slGL 6 F g ∈ linearSpecialBlock (slGL 6 F a) (X - 1) := by
      simpa [slGL, hbX] using hmem
    simpa [B] using hmem'
  have hmBGL : primaryMultiplicity
      ((slGL 6 F a : LinearMap.GeneralLinearGroup F (Fin 6 → F)) :
        Module.End F (Fin 6 → F)) (X - 1) = 4 := by
    simpa [sl6End] using hmB
  have hBcard : Nat.card B =
      Nat.card (Matrix.SpecialLinearGroup (Fin 4)
        (AdjoinRoot (X - 1 : F[X]))) := by
    obtain ⟨eB⟩ := CFSG.RankThree.CALinearPrimary.comap_linearSpecialBlock_mulEquiv
      (n := 6) (k := F) (a := a) hsq0 hhGL
    let e1 : linearSpecialBlock (slGL 6 F a) (X - 1) ≃*
        _root_.SpecialLinearGroup (AdjoinRoot (X - 1 : F[X]))
          (primaryComponent
            ((slGL 6 F a : LinearMap.GeneralLinearGroup F (Fin 6 → F)) :
              Module.End F (Fin 6 → F)) (X - 1)) :=
      MulEquiv.ofBijective
        (CFSG.RankThree.CALinearPrimary.linearSpecialBlockRestrict
          (slGL 6 F a) (X - 1))
        ⟨CFSG.RankThree.CALinearPrimary.linearSpecialBlockRestrict_injective
            (x := slGL 6 F a) hsq0,
          CFSG.RankThree.CALinearPrimary.linearSpecialBlockRestrict_surjective
            (x := slGL 6 F a) hsq0 hhGL⟩
    haveI : Fact (Irreducible (X - 1 : F[X])) :=
      ⟨irreducible_of_mem_primaryFactors hhB⟩
    haveI : Finite (AdjoinRoot (X - 1 : F[X])) := Module.finite_of_finite F
    let basis : Module.Basis
        (Fin (primaryMultiplicity
          ((slGL 6 F a : LinearMap.GeneralLinearGroup F (Fin 6 → F)) :
            Module.End F (Fin 6 → F)) (X - 1)))
        (AdjoinRoot (X - 1 : F[X]))
        (primaryComponent
          ((slGL 6 F a : LinearMap.GeneralLinearGroup F (Fin 6 → F)) :
            Module.End F (Fin 6 → F)) (X - 1)) :=
      Module.finBasisOfFinrankEq _ _ rfl
    calc
      Nat.card B = Nat.card (linearSpecialBlock (slGL 6 F a) (X - 1)) :=
        Nat.card_congr eB.toEquiv
      _ = Nat.card (_root_.SpecialLinearGroup (AdjoinRoot (X - 1 : F[X]))
            (primaryComponent
              ((slGL 6 F a : LinearMap.GeneralLinearGroup F (Fin 6 → F)) :
                Module.End F (Fin 6 → F)) (X - 1))) :=
        Nat.card_congr e1.toEquiv
      _ = Nat.card (Matrix.SpecialLinearGroup
            (Fin (primaryMultiplicity
              ((slGL 6 F a : LinearMap.GeneralLinearGroup F (Fin 6 → F)) :
                Module.End F (Fin 6 → F)) (X - 1)))
            (AdjoinRoot (X - 1 : F[X]))) :=
        Nat.card_congr (Matrix.SpecialLinearGroup.toLin_equiv basis).symm.toEquiv
      _ = Nat.card (Matrix.SpecialLinearGroup (Fin 4)
            (AdjoinRoot (X - 1 : F[X]))) := by
        rw [hmBGL]
  have hblkcard : Nat.card (CFSG.RankThree.PartOne.FOC.blkSL hsqFOC b) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 4)
        (AdjoinRoot (X - 1 : F[X]))) := by
    rw [blkSL_card_eq_SL_six hsqFOC hbgood, hm4F]
    change Nat.card (Matrix.SpecialLinearGroup (Fin 4)
      (AdjoinRoot (b : F[X]))) =
        Nat.card (Matrix.SpecialLinearGroup (Fin 4)
          (AdjoinRoot (X - 1 : F[X])))
    rw [hbX']
  have hB_eq_blk : CFSG.RankThree.PartOne.FOC.blkSL hsqFOC b = B := by
    apply Subgroup.eq_of_le_of_card_ge hb_le
    rw [hBcard, hblkcard]
  have hBproj : B.map (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F) =
      CFSG.RankThree.PartOne.FOC.Qb hsqFOC b := by
    rw [← hB_eq_blk]
    rfl
  have hQbq : CFSG.IsQuasisimple ↥(CFSG.RankThree.PartOne.FOC.Qb hsqFOC b) :=
    (CFSG.RankThree.PartOne.FOC.isComponentOf_Qb
      (n := 6) (K := F) (A := a) (hsq := hsqFOC) (b := b) hbgood).2.1
  have hQbcomm : ⁅CFSG.RankThree.PartOne.FOC.Qb hsqFOC b,
      CFSG.RankThree.PartOne.FOC.Qb hsqFOC b⁆ =
      CFSG.RankThree.PartOne.FOC.Qb hsqFOC b := by
    have h := congrArg
      (Subgroup.map (CFSG.RankThree.PartOne.FOC.Qb hsqFOC b).subtype)
      hQbq.1.commutator_eq_top
    change Subgroup.map (CFSG.RankThree.PartOne.FOC.Qb hsqFOC b).subtype
      (⁅(⊤ : Subgroup ↥(CFSG.RankThree.PartOne.FOC.Qb hsqFOC b)),
        (⊤ : Subgroup ↥(CFSG.RankThree.PartOne.FOC.Qb hsqFOC b))⁆) = _ at h
    rwa [Subgroup.map_commutator, Subgroup.map_top,
      Subgroup.range_subtype] at h
  have hQbne : CFSG.RankThree.PartOne.FOC.Qb hsqFOC b ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).mp
      (CFSG.LocalCores.isQuasisimple_nontrivial hQbq)
  have hcomp_eq : KX = B := by
    rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute
      hKX hBcomp with heq | hcomm
    · exact heq
    · exfalso
      have hprojcomm : (⁅KX, B⁆).map
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 6 F) =
          ⁅CFSG.RankThree.PartOne.FOC.Qb hsqFOC b,
            CFSG.RankThree.PartOne.FOC.Qb hsqFOC b⁆ := by
        rw [Subgroup.map_commutator, hbimg, hBproj]
      have hbot : ⁅CFSG.RankThree.PartOne.FOC.Qb hsqFOC b,
          CFSG.RankThree.PartOne.FOC.Qb hsqFOC b⁆ = ⊥ := by
        have h := hprojcomm
        rw [hcomm, Subgroup.map_bot] at h
        exact h.symm
      exact hQbne (hQbcomm.symm.trans hbot)
  show H = B.map ψ
  rw [← hKXmapH, hcomp_eq]

theorem ggF4N2K_fixedBlockRange_of_actualSL4_component
    {F F₀ Q : Type} [Field F] [Finite F] [CharP F 2]
    [Field F₀] [Finite F₀] [CharP F₀ 2] [Group Q]
    (hF : Nat.card F = 4) (hF₀ : Nat.card F₀ = 4)
    (ψ : Matrix.SpecialLinearGroup (Fin 6) F →* Q)
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) F))
    {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5)
    {H : Subgroup Q}
    (hH : CFSG.Assembly.IsComponentOf H (Subgroup.centralizer ({ψ a} : Set Q)))
    (eH : ↥H ≃* Matrix.SpecialLinearGroup (Fin 4) F₀) :
    H = ((linearSpecialBlock (slGL 6 F a) (Polynomial.X - 1)).comap (slGL 6 F)).map ψ :=
  ggF4N2K_component_eq_fixedBlock_of_fixedMultiplicity hF ψ hψ hker ha
    (ggF4N2K_fixedMultiplicity_of_actualSL4_component hF hF₀ ψ hψ hker ha hH eH) hH

private lemma ggU_PSU_three_two_card :
    Nat.card (CFSG.StandardType.ggU .PSU 3 2).K = 62400 := by
  let Fq := GaloisField 2 4
  let U := CFSG.LieType.Universal.Unitary.SU
    (CFSG.LieType.BorelTits.unitaryInvolution Fq 2 2) 3
  have hU : (CFSG.StandardType.ggU .PSU 3 2).K = U := rfl
  have hFq : Nat.card Fq = (2 ^ 2) ^ 2 := by
    rw [GaloisField.card 2 4 (by norm_num)]
    norm_num
  rw [hU]
  dsimp [U]
  rw [CFSG.LieType.Steinberg.card_SU_three (p := 2) (f := 2) hFq]
  norm_num

private lemma GGCentralImage_PSU_three_two_card
    {Q : Type} [Group Q] {H : Subgroup Q}
    (h : CFSG.StandardType.GGCentralImage .PSU 3 2 H) : Nat.card H = 62400 := by
  classical
  obtain ⟨ψ, hadm, hker, hrange⟩ := h
  let U := (CFSG.StandardType.ggU .PSU 3 2).K
  let Fq := GaloisField 2 4
  have hFq : Nat.card Fq = (2 ^ 2) ^ 2 := by
    rw [GaloisField.card 2 4 (by norm_num)]
    norm_num
  have hcenterU : Subgroup.center U = ⊥ := by
    change Subgroup.center ↥(CFSG.LieType.Universal.Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution Fq 2 2) 3) = ⊥
    have hcard_center : Nat.card (Subgroup.center ↥(CFSG.LieType.Universal.Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution Fq 2 2) 3)) = 1 := by
      rw [CFSG.RankThree.PartOne.KFU.card_center_SU_three
        (K := Fq) (f := 2) hFq (by norm_num)]
      norm_num
    exact Subgroup.eq_bot_of_card_eq
      (H := Subgroup.center ↥(CFSG.LieType.Universal.Unitary.SU
        (CFSG.LieType.BorelTits.unitaryInvolution Fq 2 2) 3)) hcard_center
  have hkerbot : ψ.ker = ⊥ := by
    refine le_antisymm ?_ bot_le
    have hker' : ψ.ker ≤ Subgroup.center U := hker
    simpa [hcenterU] using hker' 
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hkerbot
  have hcardrange : Nat.card ψ.range = Nat.card U :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [← hrange, hcardrange]
  simpa [U] using ggU_PSU_three_two_card

theorem not_GGCentralImage_PSU_three_two_of_component
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    {Q : Type} [Group Q]
    (ψ : Matrix.SpecialLinearGroup (Fin 6) F →* Q)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) F))
    (hrange : ψ.range = ⊤)
    {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5)
    {H : Subgroup Q}
    (hH : CFSG.Assembly.IsComponentOf H
      (Subgroup.centralizer ({ψ a} : Set Q))) :
    ¬ CFSG.StandardType.GGCentralImage .PSU 3 2 H := by
  intro himg
  exact sl6_component_not_card_62400 hF ψ hker hrange ha hH
    (GGCentralImage_PSU_three_two_card himg)

end CFSG.StandardType

public section

namespace CFSG.StandardType

open Polynomial Module
open CFSG
open CFSG.RankThree.CALinearPrimary
open CFSG.SeitzReduction.E6Pilot
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.RankThree.PartOne.KCPrimary

noncomputable section

private lemma adjRootXSubOneEquiv_apply (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 4) (a : F) :
    (AdjoinRoot.lift (RingHom.id F) 1 (by
      simpa using eval₂_X_sub_C (RingHom.id F) 1))
        (AdjoinRoot.of (X - 1 : F[X]) a) = a := by
  rw [AdjoinRoot.lift_of]
  rfl

private noncomputable def adjRootXSubOneEquiv (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 4) : AdjoinRoot (X - 1 : F[X]) ≃+* F := by
  classical
  let φ : AdjoinRoot (X - 1 : F[X]) →+* F :=
    AdjoinRoot.lift (RingHom.id F) 1 (by
      simpa using eval₂_X_sub_C (RingHom.id F) 1)
  haveI : Fact (Irreducible (X - 1 : F[X])) := ⟨irreducible_X_sub_C 1⟩
  have hinj : Function.Injective φ := RingHom.injective φ
  have hdeg : (X - 1 : F[X]).natDegree = 1 := by
    simpa using natDegree_X_sub_C (1 : F)
  have hcard : Nat.card (AdjoinRoot (X - 1 : F[X])) = Nat.card F := by
    rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot, hdeg, hF]
    norm_num
  exact RingEquiv.ofBijective φ
    ((Nat.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩)

private lemma adjRootXSubOneEquiv_symm (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 4) :
    ((adjRootXSubOneEquiv F hF).symm : F →+* AdjoinRoot (X - 1 : F[X])) =
      algebraMap F (AdjoinRoot (X - 1 : F[X])) := by
  ext a
  rw [AdjoinRoot.algebraMap_eq]
  apply (adjRootXSubOneEquiv F hF).symm_apply_eq.mpr
  exact (adjRootXSubOneEquiv_apply F hF a).symm

private noncomputable def slMapEquiv4 {F E : Type} [Field F] [Field E]
    (e : F ≃+* E) :
    Matrix.SpecialLinearGroup (Fin 4) F ≃*
      Matrix.SpecialLinearGroup (Fin 4) E where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv g := by
    ext i j
    change e.symm (e ((g : Matrix (Fin 4) (Fin 4) F) i j)) =
      (g : Matrix (Fin 4) (Fin 4) F) i j
    simp
  right_inv g := by
    ext i j
    change e (e.symm ((g : Matrix (Fin 4) (Fin 4) E) i j)) =
      (g : Matrix (Fin 4) (Fin 4) E) i j
    simp
  map_mul' g h := map_mul (Matrix.SpecialLinearGroup.map e.toRingHom) g h

private lemma fixed_mult_and_mem_local
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) {a : Matrix.SpecialLinearGroup (Fin 6) F}
    (ha : orderOf a = 5) (hfixed : sl6FixedMultiplicity F a = 4) :
    (X - 1 : F[X]) ∈ primaryFactors (sl6End F a) ∧
      primaryMultiplicity (sl6End F a) (X - 1) = 4 := by
  classical
  have hquad : sl6QuadraticMultiplicity F a = 1 := by
    have hdim := (primaryDimensionData_of_orderFive hF ha).1
    omega
  obtain ⟨h, H, hh, hm2, hcard, htype, hH, hcomp⟩ :=
    exists_primaryBlock_component_of_orderFive hF ha
  have hp : h = X - 1 := by
    by_contra hne
    have hle := primaryMultiplicity_le_sl6QuadraticMultiplicity hh hne
    omega
  refine ⟨?_, ?_⟩
  · simpa [hp] using hh
  · have hm := (sl6FixedMultiplicity_eq_of_fixed hh hp).symm.trans hfixed
    simpa [hp] using hm

private lemma blockFour_toLin_inl {F : Type} [Field F]
    (g : Matrix.SpecialLinearGroup (Fin 4) F) (i : Fin 4) :
    (Matrix.SpecialLinearGroup.toLin' (blockFour (K := F) g))
      (Pi.single (e46 (Sum.inl i)) 1) =
      ∑ j : Fin 4, (g : Matrix (Fin 4) (Fin 4) F) j i •
        Pi.single (e46 (Sum.inl j)) 1 := by
  rw [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
    coe_blockFour, Matrix.mulVec_single_one]
  ext k
  obtain ⟨x, rfl⟩ := e46.surjective k
  rcases x with x | x <;>
    simp [blockFourMat_apply, Matrix.col_apply, Finset.sum_apply, Pi.single_apply]

private lemma blockFour_toLin_inr {F : Type} [Field F]
    (g : Matrix.SpecialLinearGroup (Fin 4) F) (j : Fin 2) :
    (Matrix.SpecialLinearGroup.toLin' (blockFour (K := F) g))
      (Pi.single (e46 (Sum.inr j)) 1) =
      Pi.single (e46 (Sum.inr j)) 1 := by
  rw [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
    coe_blockFour, Matrix.mulVec_single_one]
  ext k
  obtain ⟨x, rfl⟩ := e46.surjective k
  rcases x with x | x <;>
    simp [blockFourMat_apply, Matrix.col_apply, Matrix.one_apply, Pi.single_apply]

private lemma card_SL4_eq_of_card
    {F F₀ : Type} [Field F] [Finite F] [Field F₀] [Finite F₀]
    (hF : Nat.card F = 4) (hF₀ : Nat.card F₀ = 4) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 4) F) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 4) F₀) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype F₀ := Fintype.ofFinite F₀
  have hF' : Fintype.card F = 4 := by
    simpa [Nat.card_eq_fintype_card] using hF
  have hF₀' : Fintype.card F₀ = 4 := by
    simpa [Nat.card_eq_fintype_card] using hF₀
  rw [Matrix.card_SL_field (𝔽 := F) 4, Matrix.card_SL_field (𝔽 := F₀) 4,
    hF', hF₀']

private lemma prodBasis_map_inl
    {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {Vfix W : Submodule F V} (h : IsCompl Vfix W)
    (bfix : Basis (Fin 4) F Vfix) (bOther : Basis (Fin 2) F W)
    (i : Fin 4) :
    ((bfix.prod bOther).map (Submodule.prodEquivOfIsCompl Vfix W h))
      (Sum.inl i) = (bfix i : V) := by
  rw [Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
  simp

private lemma prodBasis_map_inr
    {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {Vfix W : Submodule F V} (h : IsCompl Vfix W)
    (bfix : Basis (Fin 4) F Vfix) (bOther : Basis (Fin 2) F W)
    (j : Fin 2) :
    ((bfix.prod bOther).map (Submodule.prodEquivOfIsCompl Vfix W h))
      (Sum.inr j) = (bOther j : V) := by
  rw [Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
  simp

private lemma slGL_slConjugation_local {F : Type} [Field F]
    (A : Matrix.GeneralLinearGroup (Fin 6) F)
    (g : Matrix.SpecialLinearGroup (Fin 6) F) :
    slGL 6 F
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 6 F A g) =
      Matrix.GeneralLinearGroup.toLin A * slGL 6 F g *
        (Matrix.GeneralLinearGroup.toLin A)⁻¹ := by
  change Matrix.GeneralLinearGroup.toLin
      (Matrix.SpecialLinearGroup.toGL
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 6 F A g)) =
      Matrix.GeneralLinearGroup.toLin A *
        Matrix.GeneralLinearGroup.toLin (Matrix.SpecialLinearGroup.toGL g) *
        (Matrix.GeneralLinearGroup.toLin A)⁻¹
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
    map_mul, map_mul, map_inv]

theorem ggF4N2K_actualNaturalChart_of_actualSL4_component
    {F F₀ Q : Type} [Field F] [Finite F] [CharP F 2]
    [Field F₀] [Finite F₀] [CharP F₀ 2] [Group Q]
    (hF : Nat.card F = 4) (hF₀ : Nat.card F₀ = 4)
    (ψ : Matrix.SpecialLinearGroup (Fin 6) F →* Q)
    (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) F))
    {a : Matrix.SpecialLinearGroup (Fin 6) F} (ha : orderOf a = 5)
    {H : Subgroup Q}
    (hH : CFSG.Assembly.IsComponentOf H
      (Subgroup.centralizer ({ψ a} : Set Q)))
    (eH : ↥H ≃* Matrix.SpecialLinearGroup (Fin 4) F₀) :
    ∃ (A : Matrix.GeneralLinearGroup (Fin 6) F)
      (e : ↥H ≃* Matrix.SpecialLinearGroup (Fin 4) F),
      ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
        ψ (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
          6 F A (CFSG.SeitzReduction.E6Pilot.blockFour (K := F) g)) =
          H.subtype (e.symm g) := by
  classical
  let SLX := Matrix.SpecialLinearGroup (Fin 6) F
  let V := Fin 6 → F
  let Xend : Module.End F V := sl6End F a
  let p0 : F[X] := X - 1
  have hfixed : sl6FixedMultiplicity F a = 4 :=
    ggF4N2K_fixedMultiplicity_of_actualSL4_component
      hF hF₀ ψ hψ hker ha hH eH
  obtain ⟨hmem, hm4⟩ := fixed_mult_and_mem_local hF ha hfixed
  have hsq : Squarefree (minpoly F Xend) := by
    simpa [Xend] using sl6End_squarefree (F := F) (a := a) ha
  let p : primaryFactors Xend := ⟨p0, hmem⟩
  have hpval : (p : F[X]) = p0 := rfl
  have hdimfix : Module.finrank F (primaryComponent Xend (p : F[X])) = 4 := by
    haveI : Fact (Irreducible (p : F[X])) :=
      ⟨irreducible_of_mem_primaryFactors p.2⟩
    have hm4' : Module.finrank (AdjoinRoot (p : F[X]))
        (primaryComponent Xend (p : F[X])) = 4 := by
      simpa [primaryMultiplicity] using hm4
    rw [CFSG.RankThree.PartOne.KCPrimary.finrank_primaryComponent Xend (p : F[X]),
      hm4']
    have hdeg : (p : F[X]).natDegree = 1 := by
      rw [hpval]
      simpa using natDegree_X_sub_C (1 : F)
    rw [hdeg]
  have hdimV : Module.finrank F V = 6 := by
    simp [V]
  let Vfix : Submodule F V := primaryComponent Xend (p : F[X])
  let W : Submodule F V :=
    ⨆ b : {b : primaryFactors Xend // b ≠ p},
      primaryComponent Xend (b.1 : F[X])
  have hInternal : DirectSum.IsInternal
      (fun b : primaryFactors Xend => primaryComponent Xend b) :=
    CFSG.RankThree.PartOne.KCOrthogonal.isInternal_primaryComponent hsq
  have hdisj : Disjoint Vfix W := by
    have h := hInternal.submodule_iSupIndep.disjoint_biSup (x := p)
      (y := {b : primaryFactors Xend | b ≠ p}) (by simp)
    simpa [W, Vfix, iSup_subtype] using h
  have hsup : Vfix ⊔ W = ⊤ := by
    rw [← hInternal.submodule_iSup_eq_top]
    apply le_antisymm
    · refine sup_le ?_ ?_
      · exact le_iSup (fun b : primaryFactors Xend =>
          primaryComponent Xend b) p
      · refine iSup_le fun b => ?_
        exact le_iSup (fun b : primaryFactors Xend =>
          primaryComponent Xend b) b.1
    · refine iSup_le fun b => ?_
      by_cases hb : b = p
      · subst hb
        exact le_sup_left
      · have hbW : primaryComponent Xend b ≤ W :=
          le_iSup (fun b : {b : primaryFactors Xend // b ≠ p} =>
            primaryComponent Xend (b.1 : F[X])) ⟨b, hb⟩
        exact le_sup_of_le_right hbW
  let hcompl : IsCompl Vfix W := IsCompl.of_eq hdisj.eq_bot hsup
  have hdimother : Module.finrank F W = 2 := by
    have hfr := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hdimfix, hdimV] at hfr
    omega
  let bfixF : Basis (Fin 4) F Vfix :=
    Module.finBasisOfFinrankEq F Vfix hdimfix
  let bOther : Basis (Fin 2) F W :=
    Module.finBasisOfFinrankEq F W hdimother
  let bV : Basis (Fin 6) F V := by
    classical
    let bProd : Basis (Fin 4 ⊕ Fin 2) F (Vfix × W) := bfixF.prod bOther
    exact (bProd.map (Submodule.prodEquivOfIsCompl Vfix W hcompl)).reindex e46
  let P : V ≃ₗ[F] V := bV.equivFun.symm
  let A : Matrix.GeneralLinearGroup (Fin 6) F :=
    Matrix.GeneralLinearGroup.toLin.symm
      (LinearMap.GeneralLinearGroup.ofLinearEquiv P)
  let E := AdjoinRoot p0
  haveI : Fact (Irreducible p0) := ⟨irreducible_X_sub_C 1⟩
  haveI : Module.Finite F E := (AdjoinRoot.powerBasis (Fact.out : Irreducible p0).ne_zero).finite
  haveI : Finite E := Module.finite_of_finite F
  haveI : Fintype E := Fintype.ofFinite E
  let eEF : E ≃+* F := adjRootXSubOneEquiv F hF
  have hEFsymm : ((eEF.symm : F →+* E)) = algebraMap F E := by
    simpa [E, p0, eEF] using adjRootXSubOneEquiv_symm F hF
  have hdimE : Module.finrank E (primaryComponent Xend (p : F[X])) = 4 := by
    simpa [E, p0, p, hpval, primaryMultiplicity] using hm4
  let bfixE : Basis (Fin 4) E (primaryComponent Xend (p : F[X])) :=
    bfixF.mapCoeffs eEF.symm (by
      intro c v
      have hc : eEF.symm c = algebraMap F E c :=
        congrArg (fun f : F →+* E => f c) hEFsymm
      rw [hc]
      simp)
  let B : Subgroup SLX :=
    (linearSpecialBlock (slGL 6 F a) p0).comap (slGL 6 F)
  have hBfix : B =
      ((linearSpecialBlock (slGL 6 F a) p0).comap (slGL 6 F)) := rfl
  have hsq' : Squarefree (minpoly F
      ((slGL 6 F a : LinearMap.GeneralLinearGroup F V) : Module.End F V)) := by
    simpa [V, Xend, sl6End] using hsq
  have hhGL : p0 ∈ primaryFactors
      ((slGL 6 F a : LinearMap.GeneralLinearGroup F V) : Module.End F V) := by
    simpa [V, Xend, sl6End] using hmem
  let fB : B →* linearSpecialBlock (slGL 6 F a) p0 :=
    { toFun := fun b => ⟨slGL 6 F (b : SLX), b.2⟩
      map_one' := Subtype.ext (map_one (slGL 6 F))
      map_mul' := by
        intro b c
        exact Subtype.ext (map_mul (slGL 6 F) (b : SLX) (c : SLX)) }
  let eBHom : B →* SpecialLinearGroup E
      (primaryComponent Xend (p : F[X])) :=
    (linearSpecialBlockRestrict (x := slGL 6 F a) (h := p0)).comp fB
  have eB_inj : Function.Injective eBHom := by
    intro b c h
    apply Subtype.ext
    apply slGL_injective
    have hf : fB b = fB c := by
      apply linearSpecialBlockRestrict_injective hsq'
      exact h
    exact congrArg Subtype.val hf
  have eB_surj : Function.Surjective eBHom := by
    intro u
    obtain ⟨g, hg⟩ := linearSpecialBlockRestrict_surjective
      (x := slGL 6 F a) hsq' hhGL u
    obtain ⟨b, hb⟩ := linearSpecialBlock_le_range_slGL
      (n := 6) (k := F) (a := a) (hsq := hsq') (h := p0) (hh := hhGL) g.2
    refine ⟨⟨b, ?_⟩, ?_⟩
    · change slGL 6 F b ∈ linearSpecialBlock (slGL 6 F a) p0
      simpa [hb] using g.2
    · change ((linearSpecialBlockRestrict (x := slGL 6 F a) (h := p0)).comp fB)
        ⟨b, ?_⟩ = u
      simpa [fB, hb] using hg
  let eB : B ≃* SpecialLinearGroup E
      (primaryComponent Xend (p : F[X])) :=
    MulEquiv.ofBijective eBHom ⟨eB_inj, eB_surj⟩
  let e4 : Matrix.SpecialLinearGroup (Fin 4) F ≃* B :=
    (slMapEquiv4 eEF.symm).trans
      ((Matrix.SpecialLinearGroup.toLin_equiv bfixE).trans eB.symm)
  have hrangeH : H = B.map ψ := by
    simpa [B, p0] using
      ggF4N2K_fixedBlockRange_of_actualSL4_component
        hF hF₀ ψ hψ hker ha hH eH
  let ψBHom : B →* H :=
    { toFun := fun b => ⟨ψ (b : SLX), by
        rw [hrangeH]
        exact Subgroup.mem_map.mpr ⟨b, b.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one ψ)
      map_mul' := by
        intro b c
        exact Subtype.ext (map_mul ψ (b : SLX) (c : SLX)) }
  have hψBsurj : Function.Surjective ψBHom := by
    intro h
    have hh : (h : Q) ∈ B.map ψ := by
      simpa [hrangeH] using h.2
    obtain ⟨b, hbB, hb⟩ := Subgroup.mem_map.mp hh
    exact ⟨⟨b, hbB⟩, Subtype.ext hb⟩
  have hcardB : Nat.card B = Nat.card (Matrix.SpecialLinearGroup (Fin 4) F) :=
    (Nat.card_congr e4.toEquiv).symm
  have hcardH : Nat.card ↥H = Nat.card (Matrix.SpecialLinearGroup (Fin 4) F₀) :=
    Nat.card_congr eH.toEquiv
  have hcard_eq : Nat.card B = Nat.card ↥H := by
    rw [hcardB, hcardH, card_SL4_eq_of_card hF hF₀]
  have hψBbij : Function.Bijective ψBHom :=
    (Nat.bijective_iff_surjective_and_card ψBHom).mpr ⟨hψBsurj, hcard_eq⟩
  let ψB : B ≃* H := MulEquiv.ofBijective ψBHom hψBbij
  let e : ↥H ≃* Matrix.SpecialLinearGroup (Fin 4) F :=
    ψB.symm.trans e4.symm
  have hbV_inl (i : Fin 4) : bV (e46 (Sum.inl i)) = (bfixF i : V) := by
    simp only [bV, Basis.reindex_apply, e46, Equiv.symm_apply_apply]
    exact prodBasis_map_inl hcompl bfixF bOther i
  have hbV_inr (j : Fin 2) : bV (e46 (Sum.inr j)) = (bOther j : V) := by
    simp only [bV, Basis.reindex_apply, e46, Equiv.symm_apply_apply]
    exact prodBasis_map_inr hcompl bfixF bOther j
  have hPsymm (i : Fin 6) : P.symm (bV i) = Pi.single i (1 : F) := by
    ext j
    change bV.equivFun (bV i) j = (Pi.single i (1 : F) : Fin 6 → F) j
    rw [Basis.equivFun_apply, Basis.repr_self_apply]
    by_cases h : i = j
    · subst h
      simp
    · simp [Function.update, h]
  have hP (i : Fin 6) : P (Pi.single i (1 : F)) = bV i := by
    apply P.symm.injective
    rw [P.symm_apply_apply, hPsymm]

  refine ⟨A, e, ?_⟩
  intro g
  let u : SpecialLinearGroup E Vfix :=
    (Matrix.SpecialLinearGroup.toLin_equiv bfixE)
      (slMapEquiv4 eEF.symm g)
  have hmemB : slGL 6 F (e4 g : SLX) ∈
      linearSpecialBlock (slGL 6 F a) p0 := by
    have h := (e4 g).2
    change ((e4 g : B) : SLX) ∈
      (linearSpecialBlock (slGL 6 F a) p0).comap (slGL 6 F) at h
    rw [Subgroup.mem_comap] at h
    exact h
  have hres : linearSpecialBlockRestrict (x := slGL 6 F a) (h := p0)
      ⟨slGL 6 F (e4 g : SLX), hmemB⟩ = u := by
    change eB (e4 g) = u
    simp [e4, u]
  have hfixV (v : Vfix) :
      (slGL 6 F (e4 g) : V → V) (v : V) = (u v : V) := by
    rw [← CFSG.RankThree.CALinearPrimary.coe_linearSpecialBlockRestrict
      (g := (⟨slGL 6 F (e4 g : SLX), hmemB⟩ :
        linearSpecialBlock (slGL 6 F a) p0)) (v := v)]
    exact congrArg (fun x : SpecialLinearGroup E Vfix =>
      ((x v : Vfix) : V)) hres
  have hu (i : Fin 4) :
      (u (bfixF i) : V) = ∑ j : Fin 4,
        (g : Matrix (Fin 4) (Fin 4) F) j i • (bfixF j : V) := by
    have hb : bfixF i = bfixE i := by
      simp [bfixE]
    change (((Matrix.SpecialLinearGroup.toLin_equiv bfixE)
      (slMapEquiv4 eEF.symm g) : Vfix →ₗ[E] Vfix) (bfixF i) : V) = _
    rw [hb, Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq, Matrix.toLin_self]
    simp only [Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hc : eEF.symm ((g : Matrix (Fin 4) (Fin 4) F) j i) =
        algebraMap F E ((g : Matrix (Fin 4) (Fin 4) F) j i) :=
      congrArg (fun f : F →+* E => f ((g : Matrix (Fin 4) (Fin 4) F) j i)) hEFsymm
    have hm : ((slMapEquiv4 eEF.symm g : Matrix.SpecialLinearGroup (Fin 4) E) j i) =
        eEF.symm ((g : Matrix (Fin 4) (Fin 4) F) j i) := rfl
    rw [hm, hc,
      CFSG.RankThree.PartOne.KCPrimary.coe_algebraMap_smul_primaryComponent]
    rw [show ((bfixE j : Vfix) : V) = ((bfixF j : Vfix) : V) by simp [bfixE]]
  have hfixW (w : W) :
      (slGL 6 F (e4 g) : V → V) (w : V) = (w : V) := by
    obtain ⟨hc, ht, hd⟩ := hmemB
    have hWle : W ≤ LinearMap.ker
        (((slGL 6 F (e4 g) : Module.End F V) - 1)) := by
      refine iSup_le fun b => ?_
      intro v hv
      have hne : (b.1 : F[X]) ≠ p0 := by
        intro hb
        exact b.2 (Subtype.ext hb)
      have h := ht b.1.1 b.1.2 hne v hv
      simpa [LinearMap.mem_ker, sub_eq_zero] using h
    have h := hWle w.2
    simpa [LinearMap.mem_ker, sub_eq_zero] using h
  let blockLin : V ≃ₗ[F] V :=
    Matrix.SpecialLinearGroup.toLin' (CFSG.SeitzReduction.E6Pilot.blockFour (K := F) g)
  let bLin : V ≃ₗ[F] V :=
    (slGL 6 F (e4 g) : LinearMap.GeneralLinearGroup F V).toLinearEquiv
  have hconj : P * blockLin * P.symm = bLin := by
    apply LinearEquiv.toLinearMap_injective
    apply bV.ext
    intro i
    obtain ⟨s, rfl⟩ := e46.surjective i
    rcases s with x | j
    · change P (blockLin (P.symm (bV (e46 (Sum.inl x))))) =
        (slGL 6 F (e4 g) : Module.End F V) (bV (e46 (Sum.inl x)))
      calc
        P (blockLin (P.symm (bV (e46 (Sum.inl x))))) =
            P (blockLin (Pi.single (e46 (Sum.inl x)) (1 : F))) := by
          rw [hPsymm]
        _ = P (∑ y : Fin 4,
            (g : Matrix (Fin 4) (Fin 4) F) y x •
              Pi.single (e46 (Sum.inl y)) (1 : F)) := by
          rw [blockFour_toLin_inl]
        _ = ∑ y : Fin 4, (g : Matrix (Fin 4) (Fin 4) F) y x •
            P (Pi.single (e46 (Sum.inl y)) (1 : F)) := by
          rw [map_sum]
          simp [map_smul]
        _ = ∑ y : Fin 4, (g : Matrix (Fin 4) (Fin 4) F) y x •
            (bfixF y : V) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [hP, hbV_inl]
        _ = (u (bfixF x) : V) := (hu x).symm
        _ = (slGL 6 F (e4 g) : Module.End F V) (bfixF x : V) :=
          (hfixV (bfixF x)).symm
        _ = (slGL 6 F (e4 g) : Module.End F V)
            (bV (e46 (Sum.inl x))) := by
          rw [hbV_inl]
    · change P (blockLin (P.symm (bV (e46 (Sum.inr j))))) =
        (slGL 6 F (e4 g) : Module.End F V) (bV (e46 (Sum.inr j)))
      calc
        P (blockLin (P.symm (bV (e46 (Sum.inr j))))) =
            P (blockLin (Pi.single (e46 (Sum.inr j)) (1 : F))) := by
          rw [hPsymm]
        _ = P (Pi.single (e46 (Sum.inr j)) (1 : F)) := by
          rw [blockFour_toLin_inr]
        _ = bV (e46 (Sum.inr j)) := hP _
        _ = (bOther j : V) := hbV_inr j
        _ = (slGL 6 F (e4 g) : Module.End F V) (bOther j : V) :=
          (hfixW (bOther j)).symm
        _ = (slGL 6 F (e4 g) : Module.End F V)
            (bV (e46 (Sum.inr j))) := by
          rw [hbV_inr]
  have hA : Matrix.GeneralLinearGroup.toLin A =
      LinearMap.GeneralLinearGroup.ofLinearEquiv P := by
    simp [A]
  have hleft : (LinearMap.GeneralLinearGroup.ofLinearEquiv P * slGL 6 F
      (CFSG.SeitzReduction.E6Pilot.blockFour (K := F) g) *
      (LinearMap.GeneralLinearGroup.ofLinearEquiv P)⁻¹).toLinearEquiv =
      P * blockLin * P.symm := by
    rw [LinearMap.GeneralLinearGroup.toLinearEquiv_mul,
      LinearMap.GeneralLinearGroup.toLinearEquiv_mul,
      LinearMap.GeneralLinearGroup.toLinearEquiv_inv]
    have hP' : (LinearMap.GeneralLinearGroup.ofLinearEquiv P).toLinearEquiv = P := rfl
    have hBlock : (slGL 6 F
        (CFSG.SeitzReduction.E6Pilot.blockFour (K := F) g)).toLinearEquiv = blockLin := by
      rfl
    rw [hP', hBlock]
    rfl
  have hunit : Matrix.GeneralLinearGroup.toLin A * slGL 6 F
      (CFSG.SeitzReduction.E6Pilot.blockFour (K := F) g) *
      (Matrix.GeneralLinearGroup.toLin A)⁻¹ = slGL 6 F (e4 g) := by
    rw [hA]
    apply Units.ext
    apply LinearMap.ext
    intro v
    change (LinearMap.GeneralLinearGroup.ofLinearEquiv P * slGL 6 F
      (CFSG.SeitzReduction.E6Pilot.blockFour (K := F) g) *
      (LinearMap.GeneralLinearGroup.ofLinearEquiv P)⁻¹).toLinearEquiv v =
      ((slGL 6 F (e4 g)).toLinearEquiv) v
    rw [hleft]
    change (P * blockLin * P.symm) v = bLin v
    rw [hconj]
  have hsl : slGL 6 F
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
        6 F A (CFSG.SeitzReduction.E6Pilot.blockFour (K := F) g)) =
      slGL 6 F (e4 g) := by
    rw [slGL_slConjugation_local]
    exact hunit
  have hmatrix : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
      6 F A (CFSG.SeitzReduction.E6Pilot.blockFour (K := F) g) =
      (e4 g : SLX) := slGL_injective hsl
  have he : e.symm g = ψB (e4 g) := by
    change e4.trans ψB g = ψB (e4 g)
    rfl
  rw [hmatrix, he]
  rfl

end

end CFSG.StandardType
