module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2Defs
public import CFSG.Open.StatedDefs
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

import CFSG.Adapters.LieModelSimple
import CFSG.LocalAnalysis.GL83PartI.I713.UnitaryDiag
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.UniquenessCase.Lie.BorelSU
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.GH74.KGroups.L3EpsOuterLin
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Defs
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Quasithin.Background.RonanE111Defs
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66Sp
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open

theorem le_pRank_statedPSU_of_dvd_add_one {K : Type} [Field K] [Finite K] {q n ℓ : ℕ}
    (hK : Nat.card K = q ^ 2) (hℓ : ℓ.Prime) (hℓq : ℓ ∣ q + 1) (hn : 2 ≤ n) :
    n - 2 ≤ CFSG.Open.pRank ℓ (⊤ : Subgroup (StatedProj (StatedSU n q K))) := by
  classical
  rcases Nat.lt_or_ge n 3 with hn2 | hn3
  · have h0 : n - 2 = 0 := by omega
    rw [h0]
    exact Nat.zero_le _
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  have hq2 : 2 ≤ q := CFSG.Open.StatedCenterThree.two_le_of_card_eq_sq hK
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨ω, hω⟩ : ∃ ω : Kˣ, orderOf ω = ℓ := by
    refine exists_prime_orderOf_dvd_card' ℓ ?_
    rw [Nat.card_units, hK, CFSG.Open.StatedCenterThree.sq_sub_one_eq (by omega)]
    exact Dvd.dvd.mul_left hℓq _
  let μ : Subgroup Kˣ := Subgroup.zpowers ω
  have hμcard : Nat.card μ = ℓ := by
    dsimp only [μ]
    rw [Nat.card_zpowers, hω]
  have hμpow : ∀ x : μ, x ^ ℓ = 1 := by
    intro x
    have h1 : orderOf x ∣ Nat.card μ := orderOf_dvd_natCard x
    rw [hμcard] at h1
    exact orderOf_dvd_iff_pow_eq_one.1 h1
  have hμq : ∀ x : μ, (x : Kˣ) ^ (q + 1) = 1 := by
    intro x
    obtain ⟨t, ht⟩ := hℓq
    have h2 : (x : Kˣ) ^ ℓ = 1 := by
      simpa using congrArg (fun y : μ => (y : Kˣ)) (hμpow x)
    rw [ht, pow_mul, h2, one_pow]
  let A := (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_prodHom μ m).ker
  have hAcard : Nat.card A = ℓ ^ (m - 1) := by
    have h :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_card_ker_prod_mul μ hm1
    rw [hμcard] at h
    have hpow : ℓ ^ m = ℓ ^ (m - 1) * ℓ := by
      conv_lhs => rw [← Nat.sub_add_cancel hm1]
      rw [pow_succ]
    rw [hpow] at h
    exact Nat.eq_of_mul_eq_mul_right hℓ.pos h
  let snoc : (Fin m → Kˣ) →* (Fin (m + 1) → Kˣ) :=
    { toFun := fun x => Fin.snoc x 1
      map_one' := by
        funext i
        refine Fin.lastCases ?_ ?_ i <;> simp
      map_mul' := by
        intro x y
        funext i
        refine Fin.lastCases ?_ ?_ i <;> simp }
  let toUnits : A →* (Fin m → Kˣ) :=
    (MonoidHom.compLeft μ.subtype (Fin m)).comp A.subtype
  let toMat : A →* (Fin (m + 1) → Kˣ) := snoc.comp toUnits
  let F : A →* StatedSU (m + 1) q K :=
    { toFun := fun g => ⟨GL83.I713.UnitaryDiag.diagHomGL (Fin (m + 1)) K (toMat g), by
        refine GL83.I713.UnitaryDiag.diagHomGL_mem_statedSU (by omega) ?_ ?_
        · rw [Fin.prod_univ_castSucc]
          have hlast : toMat g (Fin.last m) = 1 := by simp [toMat, snoc]
          rw [hlast, mul_one]
          simpa [toMat, snoc, toUnits,
            CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_prodHom] using
            congrArg (fun y : μ => (y : Kˣ)) g.2
        · intro i
          refine Fin.lastCases ?_ ?_ i
          · simp [toMat, snoc]
          · intro j
            simpa [toMat, snoc, toUnits] using hμq (g.1 j)⟩
      map_one' := by
        apply Subtype.ext
        change GL83.I713.UnitaryDiag.diagHomGL (Fin (m + 1)) K (toMat 1) = 1
        rw [map_one, map_one]
      map_mul' := by
        intro g h
        apply Subtype.ext
        change GL83.I713.UnitaryDiag.diagHomGL (Fin (m + 1)) K (toMat (g * h)) =
          GL83.I713.UnitaryDiag.diagHomGL (Fin (m + 1)) K (toMat g) *
            GL83.I713.UnitaryDiag.diagHomGL (Fin (m + 1)) K (toMat h)
        rw [map_mul, map_mul] }
  let f : A →* StatedProj (StatedSU (m + 1) q K) :=
    (QuotientGroup.mk' ((StatedScalars (Fin (m + 1)) K).subgroupOf
      (StatedSU (m + 1) q K))).comp F
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have hqg : (QuotientGroup.mk (F g) : StatedProj (StatedSU (m + 1) q K)) =
        QuotientGroup.mk (1 : StatedSU (m + 1) q K) := by
      simpa [f, QuotientGroup.mk'_apply] using hg
    obtain ⟨u, hu⟩ := GL83.I713.UnitaryDiag.exists_unit_of_mk_eq_diagonal (g := F g)
      (g' := (1 : StatedSU (m + 1) q K)) (d := fun i => (toMat g i : K))
      (d' := fun _ => (1 : K)) (by exact GL83.I713.UnitaryDiag.coe_diagHomGL (toMat g)) (by
        rw [Subgroup.coe_one, Units.val_one, Matrix.diagonal_one]) hqg
    have hu1 : u = 1 := by
      have h := hu (Fin.last m)
      simp [toMat, snoc] at h
      exact Units.ext h.symm
    have hgj : ∀ j : Fin m, g.1 j = 1 := by
      intro j
      have h := hu (Fin.castSucc j)
      simp [toMat, snoc, toUnits, hu1] at h
      exact Subtype.ext (Units.ext h.symm)
    exact Subtype.ext (funext hgj)
  have hcomm : ∀ a b : A, a * b = b * a := fun a b => mul_comm a b
  have hpowA : ∀ a : A, a ^ ℓ = 1 := fun a =>
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_ker_pow (m := m) hμpow a
  have hk := CFSG.SectionRank.le_pRank_of_injective (p := ℓ)
    (G := StatedProj (StatedSU (m + 1) q K)) (H := ⊤) hℓ.one_lt hcomm hpowA
    (k := m - 1) hAcard f hf le_top
  rw [show m + 1 - 2 = m - 1 by omega]
  exact hk

theorem asch58UnitaryFive_holds :
    Asch58UnitaryFive := by
  intro X _ _ n hn hm
  obtain ⟨-, hcl | ⟨-, ⟨idx, hv⟩, hd, -⟩⟩ := hm
  · have hB : CFSG.Blueprint.LieModel X .PSU n 2 2 := Or.inl ⟨by decide, hcl⟩
    have hsimple : IsSimpleGroup X :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB
    obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := hcl
    have hfirst : 3 < CFSG.Open.pRank 5 (⊤ : Subgroup X) := by
      have hEq : CFSG.Open.pRank 5 (⊤ : Subgroup X) =
          CFSG.Open.pRank 5 (⊤ : Subgroup (StatedProj (StatedSU n (2 ^ 2) K))) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num) e
      have hrank := le_pRank_statedPSU_of_dvd_add_one (K := K) (q := 2 ^ 2)
        (n := n) (ℓ := 5) hKcard (by norm_num) (by norm_num) (by omega)
      omega
    have hnonab : ∃ a b : X, a * b ≠ b * a := by
      by_contra hcon
      have hcomm : IsMulCommutative X := ⟨⟨fun a b => by
        by_contra h
        exact hcon ⟨a, b, h⟩⟩⟩
      have hprime : (Nat.card X).Prime := Group.is_simple_iff_prime_card.mp hsimple
      obtain ⟨E, -, hE, hcardE⟩ :=
        CFSG.SectionRank.exists_pRank (p := 5) (G := X) (by norm_num) ⊤
      have h4 : 4 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup X) := hfirst
      have hdvdE : 5 ^ 4 ∣ Nat.card E := by
        rw [hcardE]
        exact pow_dvd_pow 5 h4
      have hdvdX : 5 ^ 4 ∣ Nat.card X :=
        hdvdE.trans (Subgroup.card_subgroup_dvd_card E)
      have h5dvd : 5 ∣ Nat.card X := (by norm_num : 5 ∣ 5 ^ 4).trans hdvdX
      have hcard5 : Nat.card X = 5 :=
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hprime).1 h5dvd).symm
      simp [hcard5] at hdvdX
    obtain ⟨hqC, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab
    have hq : CFSG.Open.IsQuasisimple X :=
      ⟨Group.isPerfect_def.mp hqC.1, hqC.2.1⟩
    have hLn : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSU n 2 2 :=
      CFSG.Blueprint.LieModel.of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans
          QuotientGroup.quotientBot).symm hB
    have hL : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSU
        (2 * 3 + (n - 6)) 2 2 := by
      rwa [show 2 * 3 + (n - 6) = n by omega]
    have hℓm : ¬ 5 ∣ 2 * 3 + (n - 6) := by
      rcases hn with rfl | rfl <;> norm_num
    have hWit := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwliu_borelWit_of_lieModel
      (X := X) hq (r := 3) (ε := n - 6) (n := 2) (by norm_num) (by omega)
      (by omega) (by norm_num) hL (by norm_num) (by norm_num) hℓm
    refine ⟨hfirst, ?_⟩
    intro S
    obtain ⟨F, hFle, hFabel, hFcard⟩ := hWit S
    have hle := CFSG.SectionRank.le_pRank (p := 5) (G := X)
      (H := Subgroup.normalizer ((S : Subgroup X) : Set X)) (E := F)
      (by norm_num) hFle hFabel hFcard
    have h2 : 2 ≤ 3 + (n - 6) - 1 := by omega
    omega
  · cases idx <;> simp only [CFSG.Models.NamesTag] at hd

end CFSG.LocalAnalysis.WeakClosure81
