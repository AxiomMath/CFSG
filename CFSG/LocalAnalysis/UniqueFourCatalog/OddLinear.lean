module

public import CFSG.LocalAnalysis.UniqueFourCatalog.OddClassicalGeneric
public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions
public import CFSG.LocalAnalysis.UniqueFourCatalog.Standing4Basic
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureOddLie
public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosureOddLinTwo
public import CFSG.RankThree.PartTwo.Census.OddClassical.LinearComponent
public import CFSG.RankThree.PartTwo.Census.OddClassical.LinearFourThree
public import CFSG.RankThree.PartOne.SLB4B.ModelL
public import CFSG.RankThree.PartOne.SLB4B.RankFourL
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Adapters.ClassicalCatalogReverse
public import CFSG.RankThree.PartTwo.Census.OddClassical.SmallThree
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionRankBound
public import CFSG.RankThree.PartOne.N143.SectionRankProof
public import CFSG.RankThree.PartOne.N143.SectionRankSplit
public import CFSG.RankThree.PartOne.N143.SectionReduce
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalLemmas
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
public import CFSG.RankThree.PartOne.S9.Sylow.ResidualLocal
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import Certificates.Certificate43
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

section PSLBlock

open Matrix CFSG.RankThree.PartOne.SLB4B CFSG.RankThree.PartTwo.Census
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (diagBlock diagBlock_mul diagBlock_one)
open scoped MatrixGroups

variable {F : Type} [Field F] {m : ℕ}

theorem conj_mem_range_blockHom (h2 : (2 : F) ≠ 0) {g : SpecialLinearGroup (Fin (4 + m)) F}
    (hg : g * signSL = signSL * g) (X : SpecialLinearGroup (Fin 4) F) :
    g * blockHom X * g⁻¹ ∈ (blockHom (F := F) (m := m)).range := by
  have hcomm : ∀ x : SpecialLinearGroup (Fin (4 + m)) F, x * signSL = signSL * x →
      ∃ A D, (x : Matrix (Fin (4 + m)) (Fin (4 + m)) F) = diagBlock A D := fun x hx =>
    eq_diagBlock_of_comm h2 (by
      have := congrArg Subtype.val hx
      change (x : Matrix (Fin (4 + m)) (Fin (4 + m)) F) * signMat =
        signMat * (x : Matrix (Fin (4 + m)) (Fin (4 + m)) F) at this
      exact this)
  have hg' : g⁻¹ * signSL = signSL * g⁻¹ := (Commute.inv_left hg).eq
  obtain ⟨A, D, hAD⟩ := hcomm g hg
  obtain ⟨A', D', hAD'⟩ := hcomm g⁻¹ hg'
  have hone := congrArg Subtype.val (mul_inv_cancel g)
  change (g : Matrix (Fin (4 + m)) (Fin (4 + m)) F) *
    ((g⁻¹ : SpecialLinearGroup (Fin (4 + m)) F) : Matrix (Fin (4 + m)) (Fin (4 + m)) F) = 1
    at hone
  rw [hAD, hAD', diagBlock_mul, ← diagBlock_one] at hone
  obtain ⟨hA, hD⟩ := diagBlock_injective hone
  have hdet : (A * (X : Matrix (Fin 4) (Fin 4) F) * A').det = 1 := by
    rw [det_mul, det_mul, X.2, mul_one, ← det_mul, hA, det_one]
  refine ⟨⟨A * X * A', hdet⟩, Subtype.ext ?_⟩
  change diagBlock (A * (X : Matrix (Fin 4) (Fin 4) F) * A') 1 =
    (g : Matrix (Fin (4 + m)) (Fin (4 + m)) F) * diagBlock (X : Matrix (Fin 4) (Fin 4) F) 1 *
      ((g⁻¹ : SpecialLinearGroup (Fin (4 + m)) F) : Matrix (Fin (4 + m)) (Fin (4 + m)) F)
  rw [hAD, hAD', diagBlock_mul, diagBlock_mul, Matrix.mul_one, hD]

theorem not_isCharTwoType_PSL_block_four [Finite F] (hodd : Odd (Nat.card F)) (hm : 1 ≤ m) :
    ¬ IsCharTwoType (ProjectiveSpecialLinearGroup (Fin (4 + m)) F) := by
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have hneg : (-1 : F) ≠ 1 := fun h => h2 (by linear_combination -h)
  have hq : CFSG.Open.IsQuasisimple ↥(blockHom (F := F) (m := m)).range := by
    have hq4 : CFSG.IsQuasisimple SL(4, F) :=
      CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by norm_num)
    exact CFSG.Open.IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective blockHom_injective).symm
      ⟨hq4.1.commutator_eq_top, hq4.2.1⟩
  refine not_isCharTwoType_quotient_of_quasisimple (H := SpecialLinearGroup (Fin (4 + m)) F) _
    le_rfl (t := signSL) (signSL_not_mem_center hm hneg)
    (by rw [signSL_sq]; exact Subgroup.one_mem _) (J := (blockHom (F := F) (m := m)).range)
    ?_ ?_ ?_ hq
  · rintro _ ⟨X, rfl⟩
    exact blockHom_comm_signSL X
  · rintro g hg _ ⟨X, rfl⟩
    exact conj_mem_range_blockHom h2 hg X
  · rw [eq_bot_iff]
    rintro _ hx
    obtain ⟨⟨X, rfl⟩, hc⟩ := Subgroup.mem_inf.mp hx
    have h1 : psl4Emb (F := F) (m := m) X = 1 := by
      rw [psl4Emb, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hc
    rw [psl4Emb_injective hm (h1.trans (map_one _).symm), map_one]
    exact Subgroup.one_mem _

end PSLBlock

section PSLTag

open Matrix CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Census
open CFSG.LocalAnalysis.RankThreeUC
  (localRank_le_one_of_forall_ne pRank_PSL_two_le not_commute_PSL_two_char_odd
    card_PSL_three_three cube_free_5616)

variable {G : Type} [Group G] [Finite G]

theorem false_of_PSL_two {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hS : Standing4 G) (hodd : Odd (Nat.card K))
    (e : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) : False := by
  refine hS.false_of_localRank_le_two e fun r hr hr2 => ?_
  have : Fact r.Prime := ⟨hr⟩
  by_cases hrp : r = p
  · subst hrp
    exact (localRank_le_one_of_forall_ne hr hr2
      (fun a t ha ht => not_commute_PSL_two_char_odd hr2 a t ha ht)).trans (by norm_num)
  · refine localRank_le_of_pRank_le hr (pRank_PSL_two_le hr hr2 ?_ hodd)
    intro h0
    have := (CharP.cast_eq_zero_iff K p r).mp (by exact_mod_cast h0)
    exact hrp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hr).mp this).symm

theorem false_of_statedPSL_odd (hS : Standing4 G) {n p f : ℕ} (hp : p ≠ 2)
    (h : StatedClassicalModel G .PSL n p f) : False := by
  obtain ⟨⟨hpp, hf, hn2, hn22, hn23⟩, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hpp⟩
  have hchar : CharP K p := CFSG.SectionRank.ClassicalOdd.charP_of_card hcard
  have hodd : Odd (Nat.card K) := by rw [hcard]; exact (hpp.odd_of_ne_two hp).pow
  let e' : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) K :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm
  by_cases hq3 : p ^ f = 3
  · have hK3 : Nat.card K = 3 := hcard.trans hq3
    have hp3 : p = 3 ∧ f = 1 := CFSG.ClassicalModels.eq_three_one_of_pow_eq_three hpp hf hq3
    have hn3 : 3 ≤ n := by
      by_contra hlt
      have : n = 2 := by omega
      subst this
      exact hn23 (by simp [hq3])
    rcases (show n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | h5
    · refine hS.false_of_card e' (N := 5616) {3} (card_PSL_three_three hK3) ?_ cube_free_5616
      intro _ r hr _ _
      obtain rfl : r = 3 := by simpa using hr
      exact localRank_three_PSL_three_le_of_card_eq_three hK3
    · have := Fintype.ofFinite K
      have := Fintype.ofFinite nineBase
      obtain ⟨rfl, rfl⟩ := hp3
      have hF : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card]; exact hK3
      let f' : nineBase ≃+* K :=
        (ZMod.ringEquiv (n := 3) nineBase fintype_card_nineBase).symm.trans
          (ZMod.ringEquiv (n := 3) K hF)
      let ψ : ProjectiveSpecialLinearGroup (Fin 2 × Fin 2) nineBase ≃*
          ProjectiveSpecialLinearGroup (Fin (3 + 1)) K :=
        pslCongr ((slRingEquiv f').trans (slReindexEquiv finProdFinEquiv))
      exact hS.false_of_not_isCharTwoType e'
        (fun h => not_isCharTwoType_PSL_four_three ((isCharTwoType_congr ψ).mpr h))
    · obtain ⟨m, rfl⟩ : ∃ m, n = 4 + m := ⟨n - 4, by omega⟩
      exact hS.false_of_not_isCharTwoType e' (not_isCharTwoType_PSL_block_four hodd (by omega))
  · have h4 : 4 ≤ Nat.card K := by
      have h1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hpp.one_lt
      obtain ⟨k, hk⟩ := hodd
      rw [hcard] at hk ⊢
      omega
    by_cases hn : n = 2
    · subst hn
      exact false_of_PSL_two hS hodd e'
    · obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
      exact hS.false_of_not_isCharTwoType e' (not_isCharTwoType_PSL_block h4 hodd (by omega))

end PSLTag

end CFSG.LocalAnalysis.UniqueFourCatalog
