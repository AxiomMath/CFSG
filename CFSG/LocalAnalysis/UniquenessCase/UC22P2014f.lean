module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2014d
public import CFSG.Open.SplitBNPair
public import CFSG.GroupTheory.TitsSystem.Basic
import CFSG.LocalAnalysis.UniquenessCase.UC22K108BigFix
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrPow
import CFSG.LocalAnalysis.UniquenessCase.UC22K108BN
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
import CFSG.Milestones.ASVolI.I2
import CFSG.Milestones.ASVolI.I2BNWeakClosure
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
public import CFSG.LocalAnalysis.UniquenessCase.UC22ListB
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2014b
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2014c
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.LocalAnalysis.UniquenessCase.UC6K620ExcFi22
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Permutation.UnitaryThreeRecognition.Model
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
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem CFSG.ASVolI.ChIJK Subgroup
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise

theorem uc22p2014f_map_zpow {X : Type} [Group X] {U : Subgroup X} {φ : MulAut X}
    (h : U.map φ.toMonoidHom = U) (i : ℤ) : U.map (φ ^ i).toMonoidHom = U := by
  have key : ∀ ψ : MulAut X, U.map ψ.toMonoidHom = U ↔
      ψ ∈ MulAction.stabilizer (MulAut X) U := fun ψ => by
    rw [MulAction.mem_stabilizer_iff]
    rfl
  exact (key _).2 (Subgroup.zpow_mem _ ((key φ).1 h) i)

theorem uc22p2014f_exists_fixed_of_isBNPair {X : Type} [Group X] [Finite X] {B N : Subgroup X}
    [(cartan B N).Normal] {S : Set (WeylGroup B N)} (hS : IsBNPair B N S) {U : Subgroup X}
    (hU : IsPGroup 2 U) (hUB : U ≤ B) (hNU : normalizer (U : Set X) = B)
    (hBUH : B ≤ U ⊔ (B ⊓ N)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y : Subgroup X}
    (hBY : B ≤ Y) (hY : Y ≠ ⊤) (φ : MulAut X) (hφ : ∃ k : ℕ, φ ^ (p ^ k) = 1)
    (hφU : U.map φ.toMonoidHom = U) : ∃ w ∉ Y, w⁻¹ * φ w ∈ B := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hconj : ∀ (K : Subgroup X) (a b : X), K.map (MulAut.conj (b * a)).toMonoidHom =
      (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom := fun K a b => by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  have hconjφ : ∀ (K : Subgroup X) (f : X ≃* X) (g : X),
      (K.map (MulAut.conj g).toMonoidHom).map f.toMonoidHom =
        (K.map f.toMonoidHom).map (MulAut.conj (f g)).toMonoidHom := fun K f g => by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [map_mul, map_inv]
  obtain ⟨n₀, -, hmax⟩ := CFSG.ASVolI.burnsideI25b_exists_max (B := B) (N := N) S S
  have hmax' : ∀ w, wordLength S w ≤ wordLength S (n₀ : WeylGroup B N) := fun w =>
    hmax w (hS.mem_closure w)
  have hQp : IsPGroup p (zpowers φ) := by
    obtain ⟨k, hk⟩ := hφ
    rintro ⟨a, ha⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ha
    refine ⟨k, Subtype.ext ?_⟩
    change (φ ^ i) ^ (p ^ k) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm i, zpow_mul, zpow_natCast, hk, one_zpow]
  have hQU : ∀ a : zpowers φ, U.map ((zpowers φ).subtype a).toMonoidHom = U := by
    rintro ⟨a, ha⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ha
    exact uc22p2014f_map_zpow hφU i
  have hQB : ∀ (a : zpowers φ) (x : X), (zpowers φ).subtype a x ∈ B ↔ x ∈ B := fun a x => by
    rw [← hNU]
    have h1 := Subgroup.map_equiv_normalizer_eq U ((zpowers φ).subtype a)
    rw [hQU a] at h1
    constructor
    · intro h
      rw [← h1, Subgroup.mem_map_equiv] at h
      simpa using h
    · intro h
      rw [← h1]
      exact ⟨x, h, rfl⟩
  obtain ⟨g, hg, hfix⟩ := F10.k108big_exists_conj_fixed hS (p := 2) (q := p) (Ne.symm hp2) hU
    hUB hNU.ge hBUH hmax' hQp (zpowers φ).subtype hQB hQU
  refine ⟨g, fun hgY => ?_, ?_⟩
  · obtain ⟨J, hJ, hYJ⟩ := hS.exists_parabolic hBY
    have hw₀J : (n₀ : WeylGroup B N) ∈ Subgroup.closure J :=
      (hS.mem_parabolic_iff_of_mem_dc hJ hg).1 (by rwa [hYJ] at hgY)
    have hJS : J = S := by
      refine Set.Subset.antisymm hJ fun s hs => ?_
      by_contra hsJ
      have := CFSG.ASVolI.burnsideI25b_length_lt_mul_right hS hJ hw₀J hs hsJ
      have := hmax' ((n₀ : WeylGroup B N) * s)
      omega
    exact hY (by rw [hYJ, hJS, hS.parabolic_univ])
  · have h1 := hfix ⟨φ, mem_zpowers φ⟩
    change (U.map (MulAut.conj g).toMonoidHom).map φ.toMonoidHom =
      U.map (MulAut.conj g).toMonoidHom at h1
    rw [hconjφ, hφU] at h1
    rw [← hNU, Subgroup.mem_normalizer_iff_map_conj_eq]
    change U.map (MulAut.conj (g⁻¹ * φ g)).toMonoidHom = U
    rw [hconj, h1, ← hconj, inv_mul_cancel]
    ext x
    simp

theorem uc22p2014f_exists_fixed {X : Type} [Group X] [Finite X] {B₀ N₀ : Subgroup X}
    (hBN : IsSplitBNPair 2 B₀ N₀) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y : Subgroup X}
    (hY : Y ≠ ⊤) (U : Sylow 2 X) (hUY : normalizer ((U : Subgroup X) : Set X) ≤ Y)
    (φ : MulAut X) (hφ : ∃ k : ℕ, φ ^ (p ^ k) = 1)
    (hφU : (U : Subgroup X).map φ.toMonoidHom = U) :
    ∃ w ∉ Y, w⁻¹ * φ w ∈ normalizer ((U : Subgroup X) : Set X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U₀, hU₀B, hU₀n, hU₀p, hU₀i, -, hU₀H, -⟩ := hBN.split
  have hsyl₀ : IsSylowTwoOf U₀ ⊤ := ⟨le_top, hU₀p, by
    change ¬ 2 ∣ U₀.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hU₀i⟩
  have hsyl : IsSylowTwoOf (U : Subgroup X) ⊤ := ⟨le_top, U.isPGroup', by
    change ¬ 2 ∣ (U : Subgroup X).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact U.not_dvd_index⟩
  obtain ⟨c, -, hc⟩ := hsyl₀.exists_conj hsyl
  have hfinj : Function.Injective (MulAut.conj c).toMonoidHom := (MulAut.conj c).injective
  have hBN' : IsSplitBNPair 2 (B₀.map (MulAut.conj c).toMonoidHom)
      (N₀.map (MulAut.conj c).toMonoidHom) :=
    burnsideI2BN_map hBN _ (MulAut.conj c).surjective
      (by rw [(MonoidHom.ker_eq_bot_iff _).2 hfinj]; exact bot_le)
  haveI : (cartan (B₀.map (MulAut.conj c).toMonoidHom)
      (N₀.map (MulAut.conj c).toMonoidHom)).Normal := hBN'.normal_inter
  obtain ⟨S, hS⟩ := burnsideI2BN_exists_isBNPair (burnsideI2BN_toPre hBN')
  have hUB : (U : Subgroup X) ≤ B₀.map (MulAut.conj c).toMonoidHom := by
    rw [hc]
    exact Subgroup.map_mono hU₀B
  have hBU : B₀.map (MulAut.conj c).toMonoidHom ≤ normalizer ((U : Subgroup X) : Set X) := by
    rw [hc, ← Subgroup.map_equiv_normalizer_eq U₀ (MulAut.conj c)]
    exact Subgroup.map_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer hU₀B).1 hU₀n)
  have hNU := uc22k108bn_normalizer_eq Nat.prime_two hBN' hUB
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hUB).2 hBU) U.isPGroup' U.not_dvd_index
  have hBUH : B₀.map (MulAut.conj c).toMonoidHom ≤ (U : Subgroup X) ⊔
      (B₀.map (MulAut.conj c).toMonoidHom ⊓ N₀.map (MulAut.conj c).toMonoidHom) := by
    rw [hc, ← Subgroup.map_inf_eq _ _ _ hfinj, ← Subgroup.map_sup, hU₀H]
  obtain ⟨w, hw, hwB⟩ := uc22p2014f_exists_fixed_of_isBNPair hS U.isPGroup' hUB hNU hBUH hp hp2
    (by rw [← hNU]; exact hUY) hY φ hφ hφU
  exact ⟨w, hw, by rw [hNU]; exact hwB⟩

theorem uc22p2014f_exists_map_eq {G : Type} [Group G] [Finite G] (D : Data G) {L : Subgroup G}
    (S : Sylow 2 (Bar2 L))
    (hS : normalizer ((S : Subgroup (Bar2 L)) : Set (Bar2 L)) ≤ barImage L (D.M ⊓ L)) {y : G}
    (hyL : y ∈ normalizer (L : Set G)) (hyM : y ∈ D.M) :
    ∃ a ∈ D.M, ∃ haL : a ∈ L, (S : Subgroup (Bar2 L)).map
      (UC6S846.rhoL L (⟨a, Subgroup.le_normalizer haL⟩ * ⟨y, hyL⟩)).toMonoidHom = S := by
  have hyML : y ∈ normalizer ((D.M ⊓ L : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hyM, hyL⟩
  obtain ⟨j, hj, hjS⟩ := CFSG.AGLEmbedding.ParabAutIrr.exists_conj_mul_normalizes S
    (Subgroup.le_normalizer.trans hS) _ (uc22p2014d_map_barImage hyL hyML)
  obtain ⟨⟨a, haL⟩, ha, rfl⟩ := hj
  refine ⟨a, (Subgroup.mem_subgroupOf.1 ha).1, haL, ?_⟩
  rw [map_mul, UC6S846.rhoL_inner L a haL]
  rwa [QuotientGroup.mk'_apply] at hjS

end CFSG.LocalAnalysis.UniquenessCase.UC22
