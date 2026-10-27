module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDADefs
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
import all CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympInner
import CFSG.LieType.Universal.Symplectic
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6
import CFSG.RankThree.PartOne.KC.SymplecticIsotypicFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.StandardType.SCFourCover

open Polynomial CFSG.Open CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

section Helpers

open CFSG.RankThree.PartOne.KCPrimary

variable {r g : ℕ} {K : Type} [Field K]

private theorem charP_two_kglSpF [Finite K] (hK : Nat.card K = 2 ^ g) : CharP K 2 := by
  haveI := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := g) (by rw [Fintype.card_eq_nat_card, hK])

private theorem nontrivial_kglSpF {T : Type*} [Group T] (h : CFSG.Open.IsQuasisimple T) :
    Nontrivial T := by
  haveI := h.2
  exact (QuotientGroup.mk'_surjective (Subgroup.center T)).nontrivial

private theorem not_isSolvable_kglSpF {T : Type*} [Group T] (h : CFSG.Open.IsQuasisimple T) :
    ¬ Group.IsSolvable T := by
  haveI := nontrivial_kglSpF h
  haveI : Group.IsPerfect T := Group.isPerfect_def.mpr h.1
  exact Group.IsPerfect.not_isSolvable T

private theorem spSupported_eq_bot_kglSpF {x : StatedSp r K}
    (hsq : Squarefree (minpoly K (spEnd x))) {h : K[X]} (hh : h ∉ primaryFactors (spEnd x)) :
    spSupported x {h} = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  apply spLin_injective
  apply Units.ext
  rw [map_one]
  change spEnd u = 1
  refine ext_primaryComponent hsq (f := spEnd u) (g := 1) fun k hk v hv => ?_
  rw [Module.End.one_apply]
  refine (mem_spSupported.mp hu).2 k hk ?_ v hv
  rw [Set.mem_singleton_iff]
  rintro rfl
  exact hh hk

private theorem spSupported_one_kglSpF (hr : 1 ≤ r) :
    spSupported (1 : StatedSp r K) {X - 1} = ⊤ := by
  rw [eq_top_iff]
  intro u _
  refine mem_spSupported.mpr ⟨by rw [mul_one, one_mul], fun k hk hkO => absurd ?_ hkO⟩
  haveI : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, hr⟩⟩
  obtain ⟨hki, hkm, hkd⟩ := mem_primaryFactors.mp hk
  have h1 : spEnd (1 : StatedSp r K) = 1 := by simp [spEnd]
  rw [h1, minpoly.one] at hkd
  exact eq_of_monic_of_associated hkm CFSG.RankThree.Classical.monic_X_sub_one
    (hki.associated_of_dvd CFSG.RankThree.Classical.irreducible_X_sub_one hkd)

private theorem exists_orbitPart_kglSpF {ℓ f p n : ℕ} {x y : StatedSp r K}
    {a : StatedProj (StatedSp r K)} (blocks : SpPrimaryBlocks ℓ f p x a) (hy : Commute y x)
    (hyn : y ^ n = 1) (O : ↥(reciprocalOrbits (spEnd x))) :
    ∃ z ∈ spSupported x (O : Set K[X]), z ^ n = 1 ∧
      ∀ j ∈ spSupported x (O : Set K[X]), Commute (z⁻¹ * y) j := by
  classical
  haveI : Finite ↥(reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  haveI := Fintype.ofFinite ↥(reciprocalOrbits (spEnd x))
  obtain ⟨hcomm, hind, hjoin⟩ := blocks.directProduct
  have hpair : Pairwise fun i j : ↥(reciprocalOrbits (spEnd x)) => ∀ u v : StatedSp r K,
      u ∈ spSupported x (i : Set K[X]) → v ∈ spSupported x (j : Set K[X]) → Commute u v :=
    fun i j hij u v hu hv => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) u hu v hv
  obtain ⟨φ, hφ⟩ : y ∈ (Subgroup.noncommPiCoprod hpair).range := by
    rw [Subgroup.noncommPiCoprod_range, hjoin]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hy
  have hφn : φ ^ n = 1 := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hpair) hind
    (by rw [map_pow, hφ, hyn, map_one])
  refine ⟨φ O, (φ O).2, by simpa using congrArg Subtype.val (congrFun hφn O), fun j hj => ?_⟩
  have hc : Commute ((Pi.mulSingle O (φ O))⁻¹ * φ) (Pi.mulSingle O ⟨j, hj⟩) := by
    refine Pi.commute_iff.mpr fun i => ?_
    rcases eq_or_ne i O with rfl | hi
    · simp
    · simp [Pi.mulSingle_eq_of_ne hi]
  have h := congrArg (Subgroup.noncommPiCoprod hpair) hc.eq
  simp only [map_mul, map_inv, Subgroup.noncommPiCoprod_mulSingle, hφ] at h
  exact h

private theorem mem_commutator_kglSpF [Finite K] {G : Type*} [Group G] {A : Subgroup G} {s : ℕ}
    (hK : Nat.card K = 2 ^ g) (e : A ≃* StatedSp s K) (hns : ¬ Group.IsSolvable ↥⁅A, A⁆)
    {w : G} (hw : w ∈ A) (hw3 : w ^ 3 = 1) : w ∈ ⁅A, A⁆ := by
  have hsol : ¬ Group.IsSolvable ↥A := fun _ => hns (Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective (Subgroup.commutator_le_self A)))
  haveI : Finite ↥A := Finite.of_equiv _ e.symm.toEquiv
  have hcard := (Nat.card_congr e.toEquiv).trans
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := K) s)
  rw [← Subgroup.map_subtype_commutator]
  refine ⟨⟨w, hw⟩, ?_, rfl⟩
  obtain hs | hs := Nat.eq_zero_or_pos s
  · subst hs
    haveI : Subsingleton ↥A := (Nat.card_eq_one_iff_unique.mp (by simpa using hcard)).1
    exact (hsol inferInstance).elim
  by_cases hq : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ s) ∨
      (Nat.card K = 2 ∧ 3 ≤ s)
  · haveI : Group.IsPerfect ↥(StatedSp s K) :=
      (CFSG.LieType.Universal.Symplectic.isQuasisimple s K hs hq).1
    haveI : Group.IsPerfect ↥A :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact Group.IsPerfect.mem_commutator
  have hK4 : Nat.card K < 4 := by
    by_contra h
    exact hq (Or.inl (Or.inr (by omega)))
  have hK2 : Nat.card K = 2 := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at h1 hK4 ⊢
    rcases g with _ | _ | g
    · simp at h1
    · rfl
    · rw [pow_succ, pow_succ] at hK4
      have := Nat.one_le_two_pow (n := g)
      omega
  rcases (show s = 1 ∨ s = 2 by
      by_contra h
      exact hq (Or.inr (Or.inr ⟨hK2, by omega⟩))) with rfl | rfl
  · refine absurd ?_ hsol
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.isSolvable_of_card_two_three
      (a := 1) (b := 1) one_ne_zero one_ne_zero (by rw [hcard, hK2]; norm_num [Finset.Icc_self])
  · have hd : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    obtain ⟨E⟩ := CFSG.RankThree.PartOne.nonempty_mulEquiv_sympFour hK2
      (CFSG.RankThree.Classical.spForm_isAlt (r := 2) (K := K))
      (CFSG.RankThree.Classical.spForm_nondegenerate (r := 2) (K := K)) hd
    let e₀ : StatedSp 2 K ≃* CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup (spForm 2 K) :=
      (MonoidHom.ofInjective (CFSG.RankThree.Classical.spLin_injective (r := 2) (K := K))).trans
        (MulEquiv.subgroupCongr (CFSG.RankThree.Classical.range_spLin (r := 2) (K := K)))
    exact (CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour ((e.trans e₀).trans E)).2
      Nat.prime_three (by norm_num) _ (Subtype.ext (by simpa using hw3))

end Helpers

theorem ggInnerOn_sp_fixed {r g : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ g)
    (hr : 2 ≤ r) {x y : StatedSp r K} (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxy : Commute x y)
    (hT : CFSG.Open.IsComponentOf
      ((⁅spSupported x {X - 1}, spSupported x {X - 1}⁆).map (proj r K))
      (fixSubgroup (MulAut.conj (proj r K x)))) :
    GGInnerOn ((⁅spSupported x {X - 1}, spSupported x {X - 1}⁆).map (proj r K))
      (MulAut.conj (proj r K y)) := by
  classical
  haveI := charP_two_kglSpF hK
  haveI : NeZero r := ⟨by omega⟩
  obtain ⟨y₁, hy₁, hy₁3, hy₁c, s, ⟨e⟩⟩ : ∃ y₁ ∈ spSupported x {X - 1}, y₁ ^ 3 = 1 ∧
      (∀ j ∈ spSupported x {X - 1}, Commute (y₁⁻¹ * y) j) ∧
      ∃ s, Nonempty (spSupported x {X - 1} ≃* StatedSp s K) := by
    rcases eq_or_ne x 1 with rfl | hx1
    · have htop := spSupported_one_kglSpF (K := K) (r := r) (by omega)
      exact ⟨y, by rw [htop]; exact Subgroup.mem_top y, hy3,
        fun j _ => by rw [inv_mul_cancel]; exact Commute.one_left j, r,
        ⟨(MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv⟩⟩
    have h3K : ((3 : ℕ) : K) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff K 2]
      norm_num
    have hsq := (altPrimaryData_spLin h3K hx3).squarefree
    have hh : (X - 1 : K[X]) ∈ CFSG.RankThree.PartOne.KCPrimary.primaryFactors (spEnd x) := by
      by_contra hX
      apply (Subgroup.nontrivial_iff_ne_bot _).mp (nontrivial_kglSpF hT.2.2)
      rw [spSupported_eq_bot_kglSpF hsq hX, Subgroup.commutator_bot_left, Subgroup.map_bot]
    have hx1' : proj r K x ≠ 1 := fun h => hx1
      ((CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
        (r := r) (K := K)).1 (h.trans (map_one _).symm))
    have hg1 : 1 ≤ g := Nat.pos_of_ne_zero (by
      rintro rfl
      have := Finite.one_lt_card (α := K)
      rw [hK] at this
      norm_num at this)
    have blocks := (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hg1 hK
      Nat.prime_three (by norm_num) (by norm_num) (by omega) _
      (orderOf_eq_prime (by rw [← map_pow, hx3, map_one]) hx1')).2 x rfl
      (orderOf_eq_prime hx3 hx1)
    have hO : ({X - 1} : Set K[X]) ∈ reciprocalOrbits (spEnd x) :=
      ⟨X - 1, hh, by dsimp only; rw [reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton]⟩
    obtain ⟨y₁, hy₁, hy₁3, hy₁c⟩ := exists_orbitPart_kglSpF blocks hxy.symm hy3 ⟨_, hO⟩
    obtain ⟨φ, -⟩ := blocks.fixedFactor hh
    obtain ⟨s, -, ⟨e⟩⟩ :=
      CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp
        (B := (spForm r K).restrict
          (CFSG.RankThree.PartOne.KCPrimary.primaryComponent (spEnd x) (X - 1)))
        (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)) blocks.fixed_nondegenerate
    exact ⟨y₁, hy₁, hy₁3, hy₁c, s, ⟨φ.trans e⟩⟩
  have hns : ¬ Group.IsSolvable ↥⁅spSupported x {X - 1}, spSupported x {X - 1}⁆ := fun _ =>
    not_isSolvable_kglSpF hT.2.2
      (Group.isSolvable_of_surjective ((proj r K).subgroupMap_surjective _))
  refine ⟨proj r K y₁, Subgroup.mem_map_of_mem _ (mem_commutator_kglSpF hK e hns hy₁ hy₁3), ?_⟩
  rintro _ ⟨j, hj, rfl⟩
  have hc := hy₁c j (Subgroup.commutator_le_self _ hj)
  have key : y * j * y⁻¹ = y₁ * j * y₁⁻¹ :=
    calc y * j * y⁻¹ = y₁ * ((y₁⁻¹ * y) * j * (y₁⁻¹ * y)⁻¹) * y₁⁻¹ := by group
      _ = y₁ * j * y₁⁻¹ := by rw [hc.mul_inv_cancel]
  simpa only [MulAut.conj_apply, map_mul, map_inv] using congrArg (proj r K) key

end CFSG.StandardType.SCFourCover

end
