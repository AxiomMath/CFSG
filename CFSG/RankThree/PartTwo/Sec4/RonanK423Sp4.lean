module

public import CFSG.RankThree.PartTwo.Sec4.RonanK423Decomp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.DataGlue
public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofSp4
public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoSpFour
public import CFSG.RankThree.PartTwo.Sec8.Item84KFacts4ProofSp4Tensor
public import CFSG.RankThree.PartTwo.KFacts.K71Sp48Graph
public import CFSG.LieType.SeitzGeneration.SpFourThree
public import CFSG.RankThree.PartTwo.Sec8.Item86Res2ProofIndep

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK423

open CFSG CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartTwo.Sec8.Item84KFacts4
open CFSG.RankThree.PartTwo.KFacts (sp4T sp4TT sp4Graph exists_conj_eq_sp4TT
  exists_mulAut_apply_sp4T_eq exists_conj_sp4Graph_sp4T center_statedSp_eq_bot
  sp4Graph_sp4T_sq_add_add_one)
open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.LieType.SeitzGeneration (closure_centralizers_spFour_three)
open CFSG.AGLEmbeddingD2.Wilson.Census423Three (census423_of_equiv_alpha)
open CFSG.GH74.GLS.IVK.GHInv (isQuasisimple_sl2)
open CFSG.RankThree.PartTwo.Sec8.Item86ResProof (center_specialLinearGroup_two_eq_bot)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (leviEmbedSL leviEmbedSL_injective)
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem yTMat_sq_add_add_one :
    yTMat F ^ 2 + yTMat F + 1 = 0 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [pow_two, yTMat, wMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      CharTwo.add_self_eq_zero]

theorem yT_pow_three : yT F ^ 3 = 1 := by
  apply mat_injective
  rw [map_pow, mat_yT, map_one]
  have h := yTMat_sq_add_add_one (F := F)
  have h2 : yTMat F ^ 3 - 1 = (yTMat F - 1) * (yTMat F ^ 2 + yTMat F + 1) := by noncomm_ring
  rw [h, mul_zero, sub_eq_zero] at h2
  exact h2

theorem yT_ne_one : yT F ≠ 1 := by
  intro h
  have h1 := congrArg (mat 2 F) h
  rw [mat_yT, map_one] at h1
  have h2 := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F => M (Sum.inl 0) (Sum.inr 1)) h1
  simp [yTMat, wMat] at h2

theorem exists_mulAut_apply_yT_eq {x : StatedSp 2 F} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ φ : MulAut (StatedSp 2 F), φ (yT F) = x := by
  obtain ⟨φ₀, hφ₀⟩ := exists_mulAut_apply_sp4T_eq hx3 hx1
  obtain ⟨g, hg⟩ := exists_conj_sp4Graph_sp4T (F := F)
  obtain ⟨h, hh⟩ := exists_conj_eq_sp4TT (x := yT F) yT_pow_three yT_ne_one
    (by rw [show ((yT F : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) = _ from rfl]; exact yTMat_sq_add_add_one)
  have hy : yT F = (h * g⁻¹) * sp4Graph F (sp4T F) * (h * g⁻¹)⁻¹ := by
    rw [hg, hh]
    group
  have h1 : (MulAut.conj (h * g⁻¹)).symm (yT F) = sp4Graph F (sp4T F) := by
    rw [MulEquiv.symm_apply_eq, MulAut.conj_apply]
    exact hy
  refine ⟨(MulAut.conj (h * g⁻¹)).symm.trans ((sp4Graph F).symm.trans φ₀), ?_⟩
  show φ₀ ((sp4Graph F).symm ((MulAut.conj (h * g⁻¹)).symm (yT F))) = x
  rw [h1, MulEquiv.symm_apply_apply, hφ₀]

theorem derived_centralizer_yT (hF : 4 ≤ Nat.card F) :
    ⁅Subgroup.centralizer ({yT F} : Set (StatedSp 2 F)),
      Subgroup.centralizer ({yT F} : Set (StatedSp 2 F))⁆ = (leviEmbedSL F 2).range := by
  set C := Subgroup.centralizer ({yT F} : Set (StatedSp 2 F)) with hC
  have hperf : Group.IsPerfect SL(2, F) := (isQuasisimple_sl2 hF).1
  have hLperf : Group.IsPerfect (leviEmbedSL F 2).range :=
    Group.IsPerfect.ofSurjective (f := (leviEmbedSL F 2).rangeRestrict)
      (leviEmbedSL F 2).rangeRestrict_surjective
  apply le_antisymm
  · refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    rw [commutatorElement_def]
    exact commutator_mem_range_levi hx hy
  · calc (leviEmbedSL F 2).range = ⁅(leviEmbedSL F 2).range, (leviEmbedSL F 2).range⁆ :=
          (Subgroup.isPerfect_iff.mp hLperf).symm
      _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono range_levi_le_centralizer range_levi_le_centralizer

theorem centralProductData_centralizer_yT (hF : 4 ≤ Nat.card F) :
    CentralProductData (Subgroup.centralizer ({yT F} : Set (StatedSp 2 F))) := by
  set C := Subgroup.centralizer ({yT F} : Set (StatedSp 2 F)) with hC
  have hRL := derived_centralizer_yT hF
  have hLC : (leviEmbedSL F 2).range ≤ C := range_levi_le_centralizer
  have eL := MonoidHom.ofInjective (leviEmbedSL_injective (K := F) (n := 2))
  refine ⟨?_, ?_, ?_⟩
  · rw [hRL]
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr eL).1 (isQuasisimple_sl2 hF)
  · rw [hRL]
    intro z hz
    refine ⟨0, ?_⟩
    have hcen := Subgroup.map_center_eq eL
    rw [center_specialLinearGroup_two_eq_bot, Subgroup.map_bot] at hcen
    rw [← hcen, Subgroup.mem_bot] at hz
    simp [hz]
  · refine ⟨(Subgroup.center ↥C).map C.subtype, ?_, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp ha' a)
      simpa using this
    · rintro _ ⟨a, ha, rfl⟩ r hr
      have hrC : r ∈ C := derived_le C hr
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp ha ⟨r, hrC⟩)
      simpa using this.symm
    · intro x hx
      obtain ⟨α, β, B, hB⟩ := exists_decomp_of_mem_centralizer_yT hx
      set s := leviEmbedSL F 2 B with hs
      have hsL : s ∈ (leviEmbedSL F 2).range := ⟨B, rfl⟩
      have hsC : s ∈ C := hLC hsL
      set t := x * s⁻¹ with ht
      have htC : t ∈ C := C.mul_mem hx (C.inv_mem hsC)
      have hmt : mat 2 F t = α • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) + β • yTMat F := by
        rw [ht, map_mul, hB, Matrix.mul_assoc, ← map_mul, mul_inv_cancel, map_one, Matrix.mul_one]
      have hxt : x = t * s := by rw [ht, inv_mul_cancel_right]
      clear_value t
      have htz : (⟨t, htC⟩ : ↥C) ∈ Subgroup.center ↥C := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨α', β', B', hB'⟩ := exists_decomp_of_mem_centralizer_yT y.2
        apply Subtype.ext
        show (y : StatedSp 2 F) * t = t * (y : StatedSp 2 F)
        apply mat_injective
        rw [map_mul, map_mul, hmt, hB']
        have c3 := commute_poly_poly α β α' β'
        have c4 := commute_poly_levi α β B'
        exact (c3.mul_right c4).eq.symm
      have htA : t ∈ (Subgroup.center ↥C).map C.subtype := ⟨⟨t, htC⟩, htz, rfl⟩
      rw [hRL, sup_comm, hxt]
      exact Subgroup.mul_mem_sup htA hsL

theorem exists_ne_zero_ne_one {K : Type} [Field K] [Finite K] (h : 4 ≤ Nat.card K) :
    ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have : Fintype K := Fintype.ofFinite K
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun c _ => by
    by_cases hc : c = 0
    · simp [hc]
    · simp [hcon c hc]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
  omega

theorem census423_of_sp4 {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 1 ≤ n)
    (e : X ≃* projSp 2 (GaloisField 2 n)) (hq : CFSG.IsQuasisimple X) : Census423 X := by
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · obtain rfl : n = 1 := by omega
    exact (RonanKChevTwo.SpFour.false_of_isQuasisimple_projSp_two_one hq e).elim
  · have hn0 : n ≠ 0 := by omega
    have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
    have hF4 : 4 ≤ Nat.card (GaloisField 2 n) := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have h3 : (3 : GaloisField 2 n) ≠ 0 := by
      have h31 : (3 : GaloisField 2 n) = 1 := by
        have h2 : (2 : GaloisField 2 n) = 0 := CharTwo.two_eq_zero
        linear_combination h2
      rw [h31]
      exact one_ne_zero
    set e' : X ≃* StatedSp 2 (GaloisField 2 n) :=
      e.trans (Res417Six.projSpEquivSp (GaloisField 2 n)) with he'
    refine census423_of_equiv_alpha e' ?_
    intro D hDc hDexp hD9
    have hq' : CFSG.IsQuasisimple (StatedSp 2 (GaloisField 2 n)) :=
      (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e').1 hq
    refine alphaVanishes_of_centralProduct hq' center_statedSp_eq_bot hDc hDexp hD9
      (fun b hbD hb1 => ?_)
      (closure_centralizers_spFour_three h3 (exists_ne_zero_ne_one hF4) hDc hDexp hD9).ge
    obtain ⟨φ, hφ⟩ := exists_mulAut_apply_yT_eq (hDexp b hbD) hb1
    rw [← hφ]
    exact (centralProductData_centralizer_yT hF4).of_map φ

end CFSG.RankThree.PartTwo.Sec4.RonanK423
