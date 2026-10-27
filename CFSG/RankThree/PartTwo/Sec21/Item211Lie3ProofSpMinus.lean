module

public import CFSG.RankThree.PartTwo.Sec21.Item211Lie3ProofQuat
public import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofExcRed
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofU42Char
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
public import CFSG.RankThree.PartTwo.Late.GammaZero
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec11.Theorem1134
public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec21.Item229Diagram
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools
public import CFSG.RankThree.PartTwo.Sec21.Membership
public import CFSG.RankThree.PartTwo.Sec21.SylowThree
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank
open Matrix

namespace Item211Lie3Proof

open Item211Lie2Proof

local notation "V₄" => Fin 2 ⊕ Fin 2

section Model

variable {K : Type} [Field K]

theorem sq_eq_one_of_scalar_mem {c : Kˣ}
    (hc : Matrix.GeneralLinearGroup.scalar V₄ c ∈ StatedSp 2 K) : (c : K) * c = 1 := by
  have h := CFSG.RankThree.SubgroupLists.transpose_mul_spGram_mul hc
  have e := congrFun (congrFun h (Sum.inl 0)) (Sum.inr 0)
  simp [Matrix.GeneralLinearGroup.coe_scalar, CFSG.RankThree.SubgroupLists.spGram,
    Matrix.mul_apply, fromBlocks] at e
  exact e

theorem mk_eq_mk_iff_sp {g g' : StatedSp 2 K} :
    (g : StatedProj (StatedSp 2 K)) = (g' : StatedProj (StatedSp 2 K)) ↔
      (g' : GL V₄ K) = g ∨ (g' : GL V₄ K) = -g := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨c, hc⟩
    have hmem : Matrix.GeneralLinearGroup.scalar V₄ c ∈ StatedSp 2 K := by
      rw [hc]
      exact (g⁻¹ * g').2
    have hc2 := sq_eq_one_of_scalar_mem hmem
    have hg' : (g' : GL V₄ K) = g * Matrix.GeneralLinearGroup.scalar V₄ c := by
      rw [hc, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rcases mul_self_eq_one_iff.mp hc2 with h1 | h1
    · left
      have : c = 1 := Units.ext h1
      rw [hg', this, map_one, mul_one]
    · right
      have : c = -1 := Units.ext (by rw [h1, Units.val_neg, Units.val_one])
      rw [hg', this]
      apply Units.ext
      rw [Units.val_mul, Units.val_neg, Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg,
        Units.val_one, map_neg, map_one, Matrix.mul_neg, Matrix.mul_one]
  · rintro (h | h)
    · refine ⟨1, ?_⟩
      rw [map_one, Subgroup.coe_mul, Subgroup.coe_inv, h, inv_mul_cancel]
    · refine ⟨-1, ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_inv, h, mul_neg, inv_mul_cancel]
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one, Units.val_neg,
        Units.val_one, map_neg, map_one]

theorem mk_eq_one_iff_sp {g : StatedSp 2 K} :
    (g : StatedProj (StatedSp 2 K)) = 1 ↔ (g : GL V₄ K) = 1 ∨ (g : GL V₄ K) = -1 := by
  rw [← QuotientGroup.mk_one, eq_comm, mk_eq_mk_iff_sp, Subgroup.coe_one]

theorem comm_or_anticomm_of_mk {g g' : StatedSp 2 K}
    (h : (g : StatedProj (StatedSp 2 K)) * g' = g' * g) :
    (g : GL V₄ K) * g' = g' * g ∨ (g : GL V₄ K) * g' = -(g' * g) := by
  have h1 : ((g' * g : StatedSp 2 K) : StatedProj (StatedSp 2 K)) =
      ((g * g' : StatedSp 2 K) : StatedProj (StatedSp 2 K)) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, h]
  rcases mk_eq_mk_iff_sp.mp h1 with h2 | h2
  · left
    simpa using h2
  · right
    simpa using h2

theorem sq_eq_or_of_mk {g : StatedSp 2 K} (h : (g : StatedProj (StatedSp 2 K)) ^ 2 = 1) :
    (g : GL V₄ K) * g = 1 ∨ (g : GL V₄ K) * g = -1 := by
  have h1 : ((1 : StatedSp 2 K) : StatedProj (StatedSp 2 K)) =
      ((g * g : StatedSp 2 K) : StatedProj (StatedSp 2 K)) := by
    rw [QuotientGroup.mk_mul, ← sq, h, QuotientGroup.mk_one]
  rcases mk_eq_mk_iff_sp.mp h1 with h2 | h2
  · left
    simpa using h2
  · right
    simpa using h2

theorem neg_one_mem_statedSp : (-1 : GL V₄ K) ∈ StatedSp 2 K := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
  simp

@[expose] noncomputable def negSp (g : StatedSp 2 K) : StatedSp 2 K :=
  ⟨-1 * g, mul_mem neg_one_mem_statedSp g.2⟩

theorem coe_negSp (g : StatedSp 2 K) : ((negSp g : StatedSp 2 K) : GL V₄ K) = -g := by
  simp [negSp]

theorem mk_negSp (g : StatedSp 2 K) :
    ((negSp g : StatedSp 2 K) : StatedProj (StatedSp 2 K)) = (g : StatedProj (StatedSp 2 K)) :=
  (mk_eq_mk_iff_sp.mpr (Or.inr (by rw [coe_negSp]))).symm

theorem exists_lift_pow_three {x : StatedProj (StatedSp 2 K)} (hx : x ^ 3 = 1) :
    ∃ g : StatedSp 2 K, (g : StatedProj (StatedSp 2 K)) = x ∧ (g : GL V₄ K) ^ 3 = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : ((1 : StatedSp 2 K) : StatedProj (StatedSp 2 K)) =
      ((g ^ 3 : StatedSp 2 K) : StatedProj (StatedSp 2 K)) := by
    rw [QuotientGroup.mk_pow, hx, QuotientGroup.mk_one]
  rcases mk_eq_mk_iff_sp.mp h1 with h2 | h2
  · exact ⟨g, rfl, by simpa using h2⟩
  · refine ⟨negSp g, mk_negSp g, ?_⟩
    rw [coe_negSp]
    have h3 : (g : GL V₄ K) ^ 3 = -1 := by simpa using h2
    rw [Odd.neg_pow (by decide), h3, neg_neg]

theorem center_statedProj_statedSp_eq_bot [Finite K] (hK4 : 4 ≤ Nat.card K) :
    Subgroup.center (StatedProj (StatedSp 2 K)) = ⊥ := by
  have : IsSimpleGroup (StatedProj (StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
      (Or.inl (Or.inr hK4))
  have : Group.IsPerfect (StatedProj (StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp_quotient 2 K
      (Or.inl (CFSG.LinearGroups.exists_finset_card_eq_four hK4)) _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (StatedProj (StatedSp 2 K)))
    with h1 | h1
  · exact h1
  · exfalso
    have h2 := (commutator_eq_bot_iff_center_eq_top (StatedProj (StatedSp 2 K))).2 h1
    rw [Group.IsPerfect.commutator_eq_top] at h2
    exact top_ne_bot h2

end Model

theorem commute_commutator_of_signs {G : Type*} [Group G] [HasDistribNeg G] {q b u : G}
    (hb : b * u = u * b) (hq : q * u = u * q ∨ q * u = -(u * q)) :
    q * b * q⁻¹ * b⁻¹ * u = u * (q * b * q⁻¹ * b⁻¹) := by
  have hbi : b⁻¹ * u = u * b⁻¹ := (show Commute b u from hb).inv_left.eq
  rcases hq with hq | hq
  · have hqi : q⁻¹ * u = u * q⁻¹ := (show Commute q u from hq).inv_left.eq
    calc q * b * q⁻¹ * b⁻¹ * u = q * b * q⁻¹ * (b⁻¹ * u) := by group
      _ = q * b * (q⁻¹ * u) * b⁻¹ := by rw [hbi]; group
      _ = q * (b * u) * q⁻¹ * b⁻¹ := by rw [hqi]; group
      _ = (q * u) * b * q⁻¹ * b⁻¹ := by rw [hb]; group
      _ = u * (q * b * q⁻¹ * b⁻¹) := by rw [hq]; group
  · have hqi : q⁻¹ * u = -(u * q⁻¹) := by
      have h1 : q⁻¹ * (q * u) = q⁻¹ * (-(u * q)) := by rw [hq]
      rw [inv_mul_cancel_left, mul_neg] at h1
      have h3 : q⁻¹ * u * q = -u := by rw [mul_assoc, ← neg_neg (q⁻¹ * (u * q)), ← h1]
      calc q⁻¹ * u = (q⁻¹ * u * q) * q⁻¹ := by group
        _ = -(u * q⁻¹) := by rw [h3, neg_mul]
    calc q * b * q⁻¹ * b⁻¹ * u = q * b * q⁻¹ * (b⁻¹ * u) := by group
      _ = q * b * (q⁻¹ * u) * b⁻¹ := by rw [hbi]; group
      _ = -(q * (b * u) * q⁻¹ * b⁻¹) := by rw [hqi]; simp only [mul_neg, neg_mul]; group
      _ = -((q * u) * b * q⁻¹ * b⁻¹) := by rw [hb]; group
      _ = u * (q * b * q⁻¹ * b⁻¹) := by rw [hq]; simp only [neg_mul, neg_neg]; group

theorem commute_of_pow_three_of_signs {G : Type*} [Group G] [HasDistribNeg G] {b u : G}
    (hu : u ≠ -u) (hb3 : b ^ 3 = 1) (hb : b * u = u * b ∨ b * u = -(u * b)) : b * u = u * b := by
  rcases hb with hb | hb
  · exact hb
  · exfalso
    apply hu
    have h1 : b * u * b⁻¹ = -u := by rw [hb, neg_mul, mul_inv_cancel_right]
    have hb3' : b * b * b = 1 := by rw [← pow_three', hb3]
    have h3 : b * (b * (b * u * b⁻¹) * b⁻¹) * b⁻¹ = -u := by
      rw [h1, mul_neg, neg_mul, h1, neg_neg, h1]
    have h4 : b * (b * (b * u * b⁻¹) * b⁻¹) * b⁻¹ = (b * b * b) * u * (b * b * b)⁻¹ := by group
    rw [h4, hb3', one_mul, inv_one, mul_one] at h3
    exact h3

section Quat

variable {K : Type} [Field K]

theorem neg_one_ne_one_gl (h2 : (2 : K) ≠ 0) : (-1 : GL V₄ K) ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : GL V₄ K => (g : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inl 0)) h
  simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply_eq] at h1
  apply h2
  linear_combination -h1

theorem ne_neg_gl (h2 : (2 : K) ≠ 0) (g : GL V₄ K) : g ≠ -g := by
  intro h
  apply neg_one_ne_one_gl h2
  have h1 : g⁻¹ * g = g⁻¹ * -g := by rw [← h]
  rw [inv_mul_cancel, mul_neg, inv_mul_cancel] at h1
  exact h1.symm

theorem exists_quat_lift (h2 : (2 : K) ≠ 0) {u₀ v₀ d₀ : StatedProj (StatedSp 2 K)}
    (hu2 : u₀ ^ 2 = 1) (hv2 : v₀ ^ 2 = 1) (huv : u₀ * v₀ = v₀ * u₀) (hu1 : u₀ ≠ 1)
    (hv1 : v₀ ≠ 1) (huv1 : u₀ ≠ v₀) (hdu : d₀ * u₀ * d₀⁻¹ = v₀)
    (hdv : d₀ * v₀ * d₀⁻¹ = u₀ * v₀) :
    ∃ U V : StatedSp 2 K, (U : StatedProj (StatedSp 2 K)) = u₀ ∧
      (V : StatedProj (StatedSp 2 K)) = v₀ ∧ (U : GL V₄ K) * U = -1 ∧
      (V : GL V₄ K) * V = -1 ∧ (U : GL V₄ K) * V = -((V : GL V₄ K) * U) := by
  obtain ⟨U, rfl⟩ := QuotientGroup.mk_surjective u₀
  obtain ⟨V, rfl⟩ := QuotientGroup.mk_surjective v₀
  obtain ⟨E, rfl⟩ := QuotientGroup.mk_surjective d₀
  refine ⟨U, V, rfl, rfl, ?_⟩
  have hUs := sq_eq_or_of_mk hu2
  have hVs := sq_eq_or_of_mk hv2
  have hsq : ∀ {A B : StatedSp 2 K}, ((E * A * E⁻¹ : StatedSp 2 K) : StatedProj (StatedSp 2 K)) =
      (B : StatedProj (StatedSp 2 K)) →
      ((A : GL V₄ K) * A = 1 ∨ (A : GL V₄ K) * A = -1) →
      (B : GL V₄ K) * B = (A : GL V₄ K) * A := by
    intro A B hAB hA
    have hcent : (E : GL V₄ K) * ((A : GL V₄ K) * A) * (E : GL V₄ K)⁻¹ = (A : GL V₄ K) * A := by
      rcases hA with hA | hA <;> rw [hA]
      · group
      · rw [mul_neg, mul_one, neg_mul, mul_inv_cancel]
    have hEA : ((E * A * E⁻¹ : StatedSp 2 K) : GL V₄ K) * (E * A * E⁻¹ : StatedSp 2 K) =
        (A : GL V₄ K) * A := by
      rw [← hcent]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rcases mk_eq_mk_iff_sp.mp hAB with h | h
    · rw [h, hEA]
    · rw [h, neg_mul_neg, hEA]
  have hUV : (U : GL V₄ K) * U = (V : GL V₄ K) * V :=
    (hsq (by rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]; exact hdu)
      hUs).symm
  have hVW : ((U * V : StatedSp 2 K) : GL V₄ K) * (U * V : StatedSp 2 K) =
      (V : GL V₄ K) * V :=
    hsq (by rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_mul]; exact hdv) hVs
  rw [Subgroup.coe_mul] at hVW
  have hca := comm_or_anticomm_of_mk huv
  have hUU1 : ((U : GL V₄ K) * U) * ((U : GL V₄ K) * U) = 1 := by
    rcases hUs with h | h <;> rw [h]
    · rw [mul_one]
    · rw [neg_mul_neg, mul_one]
  rcases hUs with hU1 | hU1
  ·
    exfalso
    have hV1 : (V : GL V₄ K) * V = 1 := by rw [← hUV, hU1]
    rcases hca with hc | hc
    · have hUm1 : (U : GL V₄ K) ≠ 1 := fun h => hu1 (mk_eq_one_iff_sp.mpr (Or.inl h))
      have hUm2 : (U : GL V₄ K) ≠ -1 := fun h => hu1 (mk_eq_one_iff_sp.mpr (Or.inr h))
      rcases CFSG.RankThree.SubgroupLists.eq_of_commute_involution h2 U.2 V.2 hU1 hV1 hc hUm1
        hUm2 with h | h | h | h
      · exact hv1 (mk_eq_one_iff_sp.mpr (Or.inl h))
      · exact hv1 (mk_eq_one_iff_sp.mpr (Or.inr h))
      · exact huv1 (mk_eq_mk_iff_sp.mpr (Or.inl h))
      · exact huv1 (mk_eq_mk_iff_sp.mpr (Or.inr h))
    ·
      have h1 : (U : GL V₄ K) * V * ((U : GL V₄ K) * V) = -1 := by
        calc (U : GL V₄ K) * V * ((U : GL V₄ K) * V)
            = (U : GL V₄ K) * ((V : GL V₄ K) * U) * V := by group
          _ = -((U : GL V₄ K) * ((U : GL V₄ K) * V) * V) := by
              rw [show (V : GL V₄ K) * U = -((U : GL V₄ K) * V) by rw [hc, neg_neg], mul_neg,
                neg_mul]
          _ = -1 := by
              rw [show (U : GL V₄ K) * ((U : GL V₄ K) * V) * V = ((U : GL V₄ K) * U) *
                ((V : GL V₄ K) * V) by group, hU1, hV1, mul_one]
      rw [hVW, hV1] at h1
      exact neg_one_ne_one_gl h2 h1.symm
  ·
    have hV1 : (V : GL V₄ K) * V = -1 := by rw [← hUV, hU1]
    refine ⟨hU1, hV1, ?_⟩
    rcases hca with hc | hc
    · exfalso
      have h1 : (U : GL V₄ K) * V * ((U : GL V₄ K) * V) = 1 := by
        calc (U : GL V₄ K) * V * ((U : GL V₄ K) * V)
            = (U : GL V₄ K) * ((V : GL V₄ K) * U) * V := by group
          _ = ((U : GL V₄ K) * U) * ((V : GL V₄ K) * V) := by rw [← hc]; group
          _ = 1 := by rw [hU1, hV1, neg_mul_neg, mul_one]
      rw [hVW, hV1] at h1
      exact neg_one_ne_one_gl h2 h1
    · exact hc

theorem conj_commutator_eq_or_eq_inv (h2 : (2 : K) ≠ 0) {a c : K} (hac : a ^ 2 + c ^ 2 = -1)
    {U V : StatedSp 2 K} (hU2 : (U : GL V₄ K) * U = -1) (hV2 : (V : GL V₄ K) * V = -1)
    (hUV : (U : GL V₄ K) * V = -((V : GL V₄ K) * U)) {b₀ q₀ : StatedProj (StatedSp 2 K)}
    (hb3 : b₀ ^ 3 = 1) (hbu : b₀ * U = U * b₀) (hbv : b₀ * V = V * b₀)
    (hqu : q₀ * U = U * q₀) (hqv : q₀ * V = V * q₀) :
    (q₀ * b₀ * q₀⁻¹ * b₀⁻¹) * b₀ * (q₀ * b₀ * q₀⁻¹ * b₀⁻¹)⁻¹ = b₀ ∨
      (q₀ * b₀ * q₀⁻¹ * b₀⁻¹) * b₀ * (q₀ * b₀ * q₀⁻¹ * b₀⁻¹)⁻¹ = b₀⁻¹ := by
  obtain ⟨B, rfl, hB3⟩ := exists_lift_pow_three hb3
  obtain ⟨Q, rfl⟩ := QuotientGroup.mk_surjective q₀
  have hBU := commute_of_pow_three_of_signs (ne_neg_gl h2 _) hB3 (comm_or_anticomm_of_mk hbu)
  have hBV := commute_of_pow_three_of_signs (ne_neg_gl h2 _) hB3 (comm_or_anticomm_of_mk hbv)
  have hCU := commute_commutator_of_signs hBU (comm_or_anticomm_of_mk hqu)
  have hCV := commute_commutator_of_signs hBV (comm_or_anticomm_of_mk hqv)
  set C : StatedSp 2 K := Q * B * Q⁻¹ * B⁻¹ with hC
  have hCU' : (C : GL V₄ K) * U = U * C := by
    simpa only [hC, Subgroup.coe_mul, Subgroup.coe_inv] using hCU
  have hCV' : (C : GL V₄ K) * V = V * C := by
    simpa only [hC, Subgroup.coe_mul, Subgroup.coe_inv] using hCV
  obtain ⟨a', c', hac'⟩ : ∃ a' c' : K, a' ^ 2 + c' ^ 2 = -1 := ⟨a, c, hac⟩
  rcases conj_eq_or_eq_inv_of_quat h2 hac' U.2 V.2 C.2 B.2 hU2 hV2 hUV hCU' hCV' hBU hBV hB3
    with h | h
  · left
    have h1 : C * B * C⁻¹ = B := Subtype.ext (by simpa using h)
    have h3 := congrArg (fun z : StatedSp 2 K => (z : StatedProj (StatedSp 2 K))) h1
    simpa [hC] using h3
  · right
    have h1 : C * B * C⁻¹ = B⁻¹ := Subtype.ext (by simpa using h)
    have h3 := congrArg (fun z : StatedSp 2 K => (z : StatedProj (StatedSp 2 K))) h1
    simpa [hC] using h3

end Quat

theorem eq_one_of_pow_three_of_mem {M : Type*} [Group M] {Q : Subgroup M} (hQ : IsPGroup 2 Q)
    {x : M} (hx : x ∈ Q) (hx3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have hcop : Nat.Coprime (orderOf x) 3 :=
    Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left k (by norm_num))
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop h3)

theorem mem_four_of_card {M : Type*} [Group M] {T : Subgroup M} (hT4 : Nat.card T = 4)
    {u v : M} (hu : u ∈ T) (hv : v ∈ T) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v)
    (huv1 : u * v ≠ 1) (huvu : u * v ≠ u) (huvv : u * v ≠ v) {w : M} (hw : w ∈ T) :
    w = 1 ∨ w = u ∨ w = v ∨ w = u * v := by
  by_contra hne
  push Not at hne
  obtain ⟨hw1, hwu, hwv, hwuv⟩ := hne
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hT4]; norm_num)
  let f : Fin 5 → T := ![⟨1, T.one_mem⟩, ⟨u, hu⟩, ⟨v, hv⟩, ⟨u * v, T.mul_mem hu hv⟩, ⟨w, hw⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have hij' := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp only [f] at hij' <;>
      first
        | rfl
        | exact absurd hij' (Ne.symm hu1) | exact absurd hij' hu1
        | exact absurd hij' (Ne.symm hv1) | exact absurd hij' hv1
        | exact absurd hij' (Ne.symm huv) | exact absurd hij' huv
        | exact absurd hij' (Ne.symm huv1) | exact absurd hij' huv1
        | exact absurd hij' (Ne.symm huvu) | exact absurd hij' huvu
        | exact absurd hij' (Ne.symm huvv) | exact absurd hij' huvv
        | exact absurd hij' (Ne.symm hw1) | exact absurd hij' hw1
        | exact absurd hij' (Ne.symm hwu) | exact absurd hij' hwu
        | exact absurd hij' (Ne.symm hwv) | exact absurd hij' hwv
        | exact absurd hij' (Ne.symm hwuv) | exact absurd hij' hwuv
  have h5 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, hT4] at h5
  omega

theorem excMinusFor_statedSp {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    (hK4 : 4 ≤ Nat.card K) {a c : K} (hac : a ^ 2 + c ^ 2 = -1) :
    ExcMinusFor (StatedProj (StatedSp 2 K)) := by
  classical
  have hZ := center_statedProj_statedSp_eq_bot hK4
  have hinj := Item211Lie2Proof.conj_injective' hZ
  intro D T hDi hTi hDe hD9 hTe hT4 hDT hTD u hu hu1
  set Inn := (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))).range
    with hInn
  have hTinv : ∀ t ∈ T, t ^ 2 = 1 := fun t ht => hTe.2 t ht
  have hTcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := fun s hs t ht =>
    congrArg Subtype.val (hTe.1.is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩)
  have hDcube : ∀ d ∈ D, d ^ 3 = 1 := fun d hd => hDe.2 d hd
  have hconjT : ∀ d ∈ D, ∀ t ∈ T, d * t * d⁻¹ ∈ T := fun d hd t ht =>
    (Subgroup.mem_normalizer_iff.mp (hDT hd) t).mp ht
  have hT_ne : T ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hT4
    omega
  obtain ⟨d, hdD, hdu⟩ : ∃ d ∈ D, d * u * d⁻¹ ≠ u := by
    by_contra hcon
    push Not at hcon
    apply hT_ne
    rw [← hTD, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have heu := hcon e he
    by_cases ht1 : t = 1
    · rw [ht1, one_mul, mul_one]
    by_cases htu : t = u
    · rw [htu]
      calc e * u = e * u * e⁻¹ * e := by group
        _ = u * e := by rw [heu]
    have hut1 : u * t ≠ 1 := by
      intro h
      apply htu
      have := hTinv u hu
      calc t = u * (u * t) := by rw [← mul_assoc, ← sq, this, one_mul]
        _ = u := by rw [h, mul_one]
    have hutu : u * t ≠ u := fun h => ht1 (by simpa using h)
    have hutt : u * t ≠ t := fun h => hu1 (by simpa using h)
    have hmem := mem_four_of_card hT4 hu ht hu1 ht1 (Ne.symm htu) hut1 hutu hutt
      (hconjT e he t ht)
    have het1 : e * t * e⁻¹ ≠ 1 := fun h => ht1 (by
      have : t = e⁻¹ * (e * t * e⁻¹) * e := by group
      rw [this, h]; group)
    have hetu : e * t * e⁻¹ ≠ u := fun h => htu (by
      have h3 : e * t * e⁻¹ = e * u * e⁻¹ := by rw [h, heu]
      simpa using h3)
    rcases hmem with h | h | h | h
    · exact absurd h het1
    · exact absurd h hetu
    · calc e * t = e * t * e⁻¹ * e := by group
        _ = t * e := by rw [h]
    · exfalso
      have h3 : e * (u * t) * e⁻¹ = t := by
        calc e * (u * t) * e⁻¹ = (e * u * e⁻¹) * (e * t * e⁻¹) := by group
          _ = t := by rw [heu, h, ← mul_assoc, ← sq, hTinv u hu, one_mul]
      have he3 : e * e * e = 1 := by rw [← pow_three', hDcube e he]
      have h4 : e * (e * (e * t * e⁻¹) * e⁻¹) * e⁻¹ = u * t := by rw [h, h3, h]
      have h5 : e * (e * (e * t * e⁻¹) * e⁻¹) * e⁻¹ = (e * e * e) * t * (e * e * e)⁻¹ := by
        group
      rw [h5, he3, one_mul, inv_one, mul_one] at h4
      exact hutt h4.symm
  set v := d * u * d⁻¹ with hv
  have hvT : v ∈ T := hconjT d hdD u hu
  have hv1 : v ≠ 1 := fun h => hu1 (by
    have : u = d⁻¹ * (d * u * d⁻¹) * d := by group
    rw [this, ← hv, h]; group)
  have huv : u ≠ v := fun h => hdu h.symm
  have huv1 : u * v ≠ 1 := by
    intro h
    apply huv
    have := hTinv u hu
    calc u = u * (u * v) := by rw [h, mul_one]
      _ = v := by rw [← mul_assoc, ← sq, this, one_mul]
  have huvu : u * v ≠ u := fun h => hv1 (by simpa using h)
  have huvv : u * v ≠ v := fun h => hu1 (by simpa using h)
  have hdv : d * v * d⁻¹ = u * v := by
    rcases mem_four_of_card hT4 hu hvT hu1 hv1 huv huv1 huvu huvv (hconjT d hdD v hvT) with
      h | h | h | h
    · exfalso
      apply hv1
      have : v = d⁻¹ * (d * v * d⁻¹) * d := by group
      rw [this, h]; group
    · exfalso
      have hd3 : d * d * d = 1 := by rw [← pow_three', hDcube d hdD]
      have h4 : d * (d * (d * u * d⁻¹) * d⁻¹) * d⁻¹ = v := by rw [← hv, h]
      have h5 : d * (d * (d * u * d⁻¹) * d⁻¹) * d⁻¹ = (d * d * d) * u * (d * d * d)⁻¹ := by
        group
      rw [h5, hd3, one_mul, inv_one, mul_one] at h4
      exact huv h4
    · exfalso
      apply huv
      have h3 : d * v * d⁻¹ = d * u * d⁻¹ := by rw [h]
      exact (by simpa using h3 : v = u).symm
    · exact h
  obtain ⟨u₀, rfl⟩ := hTi hu
  obtain ⟨v₀, hv₀⟩ := hTi hvT
  obtain ⟨d₀, hd₀⟩ := hDi hdD
  have hu₀2 : u₀ ^ 2 = 1 := hinj (by rw [map_pow, hTinv _ hu, map_one])
  have hv₀2 : v₀ ^ 2 = 1 := hinj (by rw [map_pow, hv₀, hTinv _ hvT, map_one])
  have hu₀v₀ : u₀ * v₀ = v₀ * u₀ := hinj (by
    rw [map_mul, map_mul, hv₀]
    exact hTcomm _ hu _ hvT)
  have hu₀1 : u₀ ≠ 1 := fun h => hu1 (by rw [h, map_one])
  have hv₀1 : v₀ ≠ 1 := fun h => hv1 (by rw [← hv₀, h, map_one])
  have hu₀v₀1 : u₀ ≠ v₀ := fun h => huv (by rw [h, hv₀])
  have hdu₀ : d₀ * u₀ * d₀⁻¹ = v₀ := hinj (by
    rw [map_mul, map_mul, map_inv, hd₀, hv₀])
  have hdv₀ : d₀ * v₀ * d₀⁻¹ = u₀ * v₀ := hinj (by
    rw [map_mul, map_mul, map_inv, hd₀, hv₀, hdv, map_mul, hv₀])
  obtain ⟨U, V, hU, hV, hU2, hV2, hUV⟩ :=
    exists_quat_lift h2 hu₀2 hv₀2 hu₀v₀ hu₀1 hv₀1 hu₀v₀1 hdu₀ hdv₀
  intro b hb
  obtain ⟨hbD, hbT⟩ := Subgroup.mem_inf.mp hb
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  set Δ := threeGen (Inn ⊓ Subgroup.centralizer ({MulAut.conj u₀} :
    Set (MulAut (StatedProj (StatedSp 2 K))))) with hΔ
  set H := Δ ⊓ Subgroup.centralizer (T : Set (MulAut (StatedProj (StatedSp 2 K)))) with hH
  set Q := inSubgroup (CFSG.pCore 2) H with hQ
  have hQ2 : IsPGroup 2 Q := (CFSG.pCore_isPGroup).map H.subtype
  have hQH : Q ≤ H := Subgroup.map_subtype_le _
  have hΔInn : Δ ≤ Inn := (Subgroup.closure_le _).mpr fun x hx => (Subgroup.mem_inf.mp hx.1).1
  have hb3 : b ^ 3 = 1 := hDcube b hbD
  have hbH : b ∈ H := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨hDi hbD, ?_⟩,
      1, by rw [pow_one, hb3]⟩, hbT⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hbT _ hu).symm
  have hbN := CFSG.RankThree.GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 H hbH
  have hcQ : q * b * q⁻¹ * b⁻¹ ∈ Q := by
    have h1 : b * q⁻¹ * b⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hbN _).mp (Q.inv_mem hq)
    have e : q * b * q⁻¹ * b⁻¹ = q * (b * q⁻¹ * b⁻¹) := by group
    rw [e]
    exact Q.mul_mem hq h1
  have hqH := hQH hq
  obtain ⟨q₀, rfl⟩ := hΔInn (Subgroup.mem_inf.mp hqH).1
  obtain ⟨b₀, rfl⟩ := hDi hbD
  have hb₀3 : b₀ ^ 3 = 1 := hinj (by rw [map_pow, hb3, map_one])
  have hcommT : ∀ {y : StatedProj (StatedSp 2 K)},
      MulAut.conj y ∈ Subgroup.centralizer (T : Set (MulAut (StatedProj (StatedSp 2 K)))) →
      y * (U : StatedProj (StatedSp 2 K)) = U * y ∧
        y * (V : StatedProj (StatedSp 2 K)) = V * y := by
    intro y hy
    refine ⟨hinj ?_, hinj ?_⟩
    · rw [map_mul, map_mul, hU]
      exact (Subgroup.mem_centralizer_iff.mp hy _ hu).symm
    · rw [map_mul, map_mul, hV, hv₀]
      exact (Subgroup.mem_centralizer_iff.mp hy _ hvT).symm
  obtain ⟨hbU, hbV⟩ := hcommT hbT
  obtain ⟨hqU, hqV⟩ := hcommT (Subgroup.mem_inf.mp hqH).2
  have hkey := conj_commutator_eq_or_eq_inv h2 hac hU2 hV2 hUV hb₀3 hbU hbV hqU hqV
  set c₀ := q₀ * b₀ * q₀⁻¹ * b₀⁻¹ with hc₀
  have hc : MulAut.conj q₀ * MulAut.conj b₀ * (MulAut.conj q₀)⁻¹ * (MulAut.conj b₀)⁻¹ =
      MulAut.conj c₀ := by
    rw [hc₀, map_mul, map_mul, map_mul, map_inv, map_inv]
  rw [hc] at hcQ
  have hc1 : c₀ = 1 := by
    rcases hkey with h | h
    ·
      have hcb : c₀ * b₀ = b₀ * c₀ := by
        calc c₀ * b₀ = c₀ * b₀ * c₀⁻¹ * c₀ := by group
          _ = b₀ * c₀ := by rw [h]
      have hqb : q₀ * b₀ * q₀⁻¹ = c₀ * b₀ := by rw [hc₀]; group
      have h3 : c₀ ^ 3 = 1 := by
        have h4 : q₀ * b₀ ^ 3 * q₀⁻¹ = (c₀ * b₀) ^ 3 := by rw [← hqb, conj_pow]
        rw [hb₀3, mul_one, mul_inv_cancel, (Commute.mul_pow hcb 3), hb₀3, mul_one] at h4
        exact h4.symm
      have := eq_one_of_pow_three_of_mem hQ2 hcQ (by rw [← map_pow, h3, map_one])
      exact hinj (by rw [this, map_one])
    ·
      have hbc : b₀ * c₀ * b₀⁻¹ = c₀ * b₀ := by
        have h4 : c₀ * b₀ = b₀⁻¹ * c₀ := by
          calc c₀ * b₀ = c₀ * b₀ * c₀⁻¹ * c₀ := by group
            _ = b₀⁻¹ * c₀ := by rw [h]
        have h5 : b₀⁻¹ = b₀ * b₀ := by
          rw [inv_eq_iff_mul_eq_one, ← pow_three, hb₀3]
        calc b₀ * c₀ * b₀⁻¹ = b₀ * c₀ * (b₀ * b₀) := by rw [h5]
          _ = b₀ * (c₀ * b₀) * b₀ := by group
          _ = b₀ * (b₀⁻¹ * c₀) * b₀ := by rw [h4]
          _ = c₀ * b₀ := by group
      have hbQ : MulAut.conj b₀ ∈ Q := by
        have h1 : MulAut.conj b₀ * MulAut.conj c₀ * (MulAut.conj b₀)⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp hbN _).mp hcQ
        have h3 : MulAut.conj c₀ * MulAut.conj b₀ ∈ Q := by
          rw [← map_mul, ← hbc, map_mul, map_mul, map_inv]
          exact h1
        have h5 := Q.mul_mem (Q.inv_mem hcQ) h3
        rwa [inv_mul_cancel_left] at h5
      have hb1 := eq_one_of_pow_three_of_mem hQ2 hbQ (by rw [← map_pow, hb₀3, map_one])
      have hb₀1 : b₀ = 1 := hinj (by rw [hb1, map_one])
      rw [hc₀, hb₀1]
      group
  have h1 : q₀ * b₀ = b₀ * q₀ := by
    have h3 : q₀ * b₀ * q₀⁻¹ * b₀⁻¹ = 1 := hc1
    calc q₀ * b₀ = (q₀ * b₀ * q₀⁻¹ * b₀⁻¹) * (b₀ * q₀) := by group
      _ = b₀ * q₀ := by rw [h3, one_mul]
  rw [← map_mul, ← map_mul, h1]

end Item211Lie3Proof

open Item211Lie2Proof Item211Lie3Proof

theorem ks211ExcMinusSp_holds : KS211ExcMinusSp := by
  intro p _ hp3
  set K := GaloisField p 1
  have hK : Nat.card K = p := by rw [GaloisField.card p 1 one_ne_zero, pow_one]
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (Fact.out : p.Prime).ne_zero)
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  obtain ⟨a, c, hac⟩ := ZMod.sq_add_sq p (-1)
  have hac' : (algebraMap (ZMod p) K a) ^ 2 + (algebraMap (ZMod p) K c) ^ 2 = -1 := by
    rw [← map_pow, ← map_pow, ← map_add, hac]
    exact (map_neg (algebraMap (ZMod p) K) 1).trans (by rw [map_one])
  exact excMinusFor_of_mulEquiv (Sec4.projSpEquivStatedProj 2 K)
    (excMinusFor_statedSp h2 (by rw [hK]; omega) hac')

end CFSG.RankThree.PartTwo.Sec21
