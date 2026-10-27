module

public import CFSG.RankThree.GF2n.Smith81.LinStmt
import CFSG.RankThree.GF2n.Smith81.TiOuter
import CFSG.RankThree.GF2n.Smith81.InspLinLocal
import CFSG.RankThree.GF2n.Smith81.LinOddAssembly
import CFSG.Timmesfeld.Orders.Classical
import CFSG.ClassicalInvolution.RouteD.TWRExoticArith
import CFSG.RankThree.GF2n.Stroth80.Sec1110Core
public import CFSG.CGT.Timmesfeld75.Forms
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.GroupTheory.HuppertProduct.Quotient
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.GF2n.Smith81.Sec1Local
public import CFSG.RankThree.GF2n.Stroth80.Consumers
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec36
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.RankThree.GF2n.Tim81.Components
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.RankOne
import CFSG.Combinatorics.AperiodicCentralInvolution
import CFSG.Combinatorics.AperiodicFiveOfSix
import CFSG.Combinatorics.AperiodicOppositeComponents
import CFSG.Combinatorics.AperiodicSixteenGraphDistances
import CFSG.Combinatorics.OuterLayerPredecessors
import CFSG.GH74.Uniqueness.Bender.OddCentralizer
import CFSG.LargeExtraspecial.S8CorBStatement
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
import CFSG.Permutation.BurnsideSchur
import CFSG.RankThree.GF2n.Smith81.InspLinCore
import CFSG.RankThree.GF2n.Stroth80.Sec1110ModuleDual
import CFSG.RankThree.GF2n.Stroth80.Sec11Stmt
import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
import CFSG.RankThree.GF2n.Stroth80.Sec4Stmt
import CFSG.RankThree.GF2n.Stroth80.Sec5Comm
import CFSG.RankThree.GF2n.Stroth80.Sec6Stmt
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80
open CFSG.SeitzReduction.F4Pilot (ordSL)

variable {G : Type} [Group G]

theorem factorization_card_of_lieModel_psl {Y : Type} [Group Y] {n f : ℕ} (hn : 1 ≤ n)
    (hL : CFSG.Blueprint.LieModel Y .PSL (n + 2) 2 f) :
    (Nat.card Y).factorization 2 = f * ((n + 1) * (n + 2) / 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 0 < f := hL.admissible.2.1
  have hY : Nat.card Y = ordA (n + 1) (2 ^ f) := by
    have h := (CFSG.Timmesfeld.card_statedClassicalModel_two
      (hL.statedClassicalModel_of_ne_zero (by omega))).1 rfl
    rwa [show n + 2 - 1 = n + 1 by omega] at h
  rw [hY, Nat.factorization_def _ Nat.prime_two,
    CFSG.ClassicalInvolution.RouteD.TWR.padicValNat_ordA (p := 2) (q := 2 ^ f) (f := f)
      (n := n + 1) rfl hf (by omega)]

private theorem factorization_arith {n f : ℕ} (hn : 1 ≤ n) :
    f * (2 * n + 1) + f * (n * (n - 1) / 2) = f * ((n + 1) * (n + 2) / 2) := by
  have hS : (n + 1) * (n + 2) = n * (n - 1) + 2 * (2 * n + 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hdiv : (n + 1) * (n + 2) / 2 = n * (n - 1) / 2 + (2 * n + 1) := by
    rw [hS, Nat.add_mul_div_left (n * (n - 1)) (2 * n + 1) (by norm_num : 0 < 2)]
  rw [hdiv, mul_add]
  ring

theorem factorization_card_Lgen [Finite G]
    {M Q Z B : Subgroup G} {n : ℕ} (hc : Ctx M Q Z B) (hn : 1 ≤ n) {V₁ V₂ : Subgroup G}
    (hW : LinSetup M Q Z B n V₁ V₂) {f : ℕ} (hf : Nat.card Z = 2 ^ f) :
    (Nat.card (Lgen M (LB M Q B))).factorization 2 = f * ((n + 1) * (n + 2) / 2) := by
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr fun h0 => by
    have h4 := hc.hyp.q4
    rw [hf, h0] at h4
    norm_num at h4
  have hcard := Insp.card_Lgen_eq hW hn
  have h0 : Nat.card Q * ordSL n (2 ^ f) ≠ 0 := by
    rw [← hf, ← hcard]
    exact Nat.card_pos.ne'
  have hw := hW.width hc.hyp
  unfold Width at hw
  rw [hcard, hf, Nat.factorization_mul (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0),
    Finsupp.add_apply, hw, hf, ← pow_mul, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same, Insp.factorization_ordSL_two hf1 n]
  exact factorization_arith hn

theorem conjSubgroup_eq_or_eq_of_inZClass_iff [Finite G] {M Q Z : Subgroup G}
    (H : StrothHyp M Q Z) {V₁ V₂ : Subgroup G} (hV₁Q : V₁ ≤ Q) (hcard : Nat.card V₁ = Nat.card V₂)
    (hcls : ∀ v : G, v ∈ Q → v ≠ 1 → (InZClass Z v ↔ v ∈ V₁ ∨ v ∈ V₂)) {m : G}
    (hm : m ∈ M) : conjSubgroup m V₁ = V₁ ∨ conjSubgroup m V₁ = V₂ := by
  have hsubset : (conjSubgroup m V₁ : Set G) ⊆ (V₁ : Set G) ∪ (V₂ : Set G) := by
    intro v hv
    by_cases hv1 : v = 1
    · exact Or.inl (by rw [hv1]; exact V₁.one_mem)
    have hw : m⁻¹ * v * m ∈ V₁ := mem_conjSubgroup.mp hv
    have hw1 : m⁻¹ * v * m ≠ 1 := by
      intro h
      apply hv1
      calc v = m * (m⁻¹ * v * m) * m⁻¹ := by group
        _ = 1 := by rw [h]; group
    have hcl : InZClass Z (m⁻¹ * v * m) := (hcls _ (hV₁Q hw) hw1).mpr (Or.inl hw)
    have hcl' : InZClass Z v := by
      have := hcl.conj m
      rwa [show m * (m⁻¹ * v * m) * m⁻¹ = v by group] at this
    have hvQ : v ∈ Q := by
      have h := (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 hm) (m⁻¹ * v * m)).mp (hV₁Q hw)
      rwa [show m * (m⁻¹ * v * m) * m⁻¹ = v by group] at h
    exact (hcls v hvQ hv1).mp hcl'
  rcases SubgroupClass.subset_union.mp hsubset with h | h
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (by rw [card_conjSubgroup]))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (by rw [card_conjSubgroup, hcard]))

theorem LinSetup.modules_ne {M Q Z B : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}
    (hW : LinSetup M Q Z B n V₁ V₂) (hc : Ctx M Q Z B) (hn : 1 ≤ n) : V₁ ≠ V₂ := by
  intro h
  obtain ⟨-, -, -, -, hint, -, -, -, hV₁card, -⟩ := hW.basic
  have hZV : Z = V₁ := by rw [← hint, ← h, inf_idem]
  rw [← hZV] at hV₁card
  have hq : 2 ≤ Nat.card Z := by
    have := hc.hyp.q4
    omega
  have hlt : Nat.card Z ^ 1 < Nat.card Z ^ (n + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  rw [pow_one] at hlt
  omega

theorem LinSetup.relIndex_normalizer_eq_two [Finite G] {M Q Z B : Subgroup G} {n : ℕ}
    {V₁ V₂ : Subgroup G} (hW : LinSetup M Q Z B n V₁ V₂) (hc : Ctx M Q Z B) (hn : 1 ≤ n)
    (hcls : ∀ v : G, v ∈ Q → v ≠ 1 → (InZClass Z v ↔ v ∈ V₁ ∨ v ∈ V₂)) :
    (Subgroup.normalizer (V₁ : Set G)).relIndex M = 2 := by
  obtain ⟨-, hV₁Q, -, -, -, -, -, -, hV₁card, hV₂card⟩ := hW.basic
  have hne := hW.modules_ne hc hn
  obtain ⟨x, hxM, hxW⟩ : ∃ x ∈ M, conjSubgroup x V₁ = V₂ := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hswap, -⟩ := hW
    exact hswap
  have hpair : ∀ m ∈ M, conjSubgroup m V₁ = V₁ ∨ conjSubgroup m V₁ = V₂ :=
    fun m hm => conjSubgroup_eq_or_eq_of_inZClass_iff hc.hyp hV₁Q (hV₁card.trans hV₂card.symm)
      hcls hm
  refine Subgroup.index_eq_two_iff_exists_notMem_and.mpr ⟨⟨x, hxM⟩, ?_, fun b => ?_⟩
  · intro hxN
    exact hne (hxW.symm.trans (conjSubgroup_eq_self_iff.mpr (Subgroup.mem_subgroupOf.mp hxN))).symm
  · by_cases hbN : (b : G) ∈ Subgroup.normalizer (V₁ : Set G)
    · exact Or.inr (Subgroup.mem_subgroupOf.mpr hbN)
    · left
      have hbswap : conjSubgroup (b : G) V₁ = V₂ :=
        (hpair b b.2).resolve_left fun h => hbN (conjSubgroup_eq_self_iff.mp h)
      have hfix : conjSubgroup ((b : G) * x) V₁ = V₁ := by
        refine (hpair _ (M.mul_mem b.2 hxM)).resolve_right fun h => hne ?_
        rw [conjSubgroup_mul, hxW] at h
        exact Subgroup.map_injective (MulAut.conj (b : G)).injective
          (show conjSubgroup (b : G) V₁ = conjSubgroup (b : G) V₂ by rw [hbswap, h])
      exact Subgroup.mem_subgroupOf.mpr (conjSubgroup_eq_self_iff.mp hfix)

theorem outerOnFStar_of_lieModel_psl [Finite G]
    {M Q Z B : Subgroup G} {n : ℕ} (hc : Ctx M Q Z B) (hn : 1 ≤ n)
    (h31 : Lin31Prop M Q Z B n) {f : ℕ} (hf : Nat.card Z = 2 ^ f)
    (hL : CFSG.Blueprint.LieModel (FStar G) .PSL (n + 2) 2 f) : OuterOnFStar G := by
  by_contra hnot
  obtain ⟨W₁, W₂, hW, -, hcls⟩ := h31
  have hFG : Nat.card (FStar G) = Nat.card G := by
    show Nat.card ↥(generalizedFitting G) = Nat.card G
    rw [generalizedFitting_eq_top_of_not_outer hnot]
    exact Subgroup.card_top
  have hG2 : (Nat.card G).factorization 2 = f * ((n + 1) * (n + 2) / 2) :=
    hFG ▸ factorization_card_of_lieModel_psl hn hL
  have hL2 := factorization_card_Lgen hc hn hW hf
  have hcardM := Subgroup.relIndex_mul_card (H := Subgroup.normalizer (W₁ : Set G)) (K := M)
  rw [hW.relIndex_normalizer_eq_two hc hn hcls] at hcardM
  obtain ⟨-, -, -, -, -, -, hLN, -, -, -⟩ := hW.basic
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (le_inf hLN (Lgen_le_M hc))
  have hdvdG : 2 * Nat.card (Lgen M (LB M Q B)) ∣ Nat.card G :=
    (Dvd.intro k (by rw [← hcardM, hk]; ring)).trans (Subgroup.card_subgroup_dvd_card M)
  have hL0 : Nat.card (Lgen M (LB M Q B)) ≠ 0 := Nat.card_pos.ne'
  have hle := (Nat.factorization_le_iff_dvd (mul_ne_zero two_ne_zero hL0)
    Nat.card_pos.ne').mpr hdvdG 2
  rw [Nat.factorization_mul two_ne_zero hL0, Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two, hG2, hL2] at hle
  omega

end CFSG.RankThree.GF2n.Smith81
