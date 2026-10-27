module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res2Proof
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverRanks
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.RankThree.Coprime.ThompsonElementaryComplement
import CFSG.RankThree.PartOne.S11c.CentralWitness
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylow
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec21.Item21Statements
public import CFSG.RankThree.PartTwo.Sec6.Item611ResProof
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartTwo.Sec4.Item47
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec5.Hyp
import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace Res611Res3

@[expose] noncomputable def nilTwo (K : Type) [Field K] : K →+ Matrix (Fin 2) (Fin 2) K where
  toFun x := Matrix.of ![![0, x], ![0, 0]]
  map_zero' := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem nilTwo_mul {K : Type} [Field K] (x y : K) : nilTwo K x * nilTwo K y = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nilTwo, Matrix.mul_apply, Fin.sum_univ_two]

theorem nilTwo_injective {K : Type} [Field K] : Function.Injective (nilTwo K) := by
  intro x y h
  have h' := congrFun (congrFun h 0) 1
  simpa [nilTwo] using h'

theorem le_pRank_projSL_two {n : ℕ} (hn : 1 ≤ n) :
    n ≤ CFSG.pRank 3 (projSL 2 (GaloisField 3 n)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine Sec4.Census.le_pRank_of_sqZero (nilTwo _) nilTwo_injective nilTwo_mul (fun x => ?_)
    (projSL 2 _) (fun x => ?_) (GaloisField.card 3 n (by omega))
  · rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  · refine ⟨Sec4.Census.sqZeroUnit (nilTwo _) nilTwo_mul x, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    change (1 + nilTwo _ x).det = 1
    simp [Matrix.det_fin_two, nilTwo]

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_thetaQuotCentralizer (he : CFSG.Assembly.evenRank G = 3) {L B : Subgroup G}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (hBL : B ≤ L) (h81 : 81 ≤ Nat.card B) {t : G}
    (ht : t ∈ thetaQuotCentralizer L) (ht2 : t ^ 2 = 1) : t = 1 := by
  by_contra ht1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  set M := Subgroup.zpowers t ⊔ θL with hM
  have htN : t ∈ Subgroup.normalizer (L : Set G) := (mem_thetaQuotCentralizer_iff.mp ht).1
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hT2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hTθ : Subgroup.zpowers t ≤ Subgroup.normalizer (θL : Set G) :=
    Subgroup.zpowers_le.mpr (normalizer_le_normalizer_theta L htN)
  have hM3 : ¬ 3 ∣ Nat.card M :=
    not_dvd_card_sup_of_isPGroup Nat.prime_three (by norm_num) hT2 hTθ
      (theta_solvable_and_not_dvd L).2
  have hLM : L ≤ Subgroup.normalizer (M : Set G) := by
    apply le_normalizer_sup_of_conj
    · intro l hl x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have h1 : l * t * l⁻¹ ∈ M := by
        have h := (mem_thetaQuotCentralizer_iff.mp ht).2 l⁻¹ (L.inv_mem hl)
        rw [inv_inv] at h
        rw [show l * t * l⁻¹ = (l * (t * l⁻¹ * t⁻¹)) * t by group]
        exact M.mul_mem (Subgroup.mem_sup_right h)
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
      rw [← conj_zpow]
      exact M.zpow_mem h1 k
    · intro l hl x hx
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (le_normalizer_theta L hl) x).mp
        hx)
  have hB3 : IsPGroup 3 B := Sec5.isPGroup_of_isElemAbelian hB
  obtain ⟨R, hBR⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_in_prime_complement_subgroup
      3 Nat.prime_three B M hB3 hM3 (hBL.trans hLM) 2 Nat.prime_two
  set RG := (R : Subgroup M).map M.subtype with hRG
  have hRG2 : IsPGroup 2 RG := R.isPGroup'.map M.subtype
  have hRG1 : RG ≠ ⊥ := by
    intro hbot
    obtain ⟨y, -, hle⟩ := exists_le_conj_sylow R (le_sup_left : Subgroup.zpowers t ≤ M) hT2
    rw [← hRG, hbot, Subgroup.map_bot] at hle
    exact ht1 (Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers t)))
  have hcard := Sec5.card_le_of_le_normalizer he hRG1 hRG2 hB hBR
  omega

theorem inf_thetaQuotCentralizer_eq_bot_of_le (he : CFSG.Assembly.evenRank G = 3)
    {L B T : Subgroup G} (hB : CFSG.Assembly.IsElemAbelian 3 B) (hBL : B ≤ L)
    (h81 : 81 ≤ Nat.card B) (hT : CFSG.Assembly.IsElemAbelian 2 T) :
    T ⊓ thetaQuotCentralizer L = ⊥ := by
  rw [eq_bot_iff]
  rintro t ⟨htT, htC⟩
  exact eq_one_of_mem_thetaQuotCentralizer he hB hBL h81 htC (hT.2 t htT)

theorem odd_card_theta (he : CFSG.Assembly.evenRank G = 3) {B L : Subgroup G}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (h81 : 81 ≤ Nat.card B)
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) :
    Odd (Nat.card (inSubgroup (aschbacherSolvableCore 3) L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  have hθ3 : ¬ 3 ∣ Nat.card θL := (theta_solvable_and_not_dvd L).2
  have hBθ : B ≤ Subgroup.normalizer (θL : Set G) := hBL.trans (normalizer_le_normalizer_theta L)
  obtain ⟨R, hBR⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_in_prime_complement_subgroup
      3 Nat.prime_three B θL (Sec5.isPGroup_of_isElemAbelian hB) hθ3 hBθ 2 Nat.prime_two
  have hR2 : IsPGroup 2 ((R : Subgroup θL).map θL.subtype) := R.isPGroup'.map θL.subtype
  have hRbot : (R : Subgroup θL).map θL.subtype = ⊥ := by
    by_contra hne
    have := Sec5.card_le_of_le_normalizer he hne hR2 hB hBR
    omega
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  apply R.ne_bot_of_dvd_card h2
  rw [← Subgroup.map_eq_bot_iff_of_injective _ θL.subtype_injective]
  exact hRbot

theorem card_le_three_mul_card_inf {A L : Subgroup G} (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    {c : G} (hcA : c ∈ A) (hc1 : c ≠ 1) (hdec : A = Subgroup.zpowers c ⊔ (A ⊓ L)) :
    Nat.card A ≤ 3 * Nat.card (A ⊓ L : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : Subgroup.zpowers c ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · have h1 : c * y * c⁻¹ = y := by
        rw [show c * y = y * c from congrArg Subtype.val
          (hAe.1.is_comm.comm ⟨c, hcA⟩ ⟨y, hy.1⟩), mul_inv_cancel_right]
      rw [h1]
      exact hy
    · have hyA : y ∈ A := by
        have := A.mul_mem (A.mul_mem (A.inv_mem hcA) hy.1) hcA
        simpa [mul_assoc] using this
      have h2 : c * y * c⁻¹ = y := by
        rw [show c * y = y * c from congrArg Subtype.val
          (hAe.1.is_comm.comm ⟨c, hcA⟩ ⟨y, hyA⟩), mul_inv_cancel_right]
      rw [← h2]
      exact hy
  have hsurj : Function.Surjective (fun p : Subgroup.zpowers c × (A ⊓ L : Subgroup G) =>
      (⟨(p.1 : G) * p.2, by
        have h1 : (p.1 : G) ∈ A := Subgroup.zpowers_le.mpr hcA p.1.2
        exact A.mul_mem h1 p.2.2.1⟩ : A)) := by
    rintro ⟨a, ha⟩
    have haS : a ∈ Subgroup.zpowers c ⊔ (A ⊓ L) := hdec ▸ ha
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at haS
    obtain ⟨x, hx, l, hl, hxl⟩ := haS
    exact ⟨(⟨x, hx⟩, ⟨l, hl⟩), Subtype.ext hxl⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  rwa [Nat.card_prod, Nat.card_zpowers, orderOf_eq_prime (hAe.2 c hcA) hc1] at hle

end Res611Res3

open Res611Res3

theorem Res611Res3.odd_card_theta_of_config (h45 : Sec4.Item4_5) {G : Type} [Group G] [Finite G]
    (hst : PartTwoStanding G) {A : Subgroup G} (hA : A ∈ partTwoS G)
    (hrank : 4 < CFSG.Open.pRank 3 A) {c : G} (hcA : c ∈ A) (hc1 : c ≠ 1) {L : Subgroup G}
    (hLc : L ∈ thetaComponentsAt 3 c) :
    Odd (Nat.card (inSubgroup (aschbacherSolvableCore 3) L)) := by
  obtain ⟨m, hm5, hAcard⟩ := exists_card_eq_of_four_lt_pRank hA.1.1 hrank
  have hAL := le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp hA.1.1 hcA hc1 L hLc
  refine Res611Res3.odd_card_theta hst.evenRank_eq hA.1.1 ?_ hAL
  rw [hAcard]
  calc 81 = 3 ^ 4 := by norm_num
    _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.RankThree.PartTwo.Sec6
