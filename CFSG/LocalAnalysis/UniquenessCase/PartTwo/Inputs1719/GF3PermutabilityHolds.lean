module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF3Lie
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF3PermFun
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdBorelGeneric
public import CFSG.ClassicalInvolution.Q3.TL4SecIdLieE
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AFix
public import CFSG.GroupTheory.QuasisimpleOddCenterQuotient
import CFSG.GroupTheory.CentralizerMapCentralKernel
public import CFSG.GroupTheory.LiftPermutes
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227Eq
public import CFSG.Quasithin.Vol2.Ch10SecQ9G11
public import CFSG.GH74.Generic.BProg.B2.L3Cover
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsL3EpsOdd17)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm (PermWitness)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3Odd)

private theorem center_eq_pCore_of_center_quotient_eq_bot
    {K : Type} [Group K] [Finite K] (hKq : CFSG.Open.IsQuasisimple K)
    (hZbar : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥) :
    Subgroup.center K = CFSG.pCore 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOZ : CFSG.pCore 2 K ≤ Subgroup.center K := GL83.I243.Cover.pCore_le_center hKq
  refine le_antisymm ?_ hOZ
  intro z hz
  have hzbar : (QuotientGroup.mk' (CFSG.pCore 2 K)) z ∈
      Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) y
    rw [← map_mul, ← map_mul]
    exact congrArg (QuotientGroup.mk' (CFSG.pCore 2 K))
      (Subgroup.mem_center_iff.mp hz y)
  rw [hZbar, Subgroup.mem_bot] at hzbar
  exact (QuotientGroup.eq_one_iff z).mp hzbar

private theorem lieModel_psl_of_lieModel_pCore_quotient
    {K : Type} [Group K] [Finite K] (hKq : CFSG.Open.IsQuasisimple K)
    (h : LieModel (K ⧸ CFSG.pCore 2 K) .PSL 3 3 1) : LieModel K .PSL 3 3 1 := by
  have hZbar : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥ :=
    CFSG.Quasithin.F420.center_eq_bot_of_statedPSL
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h)
  have hZ : Subgroup.center K = CFSG.pCore 2 K :=
    center_eq_pCore_of_center_quotient_eq_bot hKq hZbar
  have h' : LieModel (K ⧸ Subgroup.center K) .PSL 3 3 1 :=
    h.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  exact (CFSG.GH74.Generic.BProg.B2.l3_three_cover_center
    (CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F.isQuasisimple_of_open' hKq) h').2


private theorem lieModel_psu_three_of_lieModel_quotient_center
    {K : Type} [Group K] [Finite K] (hKq : CFSG.Open.IsQuasisimple K)
    (h : LieModel (K ⧸ Subgroup.center K) .PSU 3 3 1) :
    Subgroup.center K = ⊥ ∧ LieModel K .PSU 3 3 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPSUadm : StatedLieAdmissible .PSU 3 3 1 :=
    ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
  obtain ⟨ψ, hψs, hψk⟩ :=
    OddLie.exists_cover_of_lieModel_three_full (t := .PSU) (n := 3) trivial hPSUadm hKq h
      (by decide)
  have hZU : Subgroup.center
      (CFSG.ClassicalInvolution.Generic.modelUniv .PSU 3 3 1 Nat.prime_three).K = ⊥ :=
    CFSG.ClassicalInvolution.Q3.TL4.center_modelUniv_psu_three Nat.prime_three
  have hUq := (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .PSU 3 3 1
    Nat.prime_three trivial hPSUadm).1
  have hperf : Group.IsPerfect
      (CFSG.ClassicalInvolution.Generic.modelUniv .PSU 3 3 1 Nat.prime_three).K :=
    ⟨hUq.1⟩
  have hZK : Subgroup.center K = ⊥ := by
    rw [← CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel ψ hψs hψk,
      hZU, Subgroup.map_bot]
  exact ⟨hZK, LieModel.of_quotient_center hZK h⟩

private theorem lieModel_psu_of_lieModel_pCore_quotient
    {K : Type} [Group K] [Finite K] (hKq : CFSG.Open.IsQuasisimple K)
    (h : LieModel (K ⧸ CFSG.pCore 2 K) .PSU 3 3 1) : LieModel K .PSU 3 3 1 := by
  have : (CFSG.Open.pCoreOf 2 (Subgroup.center K)).Normal :=
    Subgroup.normal_of_le_center (CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 _)
  have hqsbar : CFSG.Open.IsQuasisimple (K ⧸ CFSG.pCore 2 K) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq
        (CFSG.GroupTheory.pCoreOf_center_eq_pCore hKq)).symm
      (CFSG.GroupTheory.isQuasisimple_quotient_pCoreOf_center hKq)
  have hZbar : Subgroup.center (K ⧸ CFSG.pCore 2 K) = ⊥ :=
    (CFSG.Quasithin.H13.Lem1227Eq.card_center_of_lieModel_psu
      (CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F.isQuasisimple_of_open' hqsbar) h).2
  have hZ : Subgroup.center K = CFSG.pCore 2 K :=
    center_eq_pCore_of_center_quotient_eq_bot hKq hZbar
  have h' : LieModel (K ⧸ Subgroup.center K) .PSU 3 3 1 :=
    h.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  exact (lieModel_psu_three_of_lieModel_quotient_center hKq h').2

private theorem gf3_permutability_odd_core (hFC : K_FunCommuteThree)
    {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} (hKn : K.Normal)
    (hKq : CFSG.Open.IsQuasisimple ↥K) (hodd : Odd (Nat.card (Subgroup.center ↥K)))
    (hlie : ∃ (t : StatedLieTag) (n : ℕ),
      StatedLieAdmissible t n 3 1 ∧
        LieModel (↥K ⧸ Subgroup.center ↥K) t n 3 1)
    (hL3 : ¬ IsL3Odd ↥K 3 ∧ ¬ LieModel ↥K .PSU 3 3 1)
    {S : Subgroup Y} (hS : CFSG.Quasithin.IsSylowIn 2 S ⊤) :
    ∃ E : Subgroup Y,
      E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧ ¬ IsCyclic ↥E ∧
        CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
  classical
  obtain ⟨t, n, hadm, hX⟩ := hlie
  let X : Type := ↥K ⧸ Subgroup.center ↥K
  have hXq : CFSG.Open.IsQuasisimple X :=
    CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_quotient_center hKq
  have hZ : Subgroup.center X = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.KOB.center_quotient_eq_bot hKq
  have hKqC : CFSG.IsQuasisimple ↥K :=
    CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F.isQuasisimple_of_open' hKq
  have hL3X : ¬ IsL3EpsOdd17 X 3 := by
    rintro (hPSL | hPSU)
    · exact hL3.1 (CFSG.GH74.Generic.BProg.B2.l3_three_cover_center hKqC hPSL).2
    · exact hL3.2 (lieModel_psu_three_of_lieModel_quotient_center hKq hPSU).2
  let e : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hX' : LieModel (X ⧸ Subgroup.center X) t n 3 1 := hX.of_mulEquiv e.symm
  have hL3' : ¬ IsL3EpsOdd17 (X ⧸ Subgroup.center X) 3 := by
    rintro (hPSL | hPSU)
    · exact hL3X (Or.inl (hPSL.of_mulEquiv e))
    · exact hL3X (Or.inr (hPSU.of_mulEquiv e))
  exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.exists_permutes_of_permWitness hKn
    hodd (permWitness_of_lie_three hFC hXq hZ hadm hX' hL3') hS

theorem gf3_permutability_odd_of_funCommuteThree (hFC : K_FunCommuteThree) :
    ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y),
      K.Normal →
      CFSG.Open.IsQuasisimple ↥K →
      Odd (Nat.card (Subgroup.center ↥K)) →
      (∃ (t : StatedLieTag) (n : ℕ),
        StatedLieAdmissible t n 3 1 ∧
          LieModel (↥K ⧸ Subgroup.center ↥K) t n 3 1) →
      (¬ IsL3Odd ↥K 3 ∧ ¬ LieModel ↥K .PSU 3 3 1) →
      Subgroup.centralizer (K : Set Y) = (Subgroup.center ↥K).map K.subtype →
      (∃ n : ℕ, K.index = 2 ^ n) →
      ∀ S : Subgroup Y, CFSG.Quasithin.IsSylowIn 2 S ⊤ →
        ∃ E : Subgroup Y,
          E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧ ¬ IsCyclic ↥E ∧
            CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
  intro Y _ _ K hKn hKq hodd hlie hL3 _ _ S hS
  exact gf3_permutability_odd_core hFC hKn hKq hodd hlie hL3 hS

theorem k_GF3_permutability_of_funCommuteThree (hFC : K_FunCommuteThree) :
    K_GF3_permutability := by
  intro Y _ _ K hKn hKq hlie hL3 hcent hidx S hS
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup Y := (CFSG.pCore 2 ↥K).map K.subtype
  have hO_le_K : O ≤ K := Subgroup.map_subtype_le _
  have hOp : IsPGroup 2 O := (CFSG.pCore_isPGroup (p := 2)).map K.subtype
  have : K.Normal := hKn
  have hO_normal : O.Normal :=
    ConjAct.normal_of_characteristic_of_normal (H := K) (K := CFSG.pCore 2 ↥K)
  have hO_le_S : O ≤ S :=
    hS.le_of_normal le_top (hO_normal.subgroupOf ⊤) hOp
  let Ybar : Type := Y ⧸ O
  have : Finite Ybar :=
    Finite.of_surjective (QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
  let Kbar : Subgroup Ybar := K.map (QuotientGroup.mk' O)
  have hKbar_normal : Kbar.Normal :=
    hKn.map (QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
  let f : ↥K →* Ybar := (QuotientGroup.mk' O).comp K.subtype
  have hfker : f.ker = CFSG.pCore 2 ↥K := by
    ext x
    constructor
    · intro hx
      have hxO : ((x : ↥K) : Y) ∈ O := (QuotientGroup.eq_one_iff _).mp hx
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxO
      rwa [show z = x from Subtype.ext hzx] at hz
    · intro hx
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_map_of_mem K.subtype hx)
  have hfrange : f.range = Kbar := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Subgroup.mem_map_of_mem (QuotientGroup.mk' O) x.2
    · intro hy
      obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨k, hk⟩, hky⟩
  let eK : ↥Kbar ≃* (↥K ⧸ CFSG.pCore 2 ↥K) :=
    ((MulEquiv.subgroupCongr hfrange).symm.trans
      (QuotientGroup.quotientKerEquivRange f).symm).trans
      (QuotientGroup.quotientMulEquivOfEq hfker)
  have hKperf : Group.IsPerfect ↥K := ⟨hKq.1⟩
  have hker_center : (QuotientGroup.mk' O).ker ≤ (Subgroup.center ↥K).map K.subtype := by
    rw [QuotientGroup.ker_mk']
    exact Subgroup.map_mono (GL83.I243.Cover.pCore_le_center hKq)
  have hcentbar : Subgroup.centralizer (Kbar : Set Ybar) =
      (Subgroup.center ↥Kbar).map Kbar.subtype := by
    have hgen := CFSG.GroupTheory.centralizer_map_eq_map_centralizer_of_perfect
      (QuotientGroup.mk' O)
      (QuotientGroup.mk'_surjective O) hKperf hker_center
    rw [hcent] at hgen
    rw [Subgroup.map_map] at hgen
    let f' : ↥K →* ↥Kbar := f.codRestrict Kbar (fun x => by
      rw [← hfrange]
      exact MonoidHom.mem_range.mpr ⟨x, rfl⟩)
    have hf' : Function.Surjective f' := by
      intro y
      have hy : (y : Ybar) ∈ f.range := by rw [hfrange]; exact y.2
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
      exact ⟨x, Subtype.ext hx⟩
    have hf'ker : f'.ker = f.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, Subtype.ext_iff]
      rfl
    have hker' : f'.ker ≤ Subgroup.center ↥K := by
      intro x hx
      have hx' : x ∈ CFSG.pCore 2 ↥K := by
        rw [← hfker, ← hf'ker]
        exact hx
      exact GL83.I243.Cover.pCore_le_center hKq hx'
    have hcenter' : (Subgroup.center ↥K).map f' = Subgroup.center ↥Kbar :=
      CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel f' hf' hker'
    have hcenterY : (Subgroup.center ↥K).map f = (Subgroup.center ↥Kbar).map Kbar.subtype := by
      rw [← hcenter', Subgroup.map_map]
      rfl
    rw [hgen, hcenterY]
  have hidxbar : ∃ n : ℕ, Kbar.index = 2 ^ n := by
    obtain ⟨n, hn⟩ := hidx
    refine ⟨n, ?_⟩
    have hidxK : Kbar.index = K.index := by
      change (K.map (QuotientGroup.mk' O)).index = K.index
      rw [Subgroup.index_map K (QuotientGroup.mk' O), QuotientGroup.ker_mk',
        MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective O),
        Subgroup.index_top, mul_one, sup_eq_left.mpr hO_le_K]
    rw [hidxK, hn]
  have hKbar_qs : CFSG.Open.IsQuasisimple ↥Kbar := by
    have h : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
      have : (CFSG.Open.pCoreOf 2 (Subgroup.center ↥K)).Normal :=
        Subgroup.normal_of_le_center (CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 _)
      exact CFSG.Open.IsQuasisimple.of_mulEquiv
        (QuotientGroup.quotientMulEquivOfEq
          (CFSG.GroupTheory.pCoreOf_center_eq_pCore hKq)).symm
        (CFSG.GroupTheory.isQuasisimple_quotient_pCoreOf_center hKq)
    exact CFSG.Open.IsQuasisimple.of_mulEquiv eK h
  have hKbar_odd : Odd (Nat.card (Subgroup.center ↥Kbar)) := by
    have h : Odd (Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K))) := by
      have : (CFSG.Open.pCoreOf 2 (Subgroup.center ↥K)).Normal :=
        Subgroup.normal_of_le_center (CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 _)
      let e₁ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃*
          (↥K ⧸ CFSG.Open.pCoreOf 2 (Subgroup.center ↥K)) :=
        (QuotientGroup.quotientMulEquivOfEq
          (CFSG.GroupTheory.pCoreOf_center_eq_pCore hKq)).symm
      rw [Nat.card_congr (Subgroup.centerCongr e₁).toEquiv]
      exact CFSG.GroupTheory.odd_card_center_quotient_pCoreOf_center hKq
    rw [Nat.card_congr (Subgroup.centerCongr eK).toEquiv]
    exact h
  obtain ⟨t, n, hadm, hX⟩ := hlie
  have hXbar : LieModel (↥Kbar ⧸ Subgroup.center ↥Kbar) t n 3 1 := by
    let eZ : (↥Kbar ⧸ Subgroup.center ↥Kbar) ≃*
        (↥K ⧸ Subgroup.center ↥K) :=
      (QuotientGroup.congr (Subgroup.center ↥Kbar)
        (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) eK
        (Subgroup.map_center_eq eK)).trans
        (by
          have : (CFSG.Open.pCoreOf 2 (Subgroup.center ↥K)).Normal :=
            Subgroup.normal_of_le_center (CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 _)
          let e₁ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃*
              (↥K ⧸ CFSG.Open.pCoreOf 2 (Subgroup.center ↥K)) :=
            (QuotientGroup.quotientMulEquivOfEq
              (CFSG.GroupTheory.pCoreOf_center_eq_pCore hKq)).symm
          exact (QuotientGroup.congr
            (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K))
            (Subgroup.center (↥K ⧸ CFSG.Open.pCoreOf 2 (Subgroup.center ↥K))) e₁
            (Subgroup.map_center_eq e₁)).trans
            (CFSG.GroupTheory.quotientPCoreOfCenterEquiv hKq))
    exact hX.of_mulEquiv eZ.symm
  have hL3bar : ¬ IsL3Odd ↥Kbar 3 ∧ ¬ LieModel ↥Kbar .PSU 3 3 1 := by
    constructor
    · intro hPSL
      exact hL3.1 (lieModel_psl_of_lieModel_pCore_quotient hKq (hPSL.of_mulEquiv eK))
    · intro hPSU
      exact hL3.2 (lieModel_psu_of_lieModel_pCore_quotient hKq (hPSU.of_mulEquiv eK))
  let Sbar : Subgroup Ybar := S.map (QuotientGroup.mk' O)
  have hSbar : CFSG.Quasithin.IsSylowIn 2 Sbar ⊤ := by
    refine ⟨le_top, hS.isPGroup.map _, ?_⟩
    intro h2
    apply hS.not_dvd_relIndex
    rw [Subgroup.relIndex_top_right]
    rw [Subgroup.relIndex_top_right] at h2
    have hidxS : Sbar.index = S.index := by
      change (S.map (QuotientGroup.mk' O)).index = S.index
      rw [Subgroup.index_map S (QuotientGroup.mk' O), QuotientGroup.ker_mk',
        MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective O),
        Subgroup.index_top, mul_one, sup_eq_left.mpr hO_le_S]
    rwa [hidxS] at h2
  obtain ⟨Ebar, hEbar_le, hEbar_ne, hEbar_p, hEbar_exp, hEbar_ncyc, hEbar_perm⟩ :=
    gf3_permutability_odd_of_funCommuteThree hFC Ybar Kbar hKbar_normal hKbar_qs hKbar_odd
      ⟨t, n, hadm, hXbar⟩ hL3bar hcentbar hidxbar Sbar hSbar
  obtain ⟨E, hEp, hEmap, ⟨eE⟩, hEperm⟩ :=
    CFSG.GroupTheory.exists_permutes_lift (QuotientGroup.mk' O)
      (QuotientGroup.mk'_surjective O) hS.isPGroup
      (by rw [QuotientGroup.ker_mk']; exact hO_le_S) (p := 3) (by norm_num) hEbar_p
      (by simpa only [Sbar, CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes] using hEbar_perm)
  have hE_le_K : E ≤ K := by
    intro x hx
    have hxbar : (QuotientGroup.mk' O) x ∈ Ebar := by
      rw [← hEmap]
      exact Subgroup.mem_map_of_mem (QuotientGroup.mk' O) hx
    have hxKbar : (QuotientGroup.mk' O) x ∈ Kbar := hEbar_le hxbar
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hxKbar
    have hxk : x * k⁻¹ ∈ O := by
      refine (QuotientGroup.eq_one_iff (x * k⁻¹)).mp ?_
      change (QuotientGroup.mk' O) (x * k⁻¹) = 1
      rw [map_mul, map_inv, hkx, mul_inv_cancel]
    have hxeq : x = (x * k⁻¹) * k := by group
    rw [hxeq]
    exact K.mul_mem (hO_le_K hxk) hk
  have hE_ne : E ≠ ⊥ := by
    intro hEbot
    exact hEbar_ne (by rw [← hEmap, hEbot, Subgroup.map_bot])
  have hE_exp : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥E) ^ 3 = 1 := by
      apply eE.injective
      rw [map_pow, map_one]
      have h1 : (eE ⟨x, hx⟩ : ↥Ebar) ^ 3 = 1 := by
        apply Subtype.ext
        simpa using hEbar_exp (eE ⟨x, hx⟩) (eE ⟨x, hx⟩).2
      exact h1
    simpa using congrArg Subtype.val hx'
  have hE_ncyc : ¬ IsCyclic ↥E := by
    intro hcyc
    exact hEbar_ncyc (isCyclic_of_surjective eE.toMonoidHom eE.surjective)
  exact ⟨E, hE_le_K, hE_ne, hEp, hE_exp, hE_ncyc, hEperm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
