module

public import CFSG.Quasithin.H13.NQBlockSolvableSourceY
public import CFSG.Quasithin.H13.NQTermPerfectRankTwo
public import CFSG.Quasithin.H13.NQCoreWholeModuleFrattini
public import CFSG.Quasithin.H13.NQBlockContainingLocals

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open CFSG.Quasithin.SteinbergCC (normalizerCoreQuotConj)
open CFSG.RankThree.CentralExtension (autCommutator)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_pCoreOf_of_perfect_action {H A Y : Subgroup G} {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hAH : A ≤ H) (hHA : H ≤ normalizer (A : Set G)) (hAp : ⁅A, A⁆ = A)
    (hYH : Y ≤ H) (hHY : H ≤ normalizer (Y : Set G)) (hYA : ¬ Y ≤ A)
    (hno : QuasithinUnique.Setup.Campbell.NoPQuotient 2 ↥Y)
    (hexp : Monoid.exponent (↥Y ⧸ CFSG.pCore 2 ↥Y) = r)
    (hrk : CFSG.pRank r (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤ 2) : ⁅A, Y⁆ ≤ pCoreOf 2 Y := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hAY : A ≤ normalizer (Y : Set G) := hAH.trans hHY
  set φ : ↥A →* MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    (normalizerCoreQuotConj Y).comp (Subgroup.inclusion hAY) with hφdef
  have hApf : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.mpr hAp
  have hDexp : ∀ x : ↥Y ⧸ CFSG.pCore 2 ↥Y, x ^ r = 1 := fun x => by
    rw [← hexp]
    exact Monoid.pow_exponent_eq_one x
  have hD : IsPGroup r (↥Y ⧸ CFSG.pCore 2 ↥Y) := fun x => ⟨1, by rw [pow_one]; exact hDexp x⟩
  have hφ : ∀ (a : ↥A) (y : ↥Y), φ a (y : ↥Y ⧸ CFSG.pCore 2 ↥Y) =
      ((⟨(a : G) * y * (a : G)⁻¹, (mem_normalizer_iff.mp (hAY a.2) y).mp y.2⟩ : ↥Y) :
        ↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    intro a y
    rfl
  rcases NQTerm.perfect_action_on_rank_two_exponent_prime_group_is_trivial_or_generating hr hr2
    hD hDexp hrk φ with hbot | ⟨htop, -⟩
  ·
    rw [commutator_le]
    intro a ha y hy
    have h1 : φ ⟨a, ha⟩ = 1 := by
      ext x
      obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective x
      have hm : (y' : ↥Y ⧸ CFSG.pCore 2 ↥Y)⁻¹ * φ ⟨a, ha⟩ (y' : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈
          autCommutator φ.range :=
        CFSG.RankThree.CentralExtension.inv_mul_apply_mem_autCommutator _ ⟨⟨a, ha⟩, rfl⟩
      rw [hbot, mem_bot, inv_mul_eq_one] at hm
      exact hm.symm
    have h2 := (NQCore.normalizerCoreQuotConj_eq_one_iff (X := Y) ⟨a, hAY ha⟩).mp h1 y hy
    rw [commutatorElement_def]
    exact h2
  ·
    exfalso
    apply hYA
    set C := ⁅Y, A⁆ with hCdef
    have hCY : C ≤ Y := by
      rw [hCdef, commutator_le]
      intro y hy a ha
      have e : ⁅y, a⁆ = y * (a * y⁻¹ * a⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact mul_mem hy ((mem_normalizer_iff.mp (hAY ha) _).mp (inv_mem hy))
    have hCA : C ≤ A := by
      rw [hCdef, commutator_le]
      intro y hy a ha
      have e : ⁅y, a⁆ = (y * a * y⁻¹) * a⁻¹ := by
        rw [commutatorElement_def]
      rw [e]
      exact mul_mem ((mem_normalizer_iff.mp (hHA (hYH hy)) a).mp ha) (inv_mem ha)
    have hCn : (C.subgroupOf Y).Normal := by
      rw [normal_subgroupOf_iff_le_normalizer hCY]
      intro y hy
      exact mem_normalizer_commutator (le_normalizer hy) (hHA (hYH hy))
    have hle : autCommutator φ.range ≤
        (C.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) := by
      rw [autCommutator, closure_le]
      rintro _ ⟨u, _, ⟨a, rfl⟩, rfl⟩
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective u
      refine ⟨y⁻¹ * ⟨(a : G) * y * (a : G)⁻¹, (mem_normalizer_iff.mp (hAY a.2) y).mp y.2⟩,
        mem_subgroupOf.mpr ?_, ?_⟩
      · have e : ((y⁻¹ * ⟨(a : G) * y * (a : G)⁻¹,
            (mem_normalizer_iff.mp (hAY a.2) y).mp y.2⟩ : ↥Y) : G) = ⁅(y : G)⁻¹, (a : G)⁆ := by
          rw [commutatorElement_def, inv_inv]
          change (y : G)⁻¹ * ((a : G) * y * (a : G)⁻¹) = _
          group
        rw [e]
        exact commutator_mem_commutator (inv_mem y.2) a.2
      · rw [map_mul, map_inv, hφ]
        rfl
    rw [htop] at hle
    have hq : IsPGroup 2 (↥Y ⧸ C.subgroupOf Y) := by
      intro x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨c, hc, hcy⟩ := hle (mem_top (y : ↥Y ⧸ CFSG.pCore 2 ↥Y))
      have hq : c⁻¹ * y ∈ CFSG.pCore 2 ↥Y := by
        rw [← QuotientGroup.eq]
        exact hcy
      obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (⟨c⁻¹ * y, hq⟩ : ↥(CFSG.pCore 2 ↥Y))
      refine ⟨k, ?_⟩
      have hyc : (y : ↥Y ⧸ C.subgroupOf Y) = ((c⁻¹ * y : ↥Y) : ↥Y ⧸ C.subgroupOf Y) := by
        rw [QuotientGroup.eq]
        have e : y⁻¹ * (c⁻¹ * y) = (y⁻¹ * c⁻¹ * y) := by group
        rw [e]
        exact hCn.conj_mem _ (inv_mem hc) _ |> fun h => by
          have e2 : y⁻¹ * c⁻¹ * y = y⁻¹ * c⁻¹ * y⁻¹⁻¹ := by rw [inv_inv]
          rw [e2]
          exact h
      rw [hyc, ← QuotientGroup.mk_pow]
      have h1 : (c⁻¹ * y) ^ 2 ^ k = 1 := congrArg Subtype.val hk
      rw [h1, QuotientGroup.mk_one]
    have hN := hno (C.subgroupOf Y) hq
    intro y hy
    have : (⟨y, hy⟩ : ↥Y) ∈ C.subgroupOf Y := by
      rw [hN]
      exact mem_top _
    exact hCA (mem_subgroupOf.mp this)

theorem allComponentsContainedCommutatorControl_holds :
    ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
      ∀ R : Subgroup G, (R : Set G) = nqOriginalCentralizer T L →
      ∀ H : Subgroup G, quasithinIsMaxTwoLocal H → nqOriginalK T L ⊔ T ≤ H → H ≠ M →
        (∀ C ∈ cComp H, C ≤ M) →
      ∀ A ∈ cComp H, nqOriginalK T L ≤ A → (∀ A' ∈ cComp H, nqOriginalK T L ≤ A' → A' = A) →
      ∀ (r : ℕ) (Y : Subgroup G), r.Prime → r ≠ 2 → Y ≤ H → (Y.subgroupOf H).Normal → ¬ Y ≤ M →
        QuasithinUnique.Setup.Campbell.NoPQuotient 2 ↥Y →
        Monoid.exponent (↥Y ⧸ CFSG.pCore 2 ↥Y) = r →
        Subgroup.upperCentralSeries (↥Y ⧸ CFSG.pCore 2 ↥Y) 2 = ⊤ →
        CFSG.pRank r (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤ 2 →
          A ≤ L ∧ L ≤ M ∧ nqComplementaryLayer H A ≤ M ∧ ⁅A, Y⁆ ≤ pCoreOf 2 Y ∧
          ⁅nqOriginalK T L, Y⁆ ≤ pCoreOf 2 (nqOriginalK T L) ⊓ pCoreOf 2 Y ∧
          pCoreOf 2 Y ≤ pCoreOf 2 H ∧ pCoreOf 2 H ≤ R ∧
          Y ≤ normalizer (nqOriginalK T L : Set G) ∧ T ⊓ Y ≤ R ∧
          CFSG.ABGLocalTools.IsSylowOf 2 R (Y ⊔ R) ∧ QuasithinUnique.CharTwo Y ∧
          QuasithinUnique.CharTwo (Y ⊔ R) ∧ pCoreOf 2 Y ≠ ⊥ ∧
          ⁅quasithinOmegaOneCenter T, Y⁆ ≠ ⊥ := by
  intro G _ _ T L M h R hR H hH hKTH hHM hall A hA hKA hAu r Y hr hr2 hYH hYn hYM hno hexp _ hrk
  classical
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKf, -⟩ := original_common_residual_is_faithful_and_has_exact_reduced_action_kernel h hR
  obtain ⟨hKL, hTK, -⟩ := original_K_quotient_facts h
  have hTH : T ≤ H := le_sup_right.trans hKTH
  have hO2H := CFSG.Quasithin.pCoreOf_ne_bot_of_isTwoLocal hH.1
  have hTsH := isSylowTwoOf_of_qtnq h hTH
  have hO2M := CFSG.Quasithin.pCoreOf_ne_bot_of_isTwoLocal h.max_two_local.1
  have hTsM := isSylowTwoOf_of_qtnq h h.t_le
  have hAM : A ≤ M := hall A hA
  have hAloc : quasithinIsLocal T A := QuasithinUnique.Vol2Native.isLocal_of_mem_cComp hO2H hTsH hA
  obtain ⟨C, ⟨hC, hAC⟩, -⟩ := QuasithinUnique.Vol2Native.existsUnique_cComp_ge_of_isLocal
    h.nonabelian h.qtke hO2M hTsM hAM hAloc
  obtain ⟨L₀, ⟨hL₀, -⟩, -, -, hmax⟩ := sylowNormalizedLocalNormalComponent_proved G h.nonabelian
    h.qtke M T L hO2M hTsM h.l_le h.maximal_local.1 (h.eq_normalizer ▸ h.t_le)
  obtain ⟨hL₀L, -⟩ := hmax h.maximal_local
  rw [hL₀L] at hL₀
  obtain ⟨C', -, hC'u⟩ := QuasithinUnique.Vol2Native.existsUnique_cComp_ge_of_isLocal
    h.nonabelian h.qtke hO2M hTsM (hKL.trans h.l_le) hKf.1
  have hCL : C = L := (hC'u C ⟨hC, hKA.trans hAC⟩).trans (hC'u L ⟨hL₀, hKL⟩).symm
  have hAL : A ≤ L := hCL ▸ hAC
  have hAH : A ≤ H := le_of_mem_cComp hA
  have hHA : H ≤ normalizer (A : Set G) := by
    obtain ⟨A', ⟨hA', hKA'⟩, hA'u, hA'n, -⟩ := sylowNormalizedLocalNormalComponent_proved G
      h.nonabelian h.qtke H T (nqOriginalK T L) hO2H hTsH (le_sup_left.trans hKTH) hKf.1 hTK
    rw [hAu A' hA' hKA'] at hA'n
    exact (normal_subgroupOf_iff_le_normalizer hAH).mp hA'n
  have hHY : H ≤ normalizer (Y : Set G) := (normal_subgroupOf_iff_le_normalizer hYH).mp hYn
  have hAY : ⁅A, Y⁆ ≤ pCoreOf 2 Y := commutator_le_pCoreOf_of_perfect_action hr hr2 hAH hHA
    (perfect_of_mem_cComp hA) hYH hHY (fun hYA => hYM (hYA.trans hAM)) hno hexp hrk
  have hKY : ⁅nqOriginalK T L, Y⁆ ≤ pCoreOf 2 Y := (commutator_mono hKA le_rfl).trans hAY
  obtain ⟨-, -, -, hcore⟩ :=
    normal_original_K_overgroup_factors_have_core_containment_and_commutator_transport h hR
  obtain ⟨hYP, hPR, hrest⟩ := hcore H Y hKTH hYH hYn
  obtain ⟨-, hYNK, hKYQ, -, hTY, hSyl⟩ := hrest hKY
  have hH2 : QuasithinUnique.CharTwo H :=
    QuasithinUnique.charTwo_of_isSylowTwoOf_le_of_pCore_ne_bot h.qtke.2.1
      (isSylowTwoOf_top_of_qtnq h) hTH hO2H
  have hY2 : QuasithinUnique.CharTwo Y := QuasithinUnique.CharTwo.of_normal hH2 hYH hYn
  have hRT : R ≤ T := fun t ht => by
    rw [← SetLike.mem_coe, hR] at ht
    exact ht.1
  have hYRH : Y ⊔ R ≤ H := sup_le hYH (hRT.trans hTH)
  have hPYR : pCoreOf 2 H ≤ pCoreOf 2 (Y ⊔ R) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hPR.trans le_sup_right)
      (hYRH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  have hYR2 : QuasithinUnique.CharTwo (Y ⊔ R) := fun x hx =>
    hPYR (hH2 ⟨hYRH hx.1, centralizer_le hPYR hx.2⟩)
  have hqY : pCoreOf 2 Y ≠ ⊥ := by
    intro h0
    apply hYM
    intro y hy
    have hy' : y ∈ pCoreOf 2 Y := hY2 (mem_inf.mpr ⟨hy, by
      rw [h0]
      exact mem_centralizer_iff.mpr fun z hz => by
        rw [(mem_bot.mp hz : z = 1), one_mul, mul_one]⟩)
    rw [h0, mem_bot] at hy'
    rw [hy']
    exact one_mem M
  have hZY : ⁅quasithinOmegaOneCenter T, Y⁆ ≠ ⊥ := by
    intro h0
    apply hYM
    rw [commutator_eq_bot_iff_le_centralizer] at h0
    exact (le_centralizer_iff.mp h0).trans h.centralizer_le
  exact ⟨hAL, h.l_le, sSup_le fun C hC => hall C hC.1, hAY, hKYQ, hYP, hPR, hYNK, hTY, hSyl, hY2,
    hYR2, hqY, hZY⟩

theorem allComponentsContainedSourceY_holds :
    AllComponentsContainedSourceY := by
  intro G _ _ T L M h H hH hKTH hHM hall A hA hKA hAu
  obtain ⟨R, hR⟩ := exists_originalCentralizer (h.t_le.trans h.eq_normalizer.le)
  obtain ⟨r, D, Y, hr, hr2, -, -, -, -, -, -, hYH, hYn, -, hYM, -, hno, -, -, -, -, -, -, hexp,
    hcls, hrk, hcard⟩ :=
    allComponentsContainedSolvableSourceY_holds G T L M h H hH (le_sup_right.trans hKTH) hHM hall
  obtain ⟨-, -, -, -, hKY, -⟩ := allComponentsContainedCommutatorControl_holds G T L M h R hR H hH
    hKTH hHM hall A hA hKA hAu r Y hr hr2 hYH hYn hYM hno hexp hcls hrk
  exact ⟨r, Y, hr, hr2, hYH, hYn, hYM, hexp, hcls, hrk, hcard, hKY⟩

end CFSG.Quasithin.H13.NQBlock
