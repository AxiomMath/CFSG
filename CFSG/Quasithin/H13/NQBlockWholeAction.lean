module

public import CFSG.Quasithin.H13.NQBlockSolvableSource
public import CFSG.Quasithin.H13.NQBlockSourceRank
public import CFSG.Quasithin.H13.NQBlockOriginalOvergroup
public import CFSG.Quasithin.H13.NQBlockFiveModelRigidity
public import CFSG.Foundations.SteinbergCAGeneratedCoreNodes
public import CFSG.Quasithin.H13.NQBlockSourceModule

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open scoped commutatorElement

theorem normalSourceWholeActionOdd_holds :
    NormalSourceWholeActionOdd := by
  intro G _ _ T L M h R hR H hH hKTH hHM Y hYH hYn hYM hKY p hp hp2 hexp hcl hrk
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := nqOriginalK T L with hKdef
  set W := nqSourceModule Y R with hWdef
  obtain ⟨hTK, -, hRchar, htrans⟩ :=
    normal_original_K_overgroup_factors_have_core_containment_and_commutator_transport h hR
  obtain ⟨hOYH, hOHR, htr⟩ := htrans H Y hKTH hYH hYn
  obtain ⟨-, hYK, -, hYc, -, hSyl⟩ := htr hKY
  obtain ⟨-, hRKT, -⟩ := original_radical_supplements_share_simple_residual_and_internal_module h hR
  have hTH : T ≤ H := le_sup_right.trans hKTH
  have hKH : K ≤ H := le_sup_left.trans hKTH
  have hRT : R ≤ T := fun r hr => by
    rw [← SetLike.mem_coe, hR] at hr
    exact hr.1
  have hRH : R ≤ H := hRT.trans hTH
  have hSH : Y ⊔ R ≤ H := sup_le hYH hRH
  have hHY : H ≤ normalizer (Y : Set G) := (normal_subgroupOf_iff_le_normalizer hYH).mp hYn
  have hRY : R ≤ normalizer (Y : Set G) := hRH.trans hHY
  have hKY' : K ≤ normalizer (Y : Set G) := hKH.trans hHY
  have hKR : K ≤ normalizer (R : Set G) := by
    rw [hRKT]
    exact le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hSyl' : QuasithinUnique.IsSylowTwoOf R (Y ⊔ R) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mp hSyl
  have hT' : QuasithinUnique.IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, h.sylow.1, ?_⟩
    change ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact h.sylow.2
  have hHc : QuasithinUnique.CharTwo H :=
    QuasithinUnique.charTwo_of_isTwoLocal_of_isSylowTwoOf_le h.qtke.2.1 hT' hH.1 hTH
  have hOHS : pCoreOf 2 H ≤ pCoreOf 2 (Y ⊔ R) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hOHR.trans le_sup_right)
      (hSH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  have hchar : QuasithinUnique.CharTwo (Y ⊔ R) := fun x hx =>
    hOHS (hHc ⟨hSH hx.1, centralizer_le hOHS hx.2⟩)
  have hWZ := nqSourceModule_le_omegaOneCenterOf_pCoreOf hSyl' hchar
  have hOR : pCoreOf 2 (Y ⊔ R) ≤ R := QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSyl'
  have hOW : pCoreOf 2 (Y ⊔ R) ≤ centralizer (W : Set G) := fun o ho =>
    mem_centralizer_iff.mpr fun w hw => (mem_omegaOneCenterOf_iff.mp (hWZ hw)).2.1 o ho
  have hKTQ : K ⊔ T ≤ normalizer (pCoreOf 2 K : Set G) :=
    sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
      (hTK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
  have hQKR : pCoreOf 2 K ≤ R := by
    rw [hRKT]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left) hKTQ
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hQKO : pCoreOf 2 K ≤ pCoreOf 2 (Y ⊔ R) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQKR.trans le_sup_right)
      (sup_le (hYK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
        (hRT.trans (le_sup_right.trans hKTQ)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hKRQ : ⁅K, R⁆ ≤ pCoreOf 2 K := by
    rw [Subgroup.commutator_le]
    intro k hk t ht
    have h1 := ((hRchar t).mp ht).2 k⁻¹ (K.inv_mem hk)
    have e : ⁅k, t⁆ = k * (t * k⁻¹ * t⁻¹ * k⁻¹⁻¹) * k⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hk) _).mp h1
  refine ⟨isElementaryAbelian_of_le_omegaOneCenterOf hWZ,
    hWZ.trans (((omegaOneCenterOf_le 2 _).trans inf_le_left).trans hOR),
    fun k hk => mem_normalizer_nqSourceModule (hKY' hk) (hKR hk),
    le_sup_left.trans (le_normalizer_nqSourceModule Y R),
    le_sup_right.trans (le_normalizer_nqSourceModule Y R),
    (hOYH.trans hOHS).trans hOW, (hKRQ.trans hQKO).trans hOW,
    fun r hr hry => mem_centralizer_nqSourceModule_of_commutator hRY hr hry, fun hp3 => ?_⟩
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, hKs, ⟨a, b, hab⟩, s, hs, hs5, -, hKcard⟩ := original_K_quotient_facts h
  have : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := hKs
  have hZ : center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (↥K ⧸ CFSG.pCore 2 ↥K)) with
      h0 | h0
    · exact h0
    · exact absurd ((mem_center_iff.mp (h0 ▸ mem_top b)) a) hab
  have hcen : ∀ k ∈ K, (∀ k' ∈ K, k * k' * k⁻¹ * k'⁻¹ ∈ pCoreOf 2 K) → k ∈ pCoreOf 2 K := by
    intro k hk hc
    have hmem : (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) ∈
        center (↥K ⧸ CFSG.pCore 2 ↥K) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        mem_pCore_iff_mem_pCoreOf]
      have h1 : k * (k' : G)⁻¹ * k⁻¹ * k' ∈ pCoreOf 2 K := by
        have := hc _ (K.inv_mem k'.2)
        rwa [inv_inv] at this
      change (k' * k : G)⁻¹ * (k * k') ∈ pCoreOf 2 K
      have e : ((k' : G) * k)⁻¹ * (k * k') = k⁻¹ * (k * (k' : G)⁻¹ * k⁻¹ * k')⁻¹ * k⁻¹⁻¹ := by
        group
      rw [e]
      have hkinv : k⁻¹ ∈ normalizer (pCoreOf 2 K : Set G) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K (K.inv_mem hk)
      exact (mem_normalizer_iff.mp hkinv _).mp (inv_mem h1)
    rw [hZ, mem_bot, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf] at hmem
    exact hmem
  have h3dvd : 3 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rw [hKcard]
    exact three_dvd_half_order hs hs5
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  obtain ⟨⟨k₀, hk₀⟩, rfl⟩ := QuotientGroup.mk_surjective x
  have hk₀3 : k₀ ^ 3 ∈ pCoreOf 2 K := by
    have h1 := pow_orderOf_eq_one (QuotientGroup.mk (⟨k₀, hk₀⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K)
    rw [hx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf] at h1
    exact h1
  have hk₀Q : k₀ ∉ pCoreOf 2 K := by
    intro h1
    rw [← mem_pCore_iff_mem_pCoreOf (b := ⟨k₀, hk₀⟩), ← QuotientGroup.eq_one_iff] at h1
    rw [h1, orderOf_one] at hx
    omega
  have hH3 : CFSG.pRank 3 ↥H ≤ 2 := by
    rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_three H]
    exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) H hH.1).trans h.qtke.2.2
  have hrk1 := pRank_three_le_one_of_commuting_simple hKH hYH hH3 hKY' hYK hYc hKY hcen hk₀ hk₀3
    hk₀Q
  have hexp' : ∀ x : ↥Y ⧸ CFSG.pCore 2 ↥Y, x ^ 3 = 1 := fun x => by
    rw [← hexp]
    exact Monoid.pow_exponent_eq_one x
  have hcyc : IsCyclic (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    by_contra hnc
    have := two_le_pRank_of_not_isCyclic hexp' hnc
    omega
  have hQ3 : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 3 := by
    rw [← IsCyclic.exponent_eq_card, hexp]
  have hZW : quasithinOmegaOneCenter T ≤ W := by
    refine (closure_le _).mpr fun z hz => omegaOneCenterOf_le_nqSourceModule Y R ?_
    obtain ⟨hzTC, hz2⟩ := hz
    obtain ⟨hzT, hzC⟩ := mem_inf.mp hzTC
    have hzO : z ∈ pCoreOf 2 H :=
      hHc ⟨hTH hzT, centralizer_le (hOHR.trans hRT) hzC⟩
    exact subset_omegaOneCenterOf (hOHR hzO) (centralizer_le hRT hzC) hz2
  have hne : ¬ Y ≤ centralizer (W : Set G) := fun hYW =>
    hYM ((hYW.trans (centralizer_le hZW)).trans h.centralizer_le)
  have hqY : (pCoreOf 2 Y).relIndex Y = 3 := by
    have e : (pCoreOf 2 Y).subgroupOf Y = CFSG.pCore 2 ↥Y := by
      ext y
      rw [mem_subgroupOf, mem_pCore_iff_mem_pCoreOf]
    rw [Subgroup.relIndex, e]
    exact hQ3
  have hdvd : (centralizer (W : Set G)).relIndex Y ∣ 3 := by
    rw [← hqY]
    exact Subgroup.relIndex_dvd_of_le_left Y ((hOYH.trans hOHS).trans hOW)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
  · exact absurd (Subgroup.relIndex_eq_one.mp h1) hne
  · exact h1

theorem solvableSourceRankBudget_holds : SolvableSourceRankBudget :=
  solvableSourceRankBudget_of normalSourceWholeActionOdd_holds

end CFSG.Quasithin.H13.NQBlock
