module

public import CFSG.Quasithin.MS93.C134L32CorrMOne
public import CFSG.Quasithin.EmptyFaithful.S151TCHat
public import CFSG.Quasithin.EmptyFaithful.S151TCMS
public import CFSG.Quasithin.EmptyFaithful.S151TCNorm
public import CFSG.Quasithin.EmptyFaithful.SmithL3ResMain
public import CFSG.Quasithin.EmptyFaithful.S151TCSL3
public import CFSG.Quasithin.H13.GoldschmidtC137L32Red
public import CFSG.Quasithin.H13.GoldschmidtC137L32ZGen
public import CFSG.Quasithin.H13.GoldschmidtC137L32ZPerf

public section

namespace CFSG.Quasithin.S151TC

section Case

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.S151TB

variable {G : Type} [Group G] [Finite G]

theorem c134_exists_case_corrM (hM : C134L32CorrM) {L R H : Subgroup G} (hL : L ∈ cComp H)
    (hRN : R ≤ Subgroup.normalizer (L : Set G)) (hms : IsMSPair (L ⊔ R) R)
    (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))) (hα : IsModO2Surj L α) :
    ∃ i : ℕ, IsC134CaseM i (L ⊔ R) R L :=
  hM G (L ⊔ R) R L hms (mem_cComp_sup_of_normalizer hL hRN)
    (Subgroup.coe_mul_of_right_le_normalizer_left L R hRN)
    ⟨ZMod 2, inferInstance, inferInstance, α, ZMod.card 2, hα⟩

end Case

end CFSG.Quasithin.S151TC

namespace CFSG.Quasithin.SmithL3Res

section Module

open Subgroup CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.L3
  CFSG.Quasithin.H13.U3.GC137 CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL

variable {G : Type} [Group G]

theorem exists_module_of_case_corrM {G₀ R L : Subgroup G} {i : ℕ}
    (hi : IsC134CaseM i G₀ R L)
    (hi2 : 2 ≤ i) (hi4 : i ≤ 4) (hLN : L ≤ normalizer ((pCoreOf 2 G₀ : Subgroup G) : Set G))
    (hperf : Group.IsPerfect ↥L) :
    ∃ (M : Subgroup G) (F : Type) (_ : Field F) (_ : Fintype F)
      (α : ↥L →* ↥(StatedSL 3 F)) (j : ℕ), IsModO2Surj L α ∧ (j = 1 ∨ j = 2) ∧
      IsSumOfNaturalModulesVia L M ⊥ α false j ∧
      ∀ z : G, z ∈ pCoreOf 2 G₀ → (∀ n ∈ pCoreOf 2 G₀, n * z = z * n) →
        ∀ k ∈ L, k * z * k⁻¹ * z⁻¹ ∈ M := by
  have D : ∀ z : G, z ∈ pCoreOf 2 G₀ → (∀ n ∈ pCoreOf 2 G₀, n * z = z * n) →
      ZFacts L (pCoreOf 2 G₀) ⊥ 1 z := fun z hzN hzC =>
    ⟨hLN, hperf, hzN, hzC, bot_le, fun n _ w hw => by
      rw [Subgroup.mem_bot.1 hw, one_mul, mul_one], Subgroup.commutator_bot_left L,
      Subgroup.one_mem _⟩
  obtain rfl | rfl | rfl : i = 2 ∨ i = 3 ∨ i = 4 := by omega
  · obtain ⟨⟨_, F, hF, hFi, α, -, hα, hM⟩, -⟩ := hi
    exact ⟨c134Q G₀ L, F, hF, hFi, α, 2, hα, Or.inr rfl, hM,
      fun z hzN hzC => (D z hzN hzC).hcQ⟩
  · obtain ⟨⟨_, F, hF, hFi, α, -, hα, hM, -⟩, -⟩ := hi
    exact ⟨centerOf (c134Q G₀ L), F, hF, hFi, α, 1, hα, Or.inl rfl, hM,
      fun z hzN hzC => (D z hzN hzC).hcZ⟩
  · obtain ⟨⟨_, F, hF, hFi, α, -, hα, -, -, hU, -, -⟩, -⟩ := hi
    exact ⟨⁅centerOf (c134Q G₀ L), L⁆, F, hF, hFi, α, 1, hα, Or.inl rfl, hU,
      fun z hzN hzC => cocycle_mem_commutator_of_perfect (D z hzN hzC).hLZ
        (centerOf_comm_gc _) hperf (D z hzN hzC).hcZ⟩

end Module

section Sylow

open Subgroup CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.S151TB CFSG.Quasithin.H13.U3.GC137 CFSG.LieType.BorelTits
open CFSG.Open hiding StatedSL
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_q1_eq_corrM {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hcomp : L ∈ cComp (g1_1516 Z₁))
    (hL3 : IsPSL 3 2 1 (LStar L ⧸ Subgroup.center (LStar L)))
    (hRN : q1_1516 Mc Z₁ ≤ Subgroup.normalizer (L : Set G))
    (hg : S151TC.C27CaseG L (q1_1516 Mc Z₁) (mZ1516 Mc Z₁)) {i : ℕ}
    (hi : IsC134CaseM i (L ⊔ q1_1516 Mc Z₁) (q1_1516 Mc Z₁) L) (hi2 : 2 ≤ i) (hi4 : i ≤ 4) :
    ∃ S' : Subgroup G, IsSylowTwoOf S' (L ⊔ q1_1516 Mc Z₁) ∧ q1_1516 Mc Z₁ ≤ S' ∧
      q1_1516 Mc Z₁ = pCoreOf 2 ((L ⊔ q1_1516 Mc Z₁) ⊓
        Subgroup.centralizer (omegaOneCenterOf S' : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLG₁ : L ≤ g1_1516 Z₁ := le_of_mem_cComp hcomp
  have hQMZ : q1_1516 Mc Z₁ ≤ mZ1516 Mc Z₁ := q1_1516_le Mc Z₁
  have hMZG₁ : mZ1516 Mc Z₁ ≤ g1_1516 Z₁ := mZ1516_le_g1 Mc Z₁
  have hG₀G₁ : L ⊔ q1_1516 Mc Z₁ ≤ g1_1516 Z₁ := sup_le hLG₁ (hQMZ.trans hMZG₁)
  have hSG₁ : IsSylowTwoOf (s1516 T Z₁) (g1_1516 Z₁) := hc.h18.four
  obtain ⟨⟨z₀, hz₀Z⟩, hz₀1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).mp hc.ctx.qtfe.omegaOneCenter_ne_bot
  have hz₀ne : z₀ ≠ 1 := fun h => hz₀1 (Subtype.ext h)
  have h115 := hc.h18.six z₀ hz₀Z hz₀ne
  have hSMZ : s1516 T Z₁ ≤ mZ1516 Mc Z₁ := le_inf (s1516_le_g1 T Z₁) h115.le
  have hQS : q1_1516 Mc Z₁ ≤ s1516 T Z₁ :=
    pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le_of_le' hSG₁ hSMZ hMZG₁)
  have hz₀Q : z₀ ∈ q1_1516 Mc Z₁ :=
    h115.charTwo_inf ⟨hSMZ h115.z_mem, Subgroup.centralizer_le hQS h115.z_central⟩
  set Q := q1_1516 Mc Z₁ with hQdef
  set G₀ := L ⊔ Q with hG₀def
  set S' := s1516 T Z₁ ⊓ G₀ with hS'def
  have hG₀N : G₀ ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hRN
  have hSL : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hcomp) hSG₁
  have hS'L : S' ⊓ L = s1516 T Z₁ ⊓ L := by
    rw [hS'def, inf_assoc, inf_eq_right.mpr (le_sup_left : L ≤ G₀)]
  have hQS' : Q ≤ S' := le_inf hQS le_sup_right
  have hLS' : L ⊔ S' = G₀ :=
    le_antisymm (sup_le le_sup_left inf_le_right) (sup_le le_sup_left (hQS'.trans le_sup_right))
  have hS'syl : IsSylowTwoOf S' G₀ := by
    have h := isSylowTwoOf_sup_of_inf (inf_le_right.trans hG₀N) (hSG₁.2.1.to_le inf_le_left)
      (by rw [hS'L]; exact hSL)
    rwa [hLS'] at h
  have hz₀S' : z₀ ∈ omegaOneCenterOf S' :=
    Subgroup.subset_closure ⟨⟨⟨h115.z_mem, (le_sup_right : Q ≤ G₀) hz₀Q⟩,
      Subgroup.centralizer_le inf_le_left h115.z_central⟩, h115.z_sq⟩
  have hcz₀ : ∀ x ∈ Subgroup.centralizer (omegaOneCenterOf S' : Set G),
      x ∈ Subgroup.centralizer ({z₀} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact Subgroup.mem_centralizer_iff.1 hx z₀ hz₀S'
  have hPN₀ : G₀ ⊓ Subgroup.centralizer (omegaOneCenterOf S' : Set G) ≤ G₀ ⊓ mZ1516 Mc Z₁ :=
    fun x hx => ⟨hx.1, hG₀G₁ hx.1, h115.centralizer_z_le (hcz₀ x hx.2)⟩
  have hperf : Group.IsPerfect ↥L := isPerfect_of_commutator_eq_gc (perfect_of_mem_cComp hcomp)
  have hLN : L ≤ Subgroup.normalizer ((pCoreOf 2 G₀ : Subgroup G) : Set G) :=
    (le_sup_left : L ≤ G₀).trans (le_normalizer_pCoreOf 2 G₀)
  obtain ⟨Mm, F, _, _, α, j, hα, hj, hM, hcomm⟩ := exists_module_of_case_corrM hi hi2 hi4 hLN hperf
  have hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 :=
    S151TC.card_lStar_of_psl32 hc.hL.quasi hL3
  obtain ⟨K, -, hKL, hKmax, hKz⟩ := exists_pointStab hcard hα hj hM hSL
  have hNS' : pCoreOf 2 G₀ ≤ S' := pCoreOf_two_le_of_isSylowTwoOf hS'syl
  have hchG₀ : CharTwo G₀ := hg.2.2.1.2.1
  have hKC : K ≤ Subgroup.centralizer (omegaOneCenterOf S' : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzc := mem_centerOf_of_mem_omegaOneCenterOf hz
    have hzC : ∀ n ∈ pCoreOf 2 G₀, n * z = z * n := fun n hn =>
      Subgroup.mem_centralizer_iff.1 hzc.2 n (hNS' hn)
    have hzN : z ∈ pCoreOf 2 G₀ := hchG₀ ⟨hS'syl.1 hzc.1, Subgroup.mem_centralizer_iff.2 hzC⟩
    have hzSL : ∀ p ∈ s1516 T Z₁ ⊓ L, p * z = z * p := fun p hp =>
      Subgroup.mem_centralizer_iff.1 hzc.2 p ⟨hp.1, (le_sup_left : L ≤ G₀) hp.2⟩
    exact (hKz z hzSL (hcomm z hzN hzC) k hk).symm
  have hKMZ : K ≤ mZ1516 Mc Z₁ ⊓ L := fun k hk =>
    ⟨⟨hLG₁ (hKL hk), h115.centralizer_z_le (hcz₀ k (hKC hk))⟩, hKL hk⟩
  have hMLK : mZ1516 Mc Z₁ ⊓ L ≤ K := hKmax _ hKMZ inf_le_right fun h =>
    hc.hL.not_le (h.symm.le.trans inf_le_left)
  have hN₀P : G₀ ⊓ mZ1516 Mc Z₁ ≤ G₀ ⊓ Subgroup.centralizer (omegaOneCenterOf S' : Set G) := by
    intro g hg'
    refine ⟨hg'.1, ?_⟩
    have hgLQ : g ∈ (L : Set G) * (Q : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left L Q hRN]
      exact hg'.1
    obtain ⟨l, hl, q, hq, rfl⟩ := hgLQ
    have hlMZ : l ∈ mZ1516 Mc Z₁ := by
      have := (mZ1516 Mc Z₁).mul_mem hg'.2 ((mZ1516 Mc Z₁).inv_mem (hQMZ hq))
      simpa using this
    have hqC : q ∈ Subgroup.centralizer (omegaOneCenterOf S' : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (Subgroup.mem_centralizer_iff.1 (mem_centerOf_of_mem_omegaOneCenterOf hz).2 q
        (hQS' hq)).symm
    exact Subgroup.mul_mem _ (hKC (hMLK ⟨hlMZ, hl⟩)) hqC
  have hQN₀ : Q ≤ G₀ ⊓ mZ1516 Mc Z₁ := le_inf le_sup_right hQMZ
  have h1 : Q ≤ pCoreOf 2 (G₀ ⊓ mZ1516 Mc Z₁) :=
    le_pCoreOf_of_le_normalizer 2 hQN₀ (inf_le_right.trans (le_normalizer_pCoreOf 2 _))
      (pCoreOf_isPGroup 2 _)
  have hG2 : ¬ IsG2Two (↥G₀ ⧸ CFSG.pCore 2 ↥G₀) :=
    not_isG2Two_quot hcard hRN (pCoreOf_isPGroup 2 _)
  have h2 : pCoreOf 2 (G₀ ⊓ mZ1516 Mc Z₁) ≤ Q :=
    pCoreOf_le_of_msPair hg.2.2 hG2 inf_le_left fun x hx =>
      ⟨hx.1, hc.h18.five.2.1.ge ⟨hG₀G₁ hx.1, hx.2⟩⟩
  refine ⟨S', hS'syl, hQS', ?_⟩
  rw [le_antisymm hPN₀ hN₀P]
  exact le_antisymm h1 h2

end Sylow

end CFSG.Quasithin.SmithL3Res

namespace CFSG.Quasithin.S151TC

section Block

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.Quasithin.S151TB

structure L3ResCorr : Prop where
  noCase2 : ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L → L ∈ cComp (g1_1516 Z₁) →
    IsPSL 3 2 1 (LStar L ⧸ Subgroup.center (LStar L)) →
    q1_1516 Mc Z₁ ≤ Subgroup.normalizer (L : Set G) →
    C27CaseG L (q1_1516 Mc Z₁) (mZ1516 Mc Z₁) →
    ¬ MS93.IsC134CaseCorr 2 (L ⊔ q1_1516 Mc Z₁) (q1_1516 Mc Z₁) L
  noCase3 : ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L → L ∈ cComp (g1_1516 Z₁) →
    IsPSL 3 2 1 (LStar L ⧸ Subgroup.center (LStar L)) →
    q1_1516 Mc Z₁ ≤ Subgroup.normalizer (L : Set G) →
    C27CaseG L (q1_1516 Mc Z₁) (mZ1516 Mc Z₁) →
    ¬ MS93.IsC134CaseCorr 3 (L ⊔ q1_1516 Mc Z₁) (q1_1516 Mc Z₁) L
  noCase4 : ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L → L ∈ cComp (g1_1516 Z₁) →
    IsPSL 3 2 1 (LStar L ⧸ Subgroup.center (LStar L)) →
    q1_1516 Mc Z₁ ≤ Subgroup.normalizer (L : Set G) →
    C27CaseG L (q1_1516 Mc Z₁) (mZ1516 Mc Z₁) →
    ¬ MS93.IsC134CaseCorr 4 (L ⊔ q1_1516 Mc Z₁) (q1_1516 Mc Z₁) L

structure L3ResCorrM : Prop where
  noCase2 : ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L → L ∈ cComp (g1_1516 Z₁) →
    IsPSL 3 2 1 (LStar L ⧸ Subgroup.center (LStar L)) →
    q1_1516 Mc Z₁ ≤ Subgroup.normalizer (L : Set G) →
    C27CaseG L (q1_1516 Mc Z₁) (mZ1516 Mc Z₁) →
    ¬ IsC134CaseM 2 (L ⊔ q1_1516 Mc Z₁) (q1_1516 Mc Z₁) L
  noCase3 : ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L → L ∈ cComp (g1_1516 Z₁) →
    IsPSL 3 2 1 (LStar L ⧸ Subgroup.center (LStar L)) →
    q1_1516 Mc Z₁ ≤ Subgroup.normalizer (L : Set G) →
    C27CaseG L (q1_1516 Mc Z₁) (mZ1516 Mc Z₁) →
    ¬ IsC134CaseM 3 (L ⊔ q1_1516 Mc Z₁) (q1_1516 Mc Z₁) L
  noCase4 : ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L → L ∈ cComp (g1_1516 Z₁) →
    IsPSL 3 2 1 (LStar L ⧸ Subgroup.center (LStar L)) →
    q1_1516 Mc Z₁ ≤ Subgroup.normalizer (L : Set G) →
    C27CaseG L (q1_1516 Mc Z₁) (mZ1516 Mc Z₁) →
    ¬ IsC134CaseM 4 (L ⊔ q1_1516 Mc Z₁) (q1_1516 Mc Z₁) L

theorem L3ResCorrM.toCorr (h : L3ResCorrM) : L3ResCorr where
  noCase2 G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hcomp hL3 hRN hg hi :=
    h.noCase2 G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hcomp hL3 hRN hg
      (hi.toCaseM)
  noCase3 G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hcomp hL3 hRN hg hi :=
    h.noCase3 G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hcomp hL3 hRN hg
      (hi.toCaseM)
  noCase4 G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hcomp hL3 hRN hg hi :=
    h.noCase4 G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hcomp hL3 hRN hg
      (hi.toCaseM)

theorem l3ResCorrM_holds : L3ResCorrM := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc _ hcomp hL3 hRN hg hi
    obtain ⟨S', hS', hQS', heq⟩ :=
      SmithL3Res.exists_sylow_q1_eq_corrM hc hcomp hL3 hRN hg hi (by norm_num) (by norm_num)
    exact hi.2 S' hS' hQS' heq

theorem input15120L3Block_of_res_corrM (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hM : C134L32CorrM) (hres : L3ResCorrM) : S151TB.Input15120L3Block := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hcomp hL3
  have hq : CFSG.IsQuasisimple (LStar L) := hc.hL.quasi
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hcomp
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hcomp
  have hRN : q1_1516 Mc Z₁ ≤ Subgroup.normalizer (L : Set G) := by
    have hqf := hc.ctx.qtfe
    rcases lemma_1_2_1_three hqf.qtke hqf.simple hqf.nonabelian h37 h38
        (hc.ctx.setting.pCore_g1_ne_bot hqf hc.ctx.mf) hcomp with hn | ⟨hn2, -⟩
    · exact (q1_1516_le Mc Z₁).trans ((mZ1516_le_g1 Mc Z₁).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mp hn))
    · by_cases hn : (L.subgroupOf (g1_1516 Z₁)).Normal
      · exact (q1_1516_le Mc Z₁).trans ((mZ1516_le_g1 Mc Z₁).trans
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mp hn))
      · exact q1_le_normalizer_of_nonnormal h37 hC129 hc hchar hcomp hL3 hn2
  have hcard : Nat.card (LStar L) = 168 := card_lStar_of_psl32 hq hL3
  obtain ⟨α, hαs, hαk⟩ := exists_epi_sl3_two hq hL3
  have hg : C27CaseG L (q1_1516 Mc Z₁) (mZ1516 Mc Z₁) :=
    c27_g_of_card168 (hC27 G) hc.h18.five.2.2 hcomp hq hchar hc.hL.not_le hRN hcard
  obtain ⟨i, hi⟩ := c134_exists_case_corrM hM hcomp hRN hg.2.2 α ⟨hαs, hαk⟩
  match i, hi with
  | 1, hi => exact isLnBlock_three_of_isSL3Block hi.1 hcard
  | 2, hi => exact (hres.noCase2 G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hcomp hL3 hRN hg hi).elim
  | 3, hi => exact (hres.noCase3 G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hcomp hL3 hRN hg hi).elim
  | 4, hi => exact (hres.noCase4 G T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hcomp hL3 hRN hg hi).elim
  | 5, hi => exact isLnBlock_three_of_case5 hperf hchar hq hRN (commutator_ne_bot_of_caseG hg) hi.1
  | 0, hi => exact hi.elim
  | n + 6, hi => exact hi.elim

theorem input15120TwoBRes_of_res_corrM
    (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G) (hM : C134L32CorrM)
    (hres : L3ResCorrM) : S151TB.Input15120TwoBRes :=
  ⟨input15120NoHatA6_holds h37 h38 hC27, input15120L3Block_of_res_corrM h37 h38 hC27 hC129 hM hres⟩

theorem input15120TwoB_of_l3res_corrM
    (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G) (hM : C134L32CorrM)
    (hres : L3ResCorrM) : Input15120TwoB :=
  S151TB.input15120TwoB_of_res h37 h38 hC27
    (input15120TwoBRes_of_res_corrM h37 h38 hC27 hC129 hM hres)

end Block

end CFSG.Quasithin.S151TC

namespace CFSG.Quasithin.S151TC

theorem l3ResCorr_holds : L3ResCorr :=
  L3ResCorrM.toCorr l3ResCorrM_holds

end CFSG.Quasithin.S151TC
