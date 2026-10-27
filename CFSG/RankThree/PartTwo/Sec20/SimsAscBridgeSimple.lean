module

public import CFSG.RankThree.PartTwo.Sec20.OneSteps
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
import CFSG.RankThree.OddKernel.RankOneQuotients
import CFSG.LocalAnalysis.SectionRank.TwoGenerators
import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.RankThree.PartTwo.Sec20.OneTools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open scoped Pointwise

namespace AscBridge

variable {G : Type} [Group G] [Finite G]

theorem mem_of_normal_of_three_dvd_card {H : Type*} [Group H] [Finite H]
    (hH : CFSG.pRank 3 H ≤ 1) {a : H} (ha : orderOf a = 3) (N : Subgroup H) [hN : N.Normal]
    (h3 : 3 ∣ Nat.card N) : a ∈ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha3 : IsPGroup 3 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  obtain ⟨P, haP⟩ := ha3.exists_le_sylow
  have hPcyc : IsCyclic (P : Subgroup H) :=
    ((CFSG.LocalAnalysis.ComponentInitial.pgroup_rank_one_classification Nat.prime_three
      P.isPGroup').1 ((CFSG.SectionRank.pRank_sylow P).2 ▸ hH)).resolve_right
      fun h => absurd h.1 (by norm_num)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := N) 3 h3
  have hwH : orderOf (w : H) = 3 := by rw [Subgroup.orderOf_coe, hw]
  have hw3 : IsPGroup 3 (Subgroup.zpowers (w : H)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hwH, pow_one])
  obtain ⟨Q, hwQ⟩ := hw3.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q P
  have hzP : g * (w : H) * g⁻¹ ∈ (P : Subgroup H) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ (hwQ (Subgroup.mem_zpowers _))
  have hzN : g * (w : H) * g⁻¹ ∈ N := hN.conj_mem _ w.2 g
  have hz1 : g * (w : H) * g⁻¹ ≠ 1 := by
    rw [Ne, conj_eq_one_iff]
    intro h
    rw [h, orderOf_one] at hwH
    omega
  have hz3 : (g * (w : H) * g⁻¹) ^ 3 = 1 := by
    rw [conj_pow, ← hwH, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  haveI := hPcyc
  have hcomm : Commute (g * (w : H) * g⁻¹) a :=
    congrArg Subtype.val
      (mul_comm' (⟨_, hzP⟩ : (P : Subgroup H)) ⟨a, haP (Subgroup.mem_zpowers a)⟩)
  by_contra haN
  have hy : ∀ n : ℕ, (g * (w : H) * g⁻¹) ^ n ≠ a := fun n h => haN (h ▸ N.pow_mem hzN n)
  have h2 := CFSG.SectionRank.two_le_pRank_top_of_commute (p := 3) hz3
    (by rw [← ha]; exact pow_orderOf_eq_one a) hcomm hz1 hy
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
  omega

theorem pPrimeCore_eq_bot_of_normal_of_eq_bot {Γ : Type*} [Group Γ] [Finite Γ]
    (hΓ : CFSG.pPrimeCore 3 Γ = ⊥) (Yb : Subgroup Γ) [Yb.Normal] :
    CFSG.pPrimeCore 3 ↥Yb = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : (CFSG.pPrimeCore 3 ↥Yb).map Yb.subtype ≤ CFSG.pPrimeCore 3 Γ := by
    refine le_sSup ⟨inferInstance, ?_⟩
    rw [Subgroup.card_map_of_injective Yb.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  rwa [hΓ, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ Yb.subtype_injective] at hle

theorem isSimpleGroup_of_pRank_three_le_one {H : Type*} [Group H] [Finite H]
    (hH : CFSG.pRank 3 H ≤ 1) (hO : CFSG.pPrimeCore 3 H = ⊥) {a : H} (ha : orderOf a = 3)
    (hgen : ∀ N : Subgroup H, N.Normal → a ∈ N → N = ⊤) : IsSimpleGroup H := by
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha
    omega
  refine { exists_pair_ne := ⟨a, 1, ha1⟩, eq_bot_or_eq_top_of_normal := fun N hN => ?_ }
  by_cases h3 : 3 ∣ Nat.card N
  · exact Or.inr (hgen N hN (mem_of_normal_of_three_dvd_card hH ha N h3))
  · exact Or.inl (CFSG.pPrimeCore_eq_bot_iff.mp hO N hN
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))

omit [Finite G] in
theorem eq_top_of_le_normalClosureIn {H : Type*} [Group H] {Y : Subgroup G} {c : G}
    (hc : c ∈ Y) (hY : Y ≤ normalClosureIn Y c) (φ : ↥Y →* H) (hφ : Function.Surjective φ)
    (N : Subgroup H) [hN : N.Normal] (hcN : φ ⟨c, hc⟩ ∈ N) : N = ⊤ := by
  have hle : normalClosureIn Y c ≤ (N.comap φ).map Y.subtype := by
    rw [normalClosureIn, Subgroup.closure_le]
    rintro _ ⟨m, hm, rfl⟩
    refine ⟨⟨m, hm⟩ * ⟨c, hc⟩ * ⟨m, hm⟩⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hN.conj_mem _ hcN _
  rw [eq_top_iff]
  intro u _
  obtain ⟨y, rfl⟩ := hφ u
  obtain ⟨y', hy', hyy'⟩ := hle (hY y.2)
  rw [← Subtype.ext hyy']
  exact hy'

theorem exists_mul_ne_mul_of_isPerfect {K H : Type*} [Group K] [Group H] [Group.IsPerfect K]
    (ψ : K →* H) {k : K} (hk : ψ k ≠ 1) : ∃ a b : H, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  haveI : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
  haveI : IsMulCommutative ψ.range := ⟨⟨fun x y => Subtype.ext (hcomm x y)⟩⟩
  haveI : Subsingleton ψ.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  exact hk (congrArg Subtype.val (Subsingleton.elim (⟨ψ k, k, rfl⟩ : ψ.range) 1))

section Simple

variable {A M L N : Subgroup G} {c : G} {T : Subgroup G} {i j : Fin 4} {P X : Subgroup G}

private theorem yAlpha_facts (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    (hm : CFSG.Open.pRank 3 (yTwenty X c) ≤ 1) :
    CFSG.pRank 3 ↥(yAlpha M X T c) ≤ 1 ∧ CFSG.pPrimeCore 3 ↥(yAlpha M X T c) = ⊥ ∧
      ∃ a : ↥(yAlpha M X T c), orderOf a = 3 ∧
        (∀ N₁ : Subgroup ↥(yAlpha M X T c), N₁.Normal → a ∈ N₁ → N₁ = ⊤) ∧
        ∃ x y : ↥(yAlpha M X T c), x * y ≠ y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := kTwenty M c with hKdef
  set R := CFSG.Open.pCoreOf 2 (K ⊔ T) with hRdef
  set Y := yTwenty X c with hYdef
  set YR := Y ⊔ R with hYRdef
  haveI := CFSG.pPrimeCore_normal (p := 3) (G := ↥YR)
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥YR) with hπ
  set Yb := yAlpha M X T c with hYbdef
  have hKTX : K ⊔ T ≤ X := fun x hx => hX.2 hx
  have hKX : K ≤ X := le_sup_left.trans hKTX
  have hKY : K ≤ Y := Res6.kTwenty_le_yTwenty hset hKX
  have hRY : R ≤ Subgroup.normalizer (Y : Set G) :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKTX).trans
      (le_normalizer_normalClosureIn X c)
  have hYRY : YR ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hRY
  have hYn : (Y.subgroupOf YR).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hYRY
  haveI hYbn : Yb.Normal := hYn.map π (QuotientGroup.mk'_surjective _)
  let φ : ↥Y →* ↥Yb := (π.comp (Subgroup.inclusion (le_sup_left : Y ≤ YR))).codRestrict Yb
    fun y => ⟨Subgroup.inclusion le_sup_left y, y.2, rfl⟩
  have hφs : Function.Surjective φ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hc3 := Res6.orderOf_c_of_setting204 hset
  have hcY : c ∈ Y := self_mem_normalClosureIn X c
  have hcYR : c ∈ YR := (le_sup_left : Y ≤ YR) hcY
  have ha3 : orderOf (φ ⟨c, hcY⟩) = 3 := by
    have h1 : φ ⟨c, hcY⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨c, hcY⟩ : ↥Y) ^ 3 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, ← hc3, pow_orderOf_eq_one])
      rw [this, map_one]
    refine orderOf_eq_prime h1 fun h => ?_
    have h' : π ⟨c, hcYR⟩ = 1 := congrArg Subtype.val h
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h'
    have hdvd : orderOf (⟨c, hcYR⟩ : ↥YR) ∣ Nat.card (CFSG.pPrimeCore 3 ↥YR) := by
      rw [← Subgroup.orderOf_mk _ h']
      exact orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hc3] at hdvd
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card hdvd
  refine ⟨CFSG.RankThree.OddKernel.pRank_le_one_of_surjective Nat.prime_three (by norm_num) φ
      hφs (by rw [CFSG.SectionRank.pRank_coe_eq_openPRank]; exact hm),
    pPrimeCore_eq_bot_of_normal_of_eq_bot (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3) Yb,
    φ ⟨c, hcY⟩, ha3, fun N₁ _ hN₁ => eq_top_of_le_normalClosureIn hcY
      (Res6.yTwenty_le_normalClosureIn_self hset X) φ hφs N₁ hN₁, ?_⟩
  haveI : Group.IsPerfect ↥K := isPerfect_of_mem_oTwoComponentsIn hset.mem_oTwoComponentsIn
  have hcK : c ∈ K := self_mem_normalClosureIn M c
  refine exists_mul_ne_mul_of_isPerfect (φ.comp (Subgroup.inclusion hKY)) (k := ⟨c, hcK⟩)
    fun h => ?_
  have h' : φ ⟨c, hcY⟩ = 1 := h
  rw [h', orderOf_one] at ha3
  omega

theorem isSimpleGroup_yAlpha {A M L N : Subgroup G} {c : G} {T : Subgroup G} {i j : Fin 4}
    {P X : Subgroup G} (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    (hm : CFSG.Open.pRank 3 (yTwenty X c) ≤ 1) :
    IsSimpleGroup ↥(yAlpha M X T c) ∧ ∃ a b : ↥(yAlpha M X T c), a * b ≠ b * a := by
  obtain ⟨hrk, hO, a, ha, hgen, hnab⟩ := yAlpha_facts hset hX hm
  exact ⟨isSimpleGroup_of_pRank_three_le_one hrk hO ha hgen, hnab⟩

theorem pRank_yAlpha_eq_one {A M L N : Subgroup G} {c : G} {T : Subgroup G} {i j : Fin 4}
    {P X : Subgroup G} (hset : Setting204 G A M L N c T i j P)
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    (hm : CFSG.Open.pRank 3 (yTwenty X c) ≤ 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥(yAlpha M X T c)) = 1 := by
  obtain ⟨hrk, -, a, ha, -, -⟩ := yAlpha_facts hset hX hm
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hrk
  have ha3 : a ^ 3 = 1 := by
    have h := pow_orderOf_eq_one a
    rwa [ha] at h
  refine le_antisymm hrk (CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_top
    (E := Subgroup.zpowers a) ⟨⟨⟨fun x y => ?_⟩⟩, fun y hy => ?_⟩
    (by rw [Nat.card_zpowers, ha, pow_one]))
  · obtain ⟨x, i, rfl⟩ := x
    obtain ⟨y, j, rfl⟩ := y
    exact Subtype.ext (Commute.zpow_zpow_self a i j).eq
  · obtain ⟨i, rfl⟩ := hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]

end Simple

end AscBridge

end CFSG.RankThree.PartTwo.Sec20
