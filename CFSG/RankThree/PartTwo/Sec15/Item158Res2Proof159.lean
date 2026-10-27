module

public import CFSG.RankThree.PartTwo.Sec15.Item158StepsProof159
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.RankThree.PartTwo.Sec14.Item1411Strong
public import CFSG.RankThree.PartTwo.Sec14.Item146General

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

@[expose] noncomputable def Step159ClaimK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx159 G A c L → ∀ w : G, IsW159 A L w → ∀ V ∈ scriptY3 A (lB A),
      w ∈ Subgroup.normalizer (V : Set G) → oPrimeResidualOf 3 V ≠ ⊥ →
        ∃ K ∈ scriptY0Star A (lB A), w ∈ Subgroup.normalizer (K : Set G) ∧
          ∃ F ∈ omegaA A, (F : Set G) = Late.sectionCentralizer A K (CFSG.Open.pCoreOf 2 K)

@[expose] noncomputable def Step159WT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx159 G A c L → ∃ w : G, IsW159 A L w ∧
      ∃ T ∈ scriptQPi A (lB A) ⊤ (piOf 2), T ≠ ⊥ ∧ w ∈ Subgroup.normalizer (T : Set G)

namespace Proof159Res2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commute_of_conj_mem_zpowers {c x : G} (hc : orderOf c = 3) {k : ℕ} (hx : x ^ 3 ^ k = 1)
    (hxc : x * c * x⁻¹ ∈ Subgroup.zpowers c) : x * c = c * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ, x * c * x⁻¹ = c ^ j := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hxc
    exact ⟨j, hj.symm⟩
  have hit : ∀ n : ℕ, x ^ n * c * (x ^ n)⁻¹ = c ^ (j ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc x ^ (n + 1) * c * (x ^ (n + 1))⁻¹ = x * (x ^ n * c * (x ^ n)⁻¹) * x⁻¹ := by group
        _ = x * c ^ (j ^ n) * x⁻¹ := by rw [ih]
        _ = (x * c * x⁻¹) ^ (j ^ n) := conj_zpow.symm
        _ = c ^ (j ^ (n + 1)) := by rw [hj, ← zpow_mul, pow_succ, mul_comm]
  have h1 : c ^ (j ^ 3 ^ k - 1) = 1 := by
    have := hit (3 ^ k)
    rw [hx] at this
    rw [zpow_sub, zpow_one, ← this]
    simp
  have h2 : ((3 : ℕ) : ℤ) ∣ j ^ 3 ^ k - 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rwa [hc] at this
  have h3 : ((3 : ℕ) : ℤ) ∣ j - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h2 ⊢
    push_cast at h2 ⊢
    rwa [ZMod.pow_card_pow] at h2
  obtain ⟨t, ht⟩ := h3
  have hc3 : c ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat, ← hc]
    exact pow_orderOf_eq_one c
  have hcj : c ^ j = c := by
    rw [show j = 3 * t + 1 by push_cast at ht; omega, zpow_add, zpow_mul, hc3, one_zpow,
      one_mul, zpow_one]
  rw [hcj] at hj
  calc x * c = x * c * x⁻¹ * x := by group
    _ = c * x := by rw [hj]

theorem delta_normalizer_mem_scriptY3 {A : Subgroup G} (hG : IsSimpleGroup G)
    (hA27 : Nat.card A = 27) {T : Subgroup G} (hTQ : T ∈ scriptQ A (lB A)) (hT2 : IsPGroup 2 T)
    (hT1 : T ≠ ⊥) :
    delta A (lB A) (Subgroup.normalizer (T : Set G)) ∈ scriptY3 A (lB A) ∧
      T ≤ delta A (lB A) (Subgroup.normalizer (T : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTV : T ≤ delta A (lB A) (Subgroup.normalizer (T : Set G)) :=
    le_delta hTQ Subgroup.le_normalizer
  have hVN : delta A (lB A) (Subgroup.normalizer (T : Set G)) ≤ Subgroup.normalizer (T : Set G) :=
    delta_le _
  have hNtop : Subgroup.normalizer (T : Set G) ≠ ⊤ := by
    intro htop
    have hTn : T.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hG.eq_bot_or_eq_top_of_normal T with h | h
    · exact hT1 h
    · obtain ⟨n, hn⟩ := hT2.exists_card_eq
      have hdvd : Nat.card A ∣ Nat.card T := by
        rw [h]
        exact Subgroup.card_dvd_of_le le_top
      rw [hA27, hn] at hdvd
      have h3 : 3 ∣ 2 ^ n := dvd_trans (by norm_num) hdvd
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  refine ⟨⟨⟨⟨fun h => hNtop (eq_top_iff.mpr (h ▸ hVN)), le_normalizer_delta _⟩, ?_⟩,
    (delta_delta _).symm⟩, hTV⟩
  have hO2 : T ≤ CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.normalizer (T : Set G))) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hTV hVN hT2
  intro h0
  rw [h0, le_bot_iff] at hO2
  exact hT1 hO2

omit [Finite G] in
theorem isPGroup_zpowers {w : G} {k : ℕ} (hw : w ^ 3 ^ k = 1) :
    IsPGroup 3 (Subgroup.zpowers w) := by
  rintro ⟨y, hy⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine ⟨k, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw, one_zpow]

end Proof159Res2

open Proof159Res2 Proof159

theorem step159S_of (h146 : Item146R) : Step159S := by
  intro G _ _ A c L ctx w hw hcl hex
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := ctx.toSec15R
  have hD := h.toSec13Data
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  have h146' := h146 G A c L h
  obtain ⟨k, hwk⟩ := hw.2.1
  obtain ⟨V, ⟨hV, hwV⟩, hmax⟩ := Set.exists_max_image
    {V : Subgroup G | V ∈ scriptY3 A (lB A) ∧ w ∈ Subgroup.normalizer (V : Set G)}
    (fun V => (Nat.card V).factorization 2) (Set.toFinite _) hex
  have hV3 : ¬ 3 ∣ Nat.card V := not_three_dvd_of_oPrimeResidualOf_eq_bot (hcl V hV hwV)
  have hVQ : V ∈ scriptQ A (lB A) := by
    have hinv : V ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
      ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three V).mpr hV3, hV.1.1.2⟩
    have hΔ := delta_mem_scriptQ hA h146' hinv
    rwa [← hV.2] at hΔ
  set R := A ⊔ Subgroup.zpowers w with hRdef
  have hR3 : IsPGroup 3 R := IsPGroup.to_sup_of_normal_left' hA.isPGroup (isPGroup_zpowers hwk)
    (Subgroup.zpowers_le.mpr hw.1)
  have hRV : R ≤ Subgroup.normalizer (V : Set G) :=
    sup_le hV.1.1.2 (Subgroup.zpowers_le.mpr hwV)
  have hO2V : CFSG.Open.pCoreOf 2 V ≤ V := CFSG.LieType.BorelTits.pCoreOf_le 2 V
  obtain ⟨S, hS, hO2S, hRS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hR3 hV3 hRV hO2V
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) V)
    (hRV.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 V))
  have hSV : S ≤ V := hS.1
  have hS2 : IsPGroup 2 S := hS.2.1
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := le_sup_left.trans hRS
  have hwS : w ∈ Subgroup.normalizer (S : Set G) :=
    hRS (le_sup_right (a := A) (Subgroup.mem_zpowers w))
  have hS1 : S ≠ ⊥ := fun h0 => hV.1.2 (le_bot_iff.mp (h0 ▸ hO2S))
  have hSQ : S ∈ scriptQ A (lB A) := mem_scriptQ_of_le hVQ hSV hAS
  have hSmem : S ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
    ⟨⟨hSQ, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two S).mpr hS2⟩
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S V :=
    CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hS
  refine ⟨S, ⟨hSmem, fun T hT hST => ?_⟩, hwS⟩
  by_contra hTS
  have hne : S ≠ T := fun h => hTS (h ▸ le_rfl)
  have hT2 : IsPGroup 2 T := isPGroup_of_mem_scriptQPi Nat.prime_two hT
  have hlt := CFSG.Goldschmidt.G310.lt_inf_normalizer hT2 hST hne
  have hNQ : T ⊓ Subgroup.normalizer (S : Set G) ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hT.1.1 inf_le_left
      (Late.le_normalizer_inf hT.1.1.1.2.2 (hAS.trans Subgroup.le_normalizer))
  have hNV' : T ⊓ Subgroup.normalizer (S : Set G) ≤
      delta A (lB A) (Subgroup.normalizer (S : Set G)) := le_delta hNQ inf_le_right
  obtain ⟨hV'3, -⟩ := delta_normalizer_mem_scriptY3 h.isSimpleGroup hD.card_eq hSQ hS2 hS1
  have hwV' : w ∈ Subgroup.normalizer
      ((delta A (lB A) (Subgroup.normalizer (S : Set G)) : Subgroup G) : Set G) :=
    mem_normalizer_delta hw.1 (Subgroup.le_normalizer hwS)
  have hle := hmax _ ⟨hV'3, hwV'⟩
  obtain ⟨a, ha⟩ :=
    (hT2.to_le (inf_le_left : T ⊓ Subgroup.normalizer (S : Set G) ≤ T)).exists_card_eq
  have hcardS := hSyl.card_eq
  have hlt' : Nat.card S < Nat.card (T ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) :=
    Subgroup.card_lt_of_lt hlt
  rw [hcardS, ha] at hlt'
  have hab : (Nat.card V).factorization 2 < a := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt'
  have hdvd : 2 ^ a ∣ Nat.card (delta A (lB A) (Subgroup.normalizer (S : Set G))) := by
    rw [← ha]
    exact Subgroup.card_dvd_of_le hNV'
  have ha' : a ≤ (Nat.card (delta A (lB A) (Subgroup.normalizer (S : Set G)))).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd
  omega

theorem step159Claim_of
    (hK : Step159ClaimK) : Step159Claim := by
  intro G _ _ A c L ctx w hw V hV hwV
  by_contra hne
  obtain ⟨K, -, hwK, F, hF, hFeq⟩ := hK G A c L ctx w hw V hV hwV hne
  have hFΩ := hF
  obtain ⟨hFA, hF3, a, rfl, -⟩ := hF
  have ha3 : orderOf a = 3 := by rw [← Nat.card_zpowers]; exact hF3
  obtain ⟨k, hwk⟩ := hw.2.1
  have haC : a ∈ Late.sectionCentralizer A K (CFSG.Open.pCoreOf 2 K) := by
    rw [← hFeq]
    exact Subgroup.mem_zpowers a
  have hwO2 : w ∈ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 K : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hwK
  have hwa : w * a * w⁻¹ ∈ Subgroup.zpowers a := by
    have hmem : w * a * w⁻¹ ∈ Late.sectionCentralizer A K (CFSG.Open.pCoreOf 2 K) := by
      refine ⟨(Subgroup.mem_normalizer_iff.mp hw.1 a).mp haC.1, fun y hy => ?_⟩
      have hy' : w⁻¹ * y * w ∈ K := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem hwK) y).mp hy
        rwa [inv_inv] at this
      have h1 := (Subgroup.mem_normalizer_iff.mp hwO2 _).mp (haC.2 _ hy')
      rwa [show w * (a * (w⁻¹ * y * w) * a⁻¹ * (w⁻¹ * y * w)⁻¹) * w⁻¹ =
        w * a * w⁻¹ * y * (w * a * w⁻¹)⁻¹ * y⁻¹ by group] at h1
    rw [← hFeq] at hmem
    exact hmem
  have hcomm := commute_of_conj_mem_zpowers ha3 hwk hwa
  have hle : Subgroup.zpowers a ≤ A ⊓ Subgroup.centralizer ({w} : Set G) := by
    rw [Subgroup.zpowers_le]
    exact ⟨hFA (Subgroup.mem_zpowers a), Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
  rw [hw.inf_centralizer_eq ctx.toSec15R.toSec13Data.card_eq ctx.card_inf] at hle
  exact ctx.not_le_inf hFΩ hle

theorem step159W_of (hT : Step159WT) : Step159W := by
  intro G _ _ A c L ctx
  obtain ⟨w, hw, T, hTmem, hT1, hwT⟩ := hT G A c L ctx
  have h := ctx.toSec15R
  have hT2 : IsPGroup 2 T := isPGroup_of_mem_scriptQPi Nat.prime_two hTmem
  obtain ⟨hV3, -⟩ := delta_normalizer_mem_scriptY3 h.isSimpleGroup h.toSec13Data.card_eq
    hTmem.1.1 hT2 hT1
  exact ⟨w, hw, _, hV3, mem_normalizer_delta hw.1 (Subgroup.le_normalizer hwT)⟩

end CFSG.RankThree.PartTwo.Sec15
