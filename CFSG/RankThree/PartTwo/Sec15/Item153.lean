module

public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec14.Item14Statements
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item1411
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec15.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Item153Main (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB,
    CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) =
        {Subgroup.normalizer
          (oPrimeResidualOf 3 (delta A LB (Subgroup.normalizer (Y : Set G))) : Set G)} ∧
      (∀ S ∈ scriptQPiStar A LB (Subgroup.normalizer
          (oPrimeResidualOf 3 (delta A LB (Subgroup.normalizer (Y : Set G))) : Set G)) (piOf 2),
        S ∈ scriptQPiStar A LB ⊤ (piOf 2) ∧
          Subgroup.normalizer ((A ⊔ S : Subgroup G) : Set G) ≤
            Subgroup.normalizer
              (oPrimeResidualOf 3 (delta A LB (Subgroup.normalizer (Y : Set G))) : Set G)) ∧
      generalizedFitting ↥Y = CFSG.pCore 2 ↥Y

@[expose] def Claim153Twin (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB, ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
    ¬ M ≤ Subgroup.normalizer (Y : Set G) →
      M ≤ Subgroup.normalizer
        (oPrimeResidualOf 3 (delta A LB (Subgroup.normalizer (Y : Set G))) : Set G)

@[expose] def Claim153Char (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB,
    ∀ S ∈ scriptQPiStar A LB (Subgroup.normalizer
        (oPrimeResidualOf 3 (delta A LB (Subgroup.normalizer (Y : Set G))) : Set G)) (piOf 2),
      ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ S ∧ (C.subgroupOf S).Characteristic ∧
        Y ⊔ S ≤ Subgroup.normalizer (C : Set G)

omit [Finite G] in
theorem oPrimeResidualOf_mono (p : ℕ) {K K' : Subgroup G} (h : K ≤ K') :
    oPrimeResidualOf p K ≤ oPrimeResidualOf p K' := by
  rw [oPrimeResidualOf_eq_closure, oPrimeResidualOf_eq_closure]
  exact Subgroup.closure_mono fun x ⟨hx, k, hk⟩ => ⟨h hx, k, hk⟩

omit [Finite G] in
theorem le_oPrimeResidualOf_delta {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {Y K : Subgroup G} (hY : Y ∈ scriptY4 A LB) (hYK : Y ≤ K) :
    Y ≤ oPrimeResidualOf 3 (delta A LB K) := by
  obtain ⟨-, h3, hΔ, -⟩ := hY
  calc Y = oPrimeResidualOf 3 Y := h3
    _ = oPrimeResidualOf 3 (delta A LB Y) := by rw [← hΔ]
    _ ≤ oPrimeResidualOf 3 (delta A LB K) := oPrimeResidualOf_mono 3 (delta_mono hYK)

omit [Finite G] in
theorem normalizer_mem_scriptY {A K : Subgroup G} (hsimp : IsSimpleGroup G)
    (hK : K ∈ scriptY A) (hK1 : K ≠ ⊥) : Subgroup.normalizer (K : Set G) ∈ scriptY A := by
  refine ⟨fun htop => hK.1 ?_, hK.2.trans Subgroup.le_normalizer⟩
  have hn : K.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  exact (hsimp.eq_bot_or_eq_top_of_normal K).resolve_left hK1

omit [Finite G] in
theorem normalizer_le_normalizer_oPrimeResidualOf_delta {A : Subgroup G}
    {LB : Subgroup G → Subgroup G} (h149 : Item149 A LB) {N : Subgroup G} (hN : N ∈ scriptY A) :
    N ≤ Subgroup.normalizer (oPrimeResidualOf 3 (delta A LB N) : Set G) := by
  obtain ⟨heq, hnorm, -⟩ := h149 N hN
  rw [heq]
  have hle : oPrimeResidualOf 3 (inSubgroup (oResidual 2) (deltaZero A LB N)) ≤ N :=
    (oPrimeResidualOf_le_self 3 _).trans ((inSubgroup_oResidual_le_self 2 _).trans
      (deltaZero_le N))
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hnorm

omit [Finite G] in
theorem ne_bot_of_mem_scriptY0 {A Y : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hY : Y ∈ scriptY0 A LB) : Y ≠ ⊥ := by
  intro h0
  apply hY.2.2
  rw [h0, eq_bot_iff]
  exact CFSG.LieType.BorelTits.pCoreOf_le 2 ⊥

theorem isCharacteristicP_of_le_normalizer {p : ℕ} [Fact p.Prime] {X Y : Subgroup G}
    (hYX : Y ≤ X) (hXY : X ≤ Subgroup.normalizer (Y : Set G)) (hX : IsCharacteristicP p ↥X) :
    IsCharacteristicP p ↥Y := by
  have hn : (Y.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr hXY
  exact isCharacteristicP_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hYX)
    (isCharacteristicP_of_normal (Y.subgroupOf X) hX)

theorem eq_normalizer_of_le {M X : Subgroup G} (hM : IsMaximalTwoLocal M)
    (hMX : M ≤ Subgroup.normalizer (X : Set G)) (hX2 : CFSG.Open.pCoreOf 2 X ≠ ⊥) :
    M = Subgroup.normalizer (X : Set G) := by
  have hloc : IsPLocal 2 (Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G)) :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X) hX2
  have hle : Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X
  have hMeq : M = Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) := by
    by_contra hne
    exact hM.2 _ (lt_of_le_of_ne (hMX.trans hle) hne) hloc
  exact le_antisymm hMX (hMeq ▸ hle)

omit [Finite G] in
theorem mem_of_mem_sup_of_pow_two_pow {A S : Subgroup G}
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hS : IsPGroup 2 S) {x : G} (hx : x ∈ A ⊔ S) {n : ℕ} (hxn : x ^ 2 ^ n = 1) : x ∈ S := by
  have hx' : x ∈ (A : Set G) * (S : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A S hAS]
    exact hx
  obtain ⟨a, ha, s, hs, rfl⟩ := Set.mem_mul.mp hx'
  have hpow : ∀ m : ℕ, ∃ t ∈ S, (a * s) ^ m = a ^ m * t := by
    intro m
    induction m with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ m ih =>
      obtain ⟨t, ht, he⟩ := ih
      have hat : a⁻¹ * t * a⁻¹⁻¹ ∈ S :=
        (Subgroup.mem_normalizer_iff.mp (hAS (inv_mem ha)) t).mp ht
      refine ⟨(a⁻¹ * t * a⁻¹⁻¹) * s, mul_mem hat hs, ?_⟩
      rw [pow_succ, he, pow_succ]
      group
  obtain ⟨t, ht, he⟩ := hpow (2 ^ n)
  rw [hxn] at he
  have haS : a ^ 2 ^ n ∈ S := by
    have : a ^ 2 ^ n = t⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      exact he.symm
    rw [this]
    exact inv_mem ht
  have h1 : a ^ 2 ^ n = 1 := by
    obtain ⟨j, hj⟩ := hS ⟨_, haS⟩
    have hj' : (a ^ 2 ^ n) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have ho1 : orderOf (a ^ 2 ^ n) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
    have ho2 : orderOf (a ^ 2 ^ n) ∣ 3 := orderOf_dvd_of_pow_eq_one (by
      rw [← pow_mul, mul_comm, pow_mul, hA3 a ha, one_pow])
    have hco : Nat.Coprime (2 ^ j) 3 := Nat.Coprime.pow_left j (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hco ho1 ho2)
  have ha1 : a = 1 := by
    have ho1 : orderOf a ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h1
    have ho2 : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one (hA3 a ha)
    have hco : Nat.Coprime (2 ^ n) 3 := Nat.Coprime.pow_left n (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hco ho1 ho2)
  rw [ha1, one_mul]
  exact hs

section Item153

variable {A : Subgroup G} {c : G} {L : Subgroup G}

theorem facts153 (h : Sec14Std G A c L) (h149 : Item149 A (lB A)) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) :
    Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer
        (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) : Set G) ∧
      Y ≤ oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) ∧
      oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) ≤
        Subgroup.normalizer (Y : Set G) ∧
      CFSG.Open.pCoreOf 2 (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer
        (Y : Set G)))) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY0 : Y ∈ scriptY0 A (lB A) := hY.prop
  have hNY : Subgroup.normalizer (Y : Set G) ∈ scriptY A :=
    normalizer_mem_scriptY h.toTheoremFourHyp.isSimpleGroup hY0.1.1 (ne_bot_of_mem_scriptY0 hY0)
  set X := oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) with hX
  have hYX : Y ≤ X := le_oPrimeResidualOf_delta hY0.1 Subgroup.le_normalizer
  have hXN : X ≤ Subgroup.normalizer (Y : Set G) :=
    (oPrimeResidualOf_le_self 3 _).trans (delta_le _)
  have hO2 : CFSG.Open.pCoreOf 2 Y ≤ CFSG.Open.pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYX)
      (hXN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y)
  exact ⟨normalizer_le_normalizer_oPrimeResidualOf_delta h149 hNY, hYX, hXN,
    fun h0 => hY0.2.2 (le_bot_iff.mp (h0 ▸ hO2))⟩

theorem exists_mem_maximalTwoLocalsContaining {Y : Subgroup G} (hY : Y ∈ scriptY2 A) :
    ∃ M, M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hloc : IsPLocal 2 (Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G)) :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y) hY.2
  have hYA : Y ⊔ A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    sup_le (Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
      (hY.1.2.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
  obtain ⟨M, hle, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  exact ⟨M, hM, fun x hx => hle (hYA hx)⟩

theorem eq_normalizer_of_mem_maximalTwoLocalsContaining (h : Sec14Std G A c L)
    (h149 : Item149 A (lB A)) (htwin : Claim153Twin A (lB A)) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G)) :
    M = Subgroup.normalizer
      (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) : Set G) := by
  obtain ⟨hNX, -, -, hX2⟩ := facts153 h h149 hY
  refine eq_normalizer_of_le hM.1 ?_ hX2
  by_cases hMY : M ≤ Subgroup.normalizer (Y : Set G)
  · exact hMY.trans hNX
  · exact htwin Y hY M hM hMY

theorem rank3II_15_3_1_of (h : Sec14Std G A c L) (h149 : Item149 A (lB A))
    (htwin : Claim153Twin A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) :
    CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) =
      {Subgroup.normalizer
        (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) : Set G)} := by
  obtain ⟨M₀, hM₀⟩ := exists_mem_maximalTwoLocalsContaining hY.prop.2
  ext M
  refine ⟨fun hMm => eq_normalizer_of_mem_maximalTwoLocalsContaining h h149 htwin hY hMm,
    fun hMeq => ?_⟩
  rw [Set.mem_singleton_iff] at hMeq
  rw [hMeq, ← eq_normalizer_of_mem_maximalTwoLocalsContaining h h149 htwin hY hM₀]
  exact hM₀

@[expose] def Claim153Normal (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ scriptY0Star A LB, ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
    M ≤ Subgroup.normalizer (Y : Set G)

omit [Finite G] in
theorem claim153Twin_of_normal {LB : Subgroup G → Subgroup G} (hn : Claim153Normal A LB) :
    Claim153Twin A LB :=
  fun Y hY M hM hMY => absurd (hn Y hY M hM) hMY

theorem normalizer_x_eq_of_normal (h : Sec14Std G A c L) (h149 : Item149 A (lB A))
    (hn : Claim153Normal A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) :
    Subgroup.normalizer
        (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) : Set G) =
      Subgroup.normalizer (Y : Set G) := by
  obtain ⟨M₀, hM₀⟩ := exists_mem_maximalTwoLocalsContaining hY.prop.2
  have heq := eq_normalizer_of_mem_maximalTwoLocalsContaining h h149
    (claim153Twin_of_normal hn) hY hM₀
  refine le_antisymm ?_ (facts153 h h149 hY).1
  rw [← heq]
  exact hn Y hY M₀ hM₀

theorem rank3II_15_3_main_of (h : Sec14Std G A c L)
    (h149 : Item149 A (lB A)) (htwin : Claim153Twin A (lB A)) (hchar : Claim153Char A (lB A)) :
    Item153Main A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar2 : CFSG.Assembly.IsCharTwoType G := h.toTheoremFourHyp.charTwoType
  intro Y hY
  obtain ⟨-, hYX, hXN, -⟩ := facts153 h h149 hY
  set X := oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) with hX
  have h1 := rank3II_15_3_1_of h h149 htwin hY
  obtain ⟨M₀, hM₀⟩ := exists_mem_maximalTwoLocalsContaining hY.prop.2
  have hNXmax : IsMaximalTwoLocal (Subgroup.normalizer (X : Set G)) :=
    eq_normalizer_of_mem_maximalTwoLocalsContaining h h149 htwin hY hM₀ ▸ hM₀.1
  have hloc_le : ∀ K : Subgroup G, IsPLocal 2 K → Y ⊔ A ≤ K →
      K ≤ Subgroup.normalizer (X : Set G) := by
    intro K hK hYAK
    obtain ⟨M, hKM, hMm⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hK
    rw [← eq_normalizer_of_mem_maximalTwoLocalsContaining h h149 htwin hY
      ⟨hMm, fun x hx => hKM (hYAK hx)⟩]
    exact hKM
  refine ⟨h1, fun S hS => ?_, ?_⟩
  ·
    obtain ⟨C, hC1, hCS, hCchar, hYSC⟩ := hchar Y hY S hS
    have hSp : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
    have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
    have hAC : A ≤ Subgroup.normalizer (C : Set G) := by
      have hAS' : A ≤ Subgroup.normalizer
          (((C.subgroupOf S).map S.subtype : Subgroup G) : Set G) :=
        hAS.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
      rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCS] at hAS'
    have hCp : IsPGroup 2 C := hSp.to_le hCS
    have hNC : Subgroup.normalizer (C : Set G) ≤ Subgroup.normalizer (X : Set G) :=
      hloc_le _ (CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hCp hC1)
        (sup_le (le_sup_left.trans hYSC) hAC)
    have hnormS : Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (C : Set G) := by
      have h' := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (H := S) (C.subgroupOf S)
      rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCS] at h'
    refine ⟨?_, ?_⟩
    ·
      refine ⟨⟨⟨hS.prop.1.1, le_top⟩, hS.prop.2⟩, fun T hT hST => ?_⟩
      have hTp : IsPGroup 2 T := isPGroup_of_mem_scriptQPi Nat.prime_two hT
      have hNTmem : T ⊓ Subgroup.normalizer (S : Set G) ∈
          scriptQPi A (lB A) (Subgroup.normalizer (X : Set G)) (piOf 2) := by
        have hAN : A ≤ Subgroup.normalizer
            ((T ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) : Set G) :=
          Late.le_normalizer_inf hT.1.1.1.2.2
            (hAS.trans (Sec6.normalizer_le_normalizer_normalizer S))
        exact ⟨⟨mem_scriptQ_of_le hT.1.1 inf_le_left hAN,
          inf_le_right.trans (hnormS.trans hNC)⟩,
          (isPiSubgroup_piOf_iff Nat.prime_two _).mpr (hTp.to_le inf_le_left)⟩
      have hNTS : T ⊓ Subgroup.normalizer (S : Set G) ≤ S :=
        hS.2 hNTmem (le_inf hST Subgroup.le_normalizer)
      by_contra hTS
      have hlt : S.subgroupOf T < ⊤ := by
        refine lt_top_iff_ne_top.mpr fun htop => hTS fun x hx => ?_
        have : (⟨x, hx⟩ : T) ∈ S.subgroupOf T := htop ▸ Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp this
      have : Group.IsNilpotent T := hTp.isNilpotent
      obtain ⟨y, hyN, hyS⟩ :=
        IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
      rw [← Subgroup.subgroupOf_normalizer_eq hST, Subgroup.mem_subgroupOf] at hyN
      exact hyS (Subgroup.mem_subgroupOf.mpr (hNTS ⟨y.2, hyN⟩))
    ·
      refine le_trans ?_ (hnormS.trans hNC)
      refine Sec6.le_normalizer_of_forall_conj_mem fun g hg s hs => ?_
      have hgs : g * s * g⁻¹ ∈ A ⊔ S :=
        (Subgroup.mem_normalizer_iff.mp hg s).mp (Subgroup.mem_sup_right hs)
      obtain ⟨k, hk⟩ := hSp ⟨s, hs⟩
      have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      refine mem_of_mem_sup_of_pow_two_pow hAS h.toSec13Data.isElemAbelian.2 hSp hgs (n := k) ?_
      rw [conj_pow, hk', mul_one, mul_inv_cancel]
  ·
    have hloc : IsPLocal 2 (Subgroup.normalizer (X : Set G)) := hNXmax.1
    have hXc : IsCharacteristicP 2 ↥(Subgroup.normalizer (X : Set G)) :=
      CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal hchar2 hloc
    have hXchar : IsCharacteristicP 2 ↥X :=
      isCharacteristicP_of_le_normalizer Subgroup.le_normalizer le_rfl hXc
    have hYchar : IsCharacteristicP 2 ↥Y := isCharacteristicP_of_le_normalizer hYX hXN hXchar
    exact (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥Y 2).mp hYchar

end Item153

end CFSG.RankThree.PartTwo.Sec15
