module

public import CFSG.RankThree.PartTwo.Sec15.Item158StepsProofChar
import CFSG.CGT.PushingUp.TwoLocals
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan152Six

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}

theorem eq_n155_of_forall_le_normalizer (h : Sec14Std G A c L) (h149 : Item149 A (lB A))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hn : ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      M ≤ Subgroup.normalizer (Y : Set G))
    {M : Subgroup G} (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G)) :
    M = n155 A Y := by
  obtain ⟨hNX, -, -, hX2⟩ := facts153 h h149 hY
  exact eq_normalizer_of_le hM.1 ((hn M hM).trans hNX) hX2

theorem maximalTwoLocalsContaining_eq_of_forall_le_normalizer (h : Sec14Std G A c L)
    (h149 : Item149 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hn : ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      M ≤ Subgroup.normalizer (Y : Set G)) :
    CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) = {n155 A Y} := by
  obtain ⟨M₀, hM₀⟩ := exists_mem_maximalTwoLocalsContaining hY.prop.2
  ext M
  refine ⟨fun hMm => eq_n155_of_forall_le_normalizer h h149 hY hn hMm, fun hMeq => ?_⟩
  rw [Set.mem_singleton_iff] at hMeq
  rw [hMeq, ← eq_n155_of_forall_le_normalizer h h149 hY hn hM₀]
  exact hM₀

theorem n155_le_normalizer_of_forall_le_normalizer (h : Sec14Std G A c L)
    (h149 : Item149 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hn : ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      M ≤ Subgroup.normalizer (Y : Set G)) :
    n155 A Y ≤ Subgroup.normalizer (Y : Set G) := by
  obtain ⟨M₀, hM₀⟩ := exists_mem_maximalTwoLocalsContaining hY.prop.2
  rw [← eq_n155_of_forall_le_normalizer h h149 hY hn hM₀]
  exact hn M₀ hM₀

theorem le_n155_of_isPLocal_of_forall_le_normalizer (h : Sec14Std G A c L)
    (h149 : Item149 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hn : ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      M ≤ Subgroup.normalizer (Y : Set G))
    {K : Subgroup G} (hK : IsPLocal 2 K) (hYAK : Y ⊔ A ≤ K) : K ≤ n155 A Y := by
  obtain ⟨M, hKM, hMm⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hK
  rw [← eq_n155_of_forall_le_normalizer h h149 hY hn ⟨hMm, fun x hx => hKM (hYAK hx)⟩]
  exact hKM

theorem generalizedFitting_eq_of_forall_le_normalizer (h : Sec14Std G A c L)
    (h149 : Item149 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hn : ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      M ≤ Subgroup.normalizer (Y : Set G)) :
    generalizedFitting ↥Y = CFSG.pCore 2 ↥Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hYX, hXN, -⟩ := facts153 h h149 hY
  obtain ⟨M₀, hM₀⟩ := exists_mem_maximalTwoLocalsContaining hY.prop.2
  have hNXmax : IsMaximalTwoLocal (n155 A Y) :=
    eq_n155_of_forall_le_normalizer h h149 hY hn hM₀ ▸ hM₀.1
  have hXc : IsCharacteristicP 2 ↥(n155 A Y) :=
    CFSG.CGT.PushingUp.isCharacteristicP_of_isPLocal h.toTheoremFourHyp.charTwoType hNXmax.1
  have hXchar : IsCharacteristicP 2
      ↥(oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G)))) :=
    isCharacteristicP_of_le_normalizer Subgroup.le_normalizer le_rfl hXc
  have hYchar : IsCharacteristicP 2 ↥Y := isCharacteristicP_of_le_normalizer hYX hXN hXchar
  exact (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥Y 2).mp hYchar

theorem mem_scriptQPiStar_top_of_charNormal153 (h : Sec14Std G A c L) (h149 : Item149 A (lB A))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hn : ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      M ≤ Subgroup.normalizer (Y : Set G))
    {S : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2))
    (hC : CharNormal153 Y S) :
    S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) ∧
      Subgroup.normalizer ((A ⊔ S : Subgroup G) : Set G) ≤ n155 A Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C, hC1, hCS, hCchar, hYSC⟩ := hC
  have hSp : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
  have hAC : A ≤ Subgroup.normalizer (C : Set G) := by
    have hAS' : A ≤ Subgroup.normalizer
        (((C.subgroupOf S).map S.subtype : Subgroup G) : Set G) :=
      hAS.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCS] at hAS'
  have hCp : IsPGroup 2 C := hSp.to_le hCS
  have hNC : Subgroup.normalizer (C : Set G) ≤ n155 A Y :=
    le_n155_of_isPLocal_of_forall_le_normalizer h h149 hY hn
      (CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup hCp hC1)
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
        scriptQPi A (lB A) (n155 A Y) (piOf 2) := by
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

theorem item153Main_at_of_forall_le_normalizer (h : Sec14Std G A c L) (h149 : Item149 A (lB A))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (hn : ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      M ≤ Subgroup.normalizer (Y : Set G))
    (hchar : ∀ S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2), CharNormal153 Y S) :
    CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) = {n155 A Y} ∧
      (∀ S ∈ scriptQPiStar A (lB A) (n155 A Y) (piOf 2),
        S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) ∧
          Subgroup.normalizer ((A ⊔ S : Subgroup G) : Set G) ≤ n155 A Y) ∧
      generalizedFitting ↥Y = CFSG.pCore 2 ↥Y :=
  ⟨maximalTwoLocalsContaining_eq_of_forall_le_normalizer h h149 hY hn,
    fun S hS => mem_scriptQPiStar_top_of_charNormal153 h h149 hY hn hS (hchar S hS),
    generalizedFitting_eq_of_forall_le_normalizer h h149 hY hn⟩

end CFSG.RankThree.PartTwo.Sec15.Ronan152Six
