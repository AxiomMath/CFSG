module

public import CFSG.RankThree.PartTwo.Sec19.Item194Inputs
import CFSG.RankThree.PartTwo.Sec19.Item194Proof
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec19
open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock IsTwoPrimeComponent NineThreeConclusion barM
  Asc81bEightFour Asc81bNineThree)

namespace Res6

structure SettingJ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) : Prop
    extends PartTwoStanding G where
  isE27 : IsE27 A
  mem_scriptM : M ∈ scriptM (gamma 2 A : Set G)
  mem_scriptM_H : H ∈ scriptM (A : Set G)
  ne : H ≠ M
  twoCore_inf : CFSG.Open.pCoreOf 2 (H ⊓ M) = CFSG.Open.pCoreOf 2 H

namespace SettingJ

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G}

theorem twoCore_ne_bot (h : SettingJ G A M H) : CFSG.Open.pCoreOf 2 H ≠ ⊥ :=
  pCoreOf_ne_bot_of_isMaximalTwoLocal h.mem_scriptM_H.1

theorem normalizer_twoCore (h : SettingJ G A M H) :
    Subgroup.normalizer (CFSG.Open.pCoreOf 2 H : Set G) = H :=
  normalizer_pCoreOf_of_isMaximalTwoLocal h.mem_scriptM_H.1

theorem twoCore_le_M (h : SettingJ G A M H) : CFSG.Open.pCoreOf 2 H ≤ M := by
  rw [← h.twoCore_inf]
  exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right

theorem twoCore_eq (h : SettingJ G A M H) :
    CFSG.Open.pCoreOf 2 H =
      CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.normalizer (CFSG.Open.pCoreOf 2 H : Set G)) := by
  rw [h.normalizer_twoCore, inf_comm, h.twoCore_inf]

theorem twoCore_M_le (h : SettingJ G A M H) :
    CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 H :=
  AGLEmbedding.le_of_two_radical h.twoCore_le_M h.twoCore_eq
    (CFSG.LieType.BorelTits.pCoreOf_le 2 M) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
    (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))

theorem not_twoCore_le (h : SettingJ G A M H) :
    ¬ CFSG.Open.pCoreOf 2 H ≤ CFSG.Open.pCoreOf 2 M := fun hle => h.ne (by
  rw [← h.normalizer_twoCore, le_antisymm hle h.twoCore_M_le,
    normalizer_pCoreOf_of_isMaximalTwoLocal h.mem_scriptM.1])

theorem ne_top (h : SettingJ G A M H) : M ≠ ⊤ := by
  intro hM
  exact h.mem_scriptM_H.1.2 M (lt_of_le_of_ne (hM ▸ le_top) h.ne) h.mem_scriptM.1.1

theorem isKGroup (h : SettingJ G A M H) : CFSG.Open.IsKGroup ↥M :=
  CFSG.KCore.KProperNonab.kGroupNonab CFSG.Open.isCatalogGroup_isoInvariant h.kProper M h.ne_top

theorem asc81bHyp (h : SettingJ G A M H) : Asc81bHyp M (CFSG.Open.pCoreOf 2 H) where
  twoRadical := ⟨h.twoCore_le_M, h.twoCore_ne_bot, h.twoCore_eq⟩
  charTwo := h.charTwoType M h.mem_scriptM.1.1
  cgs := by
    rw [AGLEmbedding.maxTwoLocal_cgsIn_eq_inf
      (Item194Proof.glbIsMaxTwoLocal_of_isMaximalTwoLocal h.mem_scriptM_H.1),
      h.normalizer_twoCore]

theorem mem_scriptJ_iff (h : SettingJ G A M H) {K : Subgroup G} :
    K ∈ scriptJ M H ↔ IsWeakSBlock M (CFSG.Open.pCoreOf 2 H) K := by
  constructor
  · rintro ⟨hK, hKH⟩
    exact ⟨Item194Proof.isTwoPrimeComponent_of_mem_oTwoComponentsIn hK,
      fun hle => hKH (h.normalizer_twoCore ▸ hle)⟩
  · intro hK
    exact ⟨Item194Proof.mem_oTwoComponentsIn_of_isTwoPrimeComponent hK.toIsTwoPrimeComponent,
      fun hle => hK.not_le_normalizer (h.normalizer_twoCore.symm ▸ hle)⟩

theorem pRank_le_localRank (h : SettingJ G A M H) {p : ℕ} (hp : p.Prime) :
    CFSG.Open.pRank p M ≤ CFSG.Assembly.RankThreeEven.localRank p G :=
  le_csSup ⟨Nat.card G, by
    rintro _ ⟨Y, -, rfl⟩
    exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_card p hp Y).trans
      (Subgroup.card_le_card_group Y)⟩ ⟨M, h.mem_scriptM.1.1, rfl⟩

theorem pRank_le_two (h : SettingJ G A M H) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    CFSG.Open.pRank p M ≤ 2 :=
  Nat.lt_succ_iff.mp ((h.pRank_le_localRank hp).trans_lt (h.localRank_lt p hp hp3))

theorem pRank_three_le (h : SettingJ G A M H) : CFSG.Open.pRank 3 M ≤ 3 :=
  (h.pRank_le_localRank Nat.prime_three).trans h.localRank_three.le

theorem not_isScriptLBlock (h : SettingJ G A M H) (h316 : Item316) (L : Subgroup G) :
    ¬ IsScriptLBlock M L := fun hL =>
  h.not_inCatalog (h316 G h.isSimpleGroup h.nonabelian h.kProper h.charTwoType h.evenRank_eq M L
    h.mem_scriptM.1 hL)

theorem scriptJ_nonempty (h : SettingJ G A M H) (h84 : Asc81bEightFour) (h316 : Item316) :
    (scriptJ M H).Nonempty := by
  have hS2 : IsPGroup 2 ((CFSG.Open.pCoreOf 2 H).subgroupOf M) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).comap_subtype
  have hSQ : ¬ (CFSG.Open.pCoreOf 2 H).subgroupOf M ≤ CFSG.pCore 2 ↥M := by
    intro hle
    apply h.not_twoCore_le
    intro x hx
    exact (Item194Proof.mem_pCore_iff (⟨x, h.twoCore_le_M hx⟩ : M)).mp
      (hle (Subgroup.mem_subgroupOf.mpr hx))
  rcases AGLEmbedding.exists_component_not_le_normalizer_or_not_le_centralizer hS2 hSQ with
    ⟨Lbar, hLbar, hnot⟩ | hodd
  · obtain ⟨L, hL, hbar⟩ := AGLEmbedding.exists_isTwoPrimeComponent hLbar
    refine ⟨L, h.mem_scriptJ_iff.mpr ⟨hL, fun hLS => hnot ?_⟩⟩
    rw [← hbar]
    exact AGLEmbedding.barM_le_normalizer_barM hLS
  · rcases h84 G M (CFSG.Open.pCoreOf 2 H) h.isKGroup h.asc81bHyp with h1 | ⟨Y, hYM, hYs, hY⟩
    · exact (hodd h1).elim
    · exact (h.not_isScriptLBlock h316 Y
        (Item194Proof.isScriptLBlock_of_alternatingFour hYM hYs hY)).elim

end SettingJ

end Res6

end CFSG.RankThree.PartTwo.Sec20
