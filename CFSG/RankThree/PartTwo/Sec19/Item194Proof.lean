module

public import CFSG.RankThree.PartTwo.Sec19.Item194Inputs
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockStructureAux
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectCoprimeLifts
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock IsTwoPrimeComponent NineThreeConclusion barM
  Asc81bEightFour Asc81bNineThree)
open CFSG.QuasithinUnique (IsAltType evenWeight)

open scoped commutatorElement

namespace Item194Proof

section General

variable {G : Type} [Group G]

theorem glbIsMaxTwoLocal_of_isMaximalTwoLocal {M : Subgroup G}
    (hM : CFSG.IsMaximalTwoLocal M) : CFSG.Open.GLBIsMaxTwoLocal M :=
  ⟨hM.1, fun X hX hMX => by
    by_contra hne
    exact hM.2 X (lt_of_le_of_ne hMX (Ne.symm hne)) hX⟩

theorem mem_pCore_iff {K : Subgroup G} (k : K) :
    k ∈ CFSG.pCore 2 K ↔ (k : G) ∈ CFSG.Open.pCoreOf 2 K := (CFSG.mem_openPCoreOf_iff k).symm

theorem nonempty_barM_mulEquiv {M L : Subgroup G} (hLM : L ≤ M)
    (h : L ⊓ CFSG.Open.pCoreOf 2 M = CFSG.Open.pCoreOf 2 L) :
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(barM M L)) := by
  set f : ↥L →* ↥M ⧸ CFSG.pCore 2 ↥M :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hLM) with hf
  have hker : f.ker = CFSG.pCore 2 ↥L := by
    ext l
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_pCore_iff, mem_pCore_iff, ← h, Subgroup.coe_inclusion]
    exact ⟨fun hl => ⟨l.2, hl⟩, fun hl => hl.2⟩
  have hrange : f.range = barM M L := by
    rw [hf, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivRange f)).trans (MulEquiv.subgroupCongr hrange)⟩

theorem isQuasisimple_of_open {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨h1⟩, h2, ?_⟩
  by_contra hc
  push Not at hc
  have hZ : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (Subgroup.center Q) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc _ _
  rw [h1] at hZ
  have hall : ∀ q : Q ⧸ Subgroup.center Q, q = 1 := fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact (QuotientGroup.eq_one_iff x).mpr (hZ (Subgroup.mem_top x))
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  exact hab ((hall a).trans (hall b).symm)

theorem open_of_isQuasisimple {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

theorem inf_pCoreOf_le [Finite G] {M J : Subgroup G} (hJM : J ≤ M) :
    J ⊓ CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 J :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    (fun _j hj => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hj,
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hJM hj)⟩)
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_right)

theorem isSubnormal_subgroupOf_of_open {M Y : Subgroup G} (hY : CFSG.Open.IsSubnormal Y M) :
    (Y.subgroupOf M).IsSubnormal := by
  have h := CFSG.RankThreeCoreUniqueness.Helpers.cfsg_isSubnormal_comap M.subtype hY
  have hM : M.comap M.subtype = ⊤ := Subgroup.subgroupOf_self M
  rw [hM] at h
  exact CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain h
    Subgroup.IsSubnormal.top

theorem isTwoPrimeComponent_of_mem_oTwoComponentsIn [Finite G] {M K : Subgroup G}
    (hK : K ∈ oTwoComponentsIn M) : IsTwoPrimeComponent M K := by
  obtain ⟨hKM, ⟨-, hsn, -⟩⟩ := mem_oTwoComponentsIn_iff.mp hK
  have hinf : K ⊓ CFSG.Open.pCoreOf 2 M = CFSG.Open.pCoreOf 2 K :=
    le_antisymm (inf_pCoreOf_le hKM) (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
      (Sec18.pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hK))
  obtain ⟨e⟩ := nonempty_barM_mulEquiv hKM hinf
  have hchain := CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hsn
  refine ⟨hKM, ?_, Sec18.commutator_eq_of_mem_oTwoComponentsIn hK, le_top, ?_, ?_⟩
  · have h := CFSG.ComponentClassification.Components.chain_map M.subtype hchain
    rwa [Subgroup.map_subgroupOf_eq_of_le hKM, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
  · have h := CFSG.ComponentClassification.Components.chain_map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) hchain
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
  · exact open_of_isQuasisimple (CFSG.LocalCores.isQuasisimple_of_mulEquiv e
      (Sec18.isQuasisimple_of_mem_oTwoComponentsIn hK))

theorem mem_oTwoComponentsIn_of_isTwoPrimeComponent {M L : Subgroup G}
    (hL : IsTwoPrimeComponent M L) : L ∈ oTwoComponentsIn M := by
  obtain ⟨e⟩ := nonempty_barM_mulEquiv hL.le hL.inf_twoCore
  exact Sec18.mem_oTwoComponentsIn_of_quasisimple hL.le hL.isSubnormal_subgroupOf hL.perfect
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_of_open hL.component.2.2))

end General

section AltType

variable {G : Type} [Group G]

theorem evenWeightOnes_eq_bot {n : ℕ} (hn : Odd n) : evenWeightOnes n = ⊥ := by
  rw [eq_bot_iff]
  rintro x hx
  rw [evenWeightOnes, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_zmultiples_iff] at hx
  obtain ⟨k, hk⟩ := hx
  have hsum := x.2
  simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply] at hsum
  rw [← hk] at hsum
  simp only [allOnes, Pi.smul_apply, zsmul_eq_mul, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hn1 : (n : ZMod 2) = 1 := by
    obtain ⟨m, rfl⟩ := hn
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
  rw [hn1, one_mul] at hsum
  rw [AddSubgroup.mem_bot]
  apply Subtype.ext
  rw [← hk]
  funext i
  simp [allOnes, zsmul_eq_mul, hsum]

theorem isAltNaturalType_of_isAltType {L : Subgroup G} {n : ℕ} (hn : Odd n)
    (h : IsAltType L n) : IsAltNaturalType L n := by
  obtain ⟨α, hαs, hαk, β, hβs, hβk, hR⟩ := h
  set q := QuotientAddGroup.mk' (evenWeightOnes n) with hq
  have hqinj : Function.Injective q := by
    rw [← AddMonoidHom.ker_eq_bot_iff, QuotientAddGroup.ker_mk', evenWeightOnes_eq_bot hn]
  refine ⟨α, hαs, hαk, (AddMonoidHom.toMultiplicative q).comp β,
    (QuotientAddGroup.mk'_surjective _).comp hβs, ?_, fun ℓ u v huv x hx => ?_⟩
  · rw [← hβk]
    ext u
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro hu
      have h1 : q (Multiplicative.toAdd (β u)) = q 0 := by
        rw [map_zero]
        exact congrArg Multiplicative.toAdd hu
      have h2 := hqinj h1
      exact congrArg Multiplicative.ofAdd h2
    · intro hu
      rw [hu]
      rfl
  · change q (Multiplicative.toAdd (β v)) = q (evenWeightPerm (α ℓ : Equiv.Perm (Fin n)) x)
    have hux : Multiplicative.toAdd (β u) = x := hqinj hx
    congr 1
    apply Subtype.ext
    funext i
    rw [hR ℓ u v huv i, hux]
    rfl

end AltType

section Blocks

variable {G : Type} [Group G] [Finite G]

theorem isScriptLBlock_of_inClassXBlock {M Y : Subgroup G} (hYM : Y ≤ M)
    (hY : CFSG.Open.IsSubnormal Y M) (hX : AGLEmbedding.InClassXBlock Y) : IsScriptLBlock M Y := by
  obtain ⟨hs, hX⟩ := hX
  refine ⟨⟨IsShort2.isShort hs, hYM, isSubnormal_subgroupOf_of_open hY⟩, ?_⟩
  rcases hX with ⟨n, -, hlin⟩ | ⟨n, -, halt⟩
  · exact Or.inl ⟨n, hlin⟩
  · exact Or.inr (Or.inl ⟨2 * n + 1, isAltNaturalType_of_isAltType ⟨n, rfl⟩ halt⟩)

theorem isScriptLBlock_of_alternatingFour {M Y : Subgroup G} (hYM : Y ≤ M)
    (hY : CFSG.Open.IsSubnormal Y M) (e : Nonempty (↥Y ≃* alternatingGroup (Fin 4))) :
    IsScriptLBlock M Y :=
  isScriptLBlock_of_inClassXBlock hYM hY (AGLEmbedding.inClassXBlock_of_mulEquiv_alternatingFour e)

end Blocks

structure Setting194 (G : Type) [Group G] [Finite G] (A M H : Subgroup G) : Prop
    extends Sec19Std G where
  isE27 : IsE27 A
  mem_scriptM : M ∈ scriptM (gamma 2 A : Set G)
  mem_scriptM_H : H ∈ scriptM (A : Set G)
  ne : H ≠ M

namespace Setting194

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G}

theorem le_H (h : Setting194 G A M H) : A ≤ H := fun _ hx => h.mem_scriptM_H.2 hx

theorem twoCore_ne_bot (h : Setting194 G A M H) : CFSG.Open.pCoreOf 2 H ≠ ⊥ :=
  pCoreOf_ne_bot_of_isMaximalTwoLocal h.mem_scriptM_H.1

theorem twoCore_inf (h : Setting194 G A M H) :
    CFSG.Open.pCoreOf 2 (H ⊓ M) = CFSG.Open.pCoreOf 2 H :=
  h.hyp191 A M H h.isE27 h.mem_scriptM h.le_H h.twoCore_ne_bot

theorem normalizer_twoCore (h : Setting194 G A M H) :
    Subgroup.normalizer (CFSG.Open.pCoreOf 2 H : Set G) = H :=
  normalizer_pCoreOf_of_isMaximalTwoLocal h.mem_scriptM_H.1

theorem twoCore_le_M (h : Setting194 G A M H) : CFSG.Open.pCoreOf 2 H ≤ M := by
  rw [← h.twoCore_inf]
  exact (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right

theorem twoCore_eq (h : Setting194 G A M H) :
    CFSG.Open.pCoreOf 2 H =
      CFSG.Open.pCoreOf 2 (M ⊓ Subgroup.normalizer (CFSG.Open.pCoreOf 2 H : Set G)) := by
  rw [h.normalizer_twoCore, inf_comm, h.twoCore_inf]

theorem twoCore_M_le (h : Setting194 G A M H) :
    CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 H :=
  AGLEmbedding.le_of_two_radical h.twoCore_le_M h.twoCore_eq
    (CFSG.LieType.BorelTits.pCoreOf_le 2 M) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
    (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))

theorem not_twoCore_le (h : Setting194 G A M H) :
    ¬ CFSG.Open.pCoreOf 2 H ≤ CFSG.Open.pCoreOf 2 M := fun hle => h.ne (by
  rw [← h.normalizer_twoCore, le_antisymm hle h.twoCore_M_le,
    normalizer_pCoreOf_of_isMaximalTwoLocal h.mem_scriptM.1])

theorem ne_top (h : Setting194 G A M H) : M ≠ ⊤ := by
  intro hM
  exact h.mem_scriptM_H.1.2 M (lt_of_le_of_ne (hM ▸ le_top) h.ne) h.mem_scriptM.1.1

theorem isKGroup (h : Setting194 G A M H) : CFSG.Open.IsKGroup ↥M :=
  CFSG.KCore.KProperNonab.kGroupNonab CFSG.Open.isCatalogGroup_isoInvariant h.kProper M h.ne_top

theorem asc81bHyp (h : Setting194 G A M H) : Asc81bHyp M (CFSG.Open.pCoreOf 2 H) where
  twoRadical := ⟨h.twoCore_le_M, h.twoCore_ne_bot, h.twoCore_eq⟩
  charTwo := h.charTwoType M h.mem_scriptM.1.1
  cgs := by
    rw [AGLEmbedding.maxTwoLocal_cgsIn_eq_inf
      (glbIsMaxTwoLocal_of_isMaximalTwoLocal h.mem_scriptM_H.1), h.normalizer_twoCore]

theorem mem_scriptJ_iff (h : Setting194 G A M H) {K : Subgroup G} :
    K ∈ scriptJ M H ↔ IsWeakSBlock M (CFSG.Open.pCoreOf 2 H) K := by
  constructor
  · rintro ⟨hK, hKH⟩
    exact ⟨isTwoPrimeComponent_of_mem_oTwoComponentsIn hK,
      fun hle => hKH (h.normalizer_twoCore ▸ hle)⟩
  · intro hK
    exact ⟨mem_oTwoComponentsIn_of_isTwoPrimeComponent hK.toIsTwoPrimeComponent,
      fun hle => hK.not_le_normalizer (h.normalizer_twoCore.symm ▸ hle)⟩

theorem pRank_le_localRank (h : Setting194 G A M H) {p : ℕ} (hp : p.Prime) :
    CFSG.Open.pRank p M ≤ CFSG.Assembly.RankThreeEven.localRank p G :=
  le_csSup ⟨Nat.card G, by
    rintro _ ⟨Y, -, rfl⟩
    exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_card p hp Y).trans
      (Subgroup.card_le_card_group Y)⟩ ⟨M, h.mem_scriptM.1.1, rfl⟩

theorem pRank_le_two (h : Setting194 G A M H) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    CFSG.Open.pRank p M ≤ 2 :=
  Nat.lt_succ_iff.mp ((h.pRank_le_localRank hp).trans_lt (h.localRank_lt p hp hp3))

theorem pRank_three_le (h : Setting194 G A M H) : CFSG.Open.pRank 3 M ≤ 3 :=
  (h.pRank_le_localRank Nat.prime_three).trans h.localRank_three.le

theorem not_isScriptLBlock (h : Setting194 G A M H) (h316 : Item316) (L : Subgroup G) :
    ¬ IsScriptLBlock M L := fun hL =>
  h.not_inCatalog (h316 G h.isSimpleGroup h.nonabelian h.kProper h.charTwoType h.evenRank_eq M L
    h.mem_scriptM.1 hL)

theorem scriptJ_nonempty (h : Setting194 G A M H) (h84 : Asc81bEightFour) (h316 : Item316) :
    (scriptJ M H).Nonempty := by
  have hS2 : IsPGroup 2 ((CFSG.Open.pCoreOf 2 H).subgroupOf M) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).comap_subtype
  have hSQ : ¬ (CFSG.Open.pCoreOf 2 H).subgroupOf M ≤ CFSG.pCore 2 ↥M := by
    intro hle
    apply h.not_twoCore_le
    intro x hx
    exact (mem_pCore_iff (⟨x, h.twoCore_le_M hx⟩ : M)).mp
      (hle (Subgroup.mem_subgroupOf.mpr hx))
  rcases AGLEmbedding.exists_component_not_le_normalizer_or_not_le_centralizer hS2 hSQ with
    ⟨Lbar, hLbar, hnot⟩ | hodd
  · obtain ⟨L, hL, hbar⟩ := AGLEmbedding.exists_isTwoPrimeComponent hLbar
    refine ⟨L, h.mem_scriptJ_iff.mpr ⟨hL, fun hLS => hnot ?_⟩⟩
    rw [← hbar]
    exact AGLEmbedding.barM_le_normalizer_barM hLS
  · rcases h84 G M (CFSG.Open.pCoreOf 2 H) h.isKGroup h.asc81bHyp with h1 | ⟨Y, hYM, hYs, hY⟩
    · exact (hodd h1).elim
    · exact (h.not_isScriptLBlock h316 Y (isScriptLBlock_of_alternatingFour hYM hYs hY)).elim

end Setting194

end Item194Proof

open Item194Proof

end CFSG.RankThree.PartTwo.Sec19
