module

public import CFSG.RankThree.PartTwo.Sec19.Item194Proof
import CFSG.LocalAnalysis.AGLEmbedding.MovedComponentsAll
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic
import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFour

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.AGLEmbedding (Asc81bEightFour barM)

namespace Item194Proof.Setting194

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G}

theorem oddCore_le_centralizer (h : Setting194 G A M H) (h84 : Asc81bEightFour)
    (h316 : Item316) :
    CFSG.pPrimeCore 2 (↥M ⧸ CFSG.pCore 2 ↥M) ≤
      Subgroup.centralizer (barM M (CFSG.Open.pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  rcases h84 G M (CFSG.Open.pCoreOf 2 H) h.isKGroup h.asc81bHyp with h1 | ⟨Y, hYM, hYs, hY⟩
  · exact h1
  · exact (h.not_isScriptLBlock h316 Y (isScriptLBlock_of_alternatingFour hYM hYs hY)).elim

theorem mk_mem_centralizer_of_centralizes_scriptJ (h : Setting194 G A M H)
    (h84 : Asc81bEightFour) (h316 : Item316) {g : ↥M}
    (hg : ∀ K ∈ scriptJ M H, ∀ k ∈ K,
      (g : G) * k * (g : G)⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) g ∈
      Subgroup.centralizer (barM M (CFSG.Open.pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  refine AGLEmbedding.mem_centralizer_of_centralizes_nonnormalizing_components
    (AGLEmbedding.pCore_quotient_pCore_eq_bot' 2)
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).comap_subtype.map _)
    (h.oddCore_le_centralizer h84 h316) fun Lbar hLbar hnot => ?_
  obtain ⟨L, hL, hbar⟩ := AGLEmbedding.exists_isTwoPrimeComponent hLbar
  have hLJ : L ∈ scriptJ M H := h.mem_scriptJ_iff.mpr ⟨hL, fun hLS => hnot (by
    rw [← hbar]
    exact AGLEmbedding.barM_le_normalizer_barM hLS)⟩
  rw [← hbar, Subgroup.mem_centralizer_iff]
  rintro _ ⟨k, hk, rfl⟩
  have hc : g * k * g⁻¹ * k⁻¹ ∈ CFSG.pCore 2 ↥M := by
    rw [mem_pCore_iff]
    simpa using hg L hLJ k (Subgroup.mem_subgroupOf.mp hk)
  have h1 := (QuotientGroup.eq_one_iff (g * k * g⁻¹ * k⁻¹)).mpr hc
  rw [← QuotientGroup.mk'_apply, map_mul, map_mul, map_mul, map_inv, map_inv,
    ← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

theorem mem_of_centralizes_scriptJ (h : Setting194 G A M H) (h84 : Asc81bEightFour)
    (h316 : Item316) {m : G} (hm : m ∈ M)
    (hmJ : ∀ K ∈ scriptJ M H, ∀ k ∈ K, m * k * m⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M) :
    m ∈ H := by
  set S := CFSG.Open.pCoreOf 2 H with hS
  have hconj : ∀ g : ↥M, QuotientGroup.mk' (CFSG.pCore 2 ↥M) g ∈
      Subgroup.centralizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        ∀ x ∈ S, (g : G) * x * (g : G)⁻¹ ∈ S := by
    intro g hg x hx
    have hxM : x ∈ M := h.twoCore_le_M hx
    have hxbar : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈ barM M S :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
    have hcomm := Subgroup.mem_centralizer_iff.mp hg _ hxbar
    have h2 : g * ⟨x, hxM⟩ * g⁻¹ * (⟨x, hxM⟩ : ↥M)⁻¹ ∈ CFSG.pCore 2 ↥M := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_mul, map_mul,
        map_inv, map_inv, ← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm.symm
    have h3 : (g : G) * x * (g : G)⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
      simpa using (mem_pCore_iff _).mp h2
    have e : (g : G) * x * (g : G)⁻¹ = ((g : G) * x * (g : G)⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact S.mul_mem (h.twoCore_M_le h3) hx
  have hc := h.mk_mem_centralizer_of_centralizes_scriptJ h84 h316 (g := ⟨m, hm⟩) hmJ
  have hc' : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨m, hm⟩ : ↥M)⁻¹ ∈
      Subgroup.centralizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [map_inv]
    exact Subgroup.inv_mem _ hc
  rw [← h.normalizer_twoCore, Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hconj ⟨m, hm⟩ hc x hx, fun hx => ?_⟩
  have h4 := hconj (⟨m, hm⟩ : ↥M)⁻¹ hc' _ hx
  have e : (((⟨m, hm⟩ : ↥M)⁻¹ : ↥M) : G) * (m * x * m⁻¹) * (((⟨m, hm⟩ : ↥M)⁻¹ : ↥M) : G)⁻¹ =
      x := by
    push_cast
    group
  rwa [e] at h4

end Item194Proof.Setting194

open Item194Proof

end CFSG.RankThree.PartTwo.Sec19

namespace CFSG.RankThree.PartTwo.Late.Hyp1921

open CFSG.RankThree.PartTwo.Sec19

variable {G : Type} [Group G] [Finite G] {A M N L : Subgroup G}

theorem setting194 (h : Hyp1921 G A M N L) : Item194Proof.Setting194 G A M N :=
  ⟨h.toSec19Std, isE27_of_mem_partTwoE h.mem_partTwoE, h.mem_scriptM, h.mem_scriptM_N, h.ne⟩

theorem mem_N_of_centralizes_scriptJ (h : Hyp1921 G A M N L)
    (h316 : Item316) {m : G} (hm : m ∈ M)
    (hmJ : ∀ K ∈ scriptJ M N, ∀ k ∈ K, m * k * m⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M) : m ∈ N :=
  h.setting194.mem_of_centralizes_scriptJ
    (CFSG.AGLEmbedding.asc81bEightFour_of_factorization
        CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved) h316 hm hmJ

end CFSG.RankThree.PartTwo.Late.Hyp1921
