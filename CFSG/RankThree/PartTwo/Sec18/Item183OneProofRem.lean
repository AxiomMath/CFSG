module

public import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRemTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open scoped Pointwise

namespace Rem187QProof

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le {A M : Subgroup G} (h : Sec18Std G A M) :
    Subgroup.normalizer (A : Set G) ≤ M :=
  (normalizer_le_gamma le_rfl
    (by rw [(isE27_of_mem_partTwoE h.mem_partTwoE).pRank_eq]; norm_num)).trans
      fun _ hx => h.mem_scriptM.2 hx

theorem exists_mul_of_frattini {A B K : Subgroup G} {c : G}
    (hNK : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hB : CFSG.ABGLocalTools.IsSylowOf 3 B (K ⊓ Subgroup.centralizer ({c} : Set G)))
    (hA : A = B ⊔ Subgroup.zpowers c) {g : G}
    (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    ∃ y ∈ K ⊓ Subgroup.centralizer ({c} : Set G), ∃ w ∈ Subgroup.normalizer (A : Set G),
      w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∧ g = y * w := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤
      Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hNK hx, mem_normalizer_centralizer_of_mem_normalizer_zpowers hx⟩
  obtain ⟨y, hy, w, hw, rfl⟩ := Sec18.exists_mul_of_isSylowOf hB hN hg
  have hyN : y ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    centralizer_le_normalizer_zpowers c hy.2
  have hwN : w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hyN) hg
    rwa [inv_mul_cancel_left] at this
  refine ⟨y, hy, w, ?_, hwN, rfl⟩
  rw [hA]
  exact Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hw, hwN⟩

theorem mem_normalizer_iSup {A M K : Subgroup G} (h : Sec18Std G A M) {x : G}
    (hx : x ∈ K ∨ (x ∈ Subgroup.normalizer (A : Set G) ∧ x ∈ Subgroup.normalizer (K : Set G))) :
    x ∈ Subgroup.normalizer
      ((⨆ H ∈ {H : Subgroup G | H ∈ scriptH A M ∧ K ≤ H}, CFSG.Open.pCoreOf 2 H :
        Subgroup G) : Set G) := by
  refine mem_normalizer_iSup_pCoreOf fun H ⟨hH, hKH⟩ => ?_
  rcases hx with hxK | ⟨hxA, hxK⟩
  · rw [map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer (hKH hxK))]
    exact ⟨hH, hKH⟩
  · refine ⟨map_conj_mem_scriptH hxA (normalizer_le h hxA) hH, ?_⟩
    rw [← map_conj_eq_of_mem_normalizer hxK]
    exact Subgroup.map_mono hKH

end Rem187QProof

open Rem187QProof

end CFSG.RankThree.PartTwo.Sec18
