module

public import CFSG.RankThree.GroupTheory.SteinbergCETwoCoreAlpha
public import CFSG.RankThree.GroupTheory.SteinbergBMCoprimeGeneration
public import CFSG.RankThree.GroupTheory.SteinbergBMFrattiniNormalizerTwoCore

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG.RankThree.GroupTheory
open scoped Pointwise

variable {G : Type*} [Group G]

theorem alpha_product_structure {B : Subgroup G} (hB : B ≠ ⊥) :
    twoCoreX B ≤ CFSG.inSubgroup (CFSG.pCore 2) (centralizer (B : Set G)) ∧
      twoCoreX B ≤ normalizer (twoCoreJ B : Set G) ∧
      twoCoreAlpha B = twoCoreJ B ⊔ twoCoreX B ∧
      (twoCoreAlpha B : Set G) = (twoCoreJ B : Set G) * (twoCoreX B : Set G) ∧
      centralizer (B : Set G) ≤ normalizer (twoCoreX B : Set G) ∧
      centralizer (B : Set G) ≤ normalizer (twoCoreJ B : Set G) ∧
      centralizer (B : Set G) ≤ normalizer (twoCoreAlpha B : Set G) := by
  have hCb : ∀ c ∈ centralizer (B : Set G), ∀ b ∈ B, c ∈ centralizer ({b} : Set G) :=
    fun c hc b hb => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc b hb).symm
  have hCR : ∀ c ∈ centralizer (B : Set G), ∀ b ∈ B,
      c ∈ normalizer (CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({b} : Set G)) : Set G) :=
    fun c hc b hb => le_normalizer_inSubgroup_pCore 2 _ (hCb c hc b hb)
  obtain ⟨⟨b₀, hb₀⟩, hb₀1'⟩ := ne_bot_iff_exists_ne_one.mp hB
  have hb₀1 : b₀ ≠ 1 := fun h => hb₀1' (Subtype.ext h)
  have hX2 : IsPGroup 2 (twoCoreX B) := by
    refine ((CFSG.pCore_isPGroup (p := 2) (G := centralizer ({b₀} : Set G))).map
      (centralizer ({b₀} : Set G)).subtype).to_le fun x hx => ?_
    exact mem_twoCoreX_iff.mp hx b₀ hb₀ hb₀1
  have hXC : twoCoreX B ≤ centralizer (B : Set G) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro b hb
    by_cases hb1 : b = 1
    · rw [hb1, one_mul, mul_one]
    · have hxb : x ∈ centralizer ({b} : Set G) :=
        map_subtype_le _ (mem_twoCoreX_iff.mp hx b hb hb1)
      exact (mem_centralizer_singleton_iff.mp hxb).symm
  have hCX : centralizer (B : Set G) ≤ normalizer (twoCoreX B : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun c hc x hx => ?_
    rw [mem_twoCoreX_iff] at hx ⊢
    intro b hb hb1
    exact (mem_normalizer_iff.mp (hCR c hc b hb) x).mp (hx b hb hb1)
  have hCJ : centralizer (B : Set G) ≤ normalizer (twoCoreJ B : Set G) := by
    intro c hc
    have hcB : c ∈ normalizer (B : Set G) := centralizer_le_normalizer _ hc
    rw [mem_normalizer_iff_map_conj_eq, twoCoreJ]
    simp only [Subgroup.map_iSup]
    refine iSup_congr fun b => iSup_congr fun hb => iSup_congr fun _ => ?_
    rw [map_commutator, (mem_normalizer_iff_map_conj_eq).mp (hCR c hc b hb),
      (mem_normalizer_iff_map_conj_eq).mp hcB]
  have hXJ : twoCoreX B ≤ normalizer (twoCoreJ B : Set G) := hXC.trans hCJ
  have hcoe : (twoCoreAlpha B : Set G) = (twoCoreJ B : Set G) * (twoCoreX B : Set G) :=
    coe_mul_of_right_le_normalizer_left (twoCoreJ B) (twoCoreX B) hXJ
  have hCα : centralizer (B : Set G) ≤ normalizer (twoCoreAlpha B : Set G) := by
    intro c hc
    rw [mem_normalizer_iff_map_conj_eq, twoCoreAlpha, Subgroup.map_sup,
      (mem_normalizer_iff_map_conj_eq).mp (hCJ hc), (mem_normalizer_iff_map_conj_eq).mp (hCX hc)]
  refine ⟨le_inSubgroup_pCore_of_normal hX2 hXC hCX, hXJ, rfl, hcoe, hCX, hCJ, hCα⟩

end CFSG.RankThree.GroupTheory.SteinbergBM
