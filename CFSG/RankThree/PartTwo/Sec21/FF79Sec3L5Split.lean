module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.LieType.Simplicity.Classical
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.QuasisimpleOfCentralKer
public import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

theorem s35_layer_normal {H : Type*} [Group H] : (layer H).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have h := WholeGroup.layer_map_mulEquiv (MulAut.conj g)
  rw [← h]
  exact Subgroup.mem_map.mpr ⟨n, hn, by simp [mul_assoc]⟩

theorem s35_factorization_20160 : (20160 : ℕ).factorization 3 = 2 := by
  have h : (20160 : ℕ) = 3 ^ 2 * 2240 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem s35_card_sylow_inf {H : Type} [Group H] [Finite H] {S L : Subgroup H} [L.Normal]
    (hS : IsSylowOf 3 S ⊤) (hL : Nat.card L = 20160) : Nat.card ↥(S ⊓ L) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS' : CFSG.ABGLocalTools.IsSylowOf 3 S (⊤ : Subgroup H) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, hS.2.1, ?_⟩
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hS.2.2
  have h1 := hS'.inf_of_le_normalizer (N := L) le_top (by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance])
  rw [CFSG.ABGLocalTools.IsSylowOf.card_eq h1, hL, s35_factorization_20160]
  norm_num

theorem s35_layer_card {H : Type} [Group H]
    (hL : StatedClassicalModel ↥(⊤ : Subgroup ↥(layer H)) .PSL 3 2 2) :
    Nat.card ↥(layer H) = 20160 := by
  have h := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four hL
  rwa [Subgroup.card_top] at h

theorem s35_layer_center {H : Type} [Group H] [Finite H]
    (hL : StatedClassicalModel ↥(⊤ : Subgroup ↥(layer H)) .PSL 3 2 2) :
    ∀ z ∈ layer H, z ∈ Subgroup.center H → z = 1 := by
  intro z hzL hzc
  haveI : IsSimpleGroup ↥(⊤ : Subgroup ↥(layer H)) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 hL).2
  set X := ↥(⊤ : Subgroup ↥(layer H)) with hX
  have hc : Nat.card X = 20160 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four hL
  have hnorm : (Subgroup.center X).Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · have hz : (⟨⟨z, hzL⟩, trivial⟩ : X) ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp hzc (w : ↥(layer H)).1
    rw [h, Subgroup.mem_bot] at hz
    exact congrArg (fun w : X => ((w : ↥(layer H)) : H)) hz
  · exfalso
    letI : CommGroup X :=
      { (inferInstance : Group X) with
        mul_comm := fun a b => by
          have : a ∈ Subgroup.center X := by rw [h]; trivial
          exact (Subgroup.mem_center_iff.mp this b).symm }
    have := IsSimpleGroup.prime_card (α := X)
    rw [hc] at this
    exact absurd this (by norm_num)

theorem s35_comm_card27 {G : Type*} [Group G] {P : Subgroup G} (hP : Nat.card P = 27) {x y : G}
    (hx : x ∈ P) (hy : y ∈ P) : ⁅⁅x, y⁆, y⁆ = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := (AGLEmbeddingD2.Wilson.Proving.commute_commutatorElement_of_card_eq_prime_cube
    (p := 3) (by simpa using hP) hx hy).2
  rw [commutatorElement_def, h.eq.symm]
  group

end CFSG.RankThree.PartTwo.Sec21.FF79
