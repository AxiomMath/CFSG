module

public import CFSG.OddTranspositions.Blocks
public import CFSG.OddTranspositions.HypothesisC
public import CFSG.Timmesfeld.Bridge.Asc72Triangle

import CFSG.GroupTheory.InvolutionClassDerived
import CFSG.OddTranspositions.PartThree.EightEight.FibreCentre
import CFSG.OddTranspositions.PartThree.HalphaCentralizer
import CFSG.OddTranspositions.PartThree.Nine.ThreeBlocks
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72
open CFSG.OddTranspositions.PartThree.Nine

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem commute_mul_mul_pow_left (hD : IsOddTransp D) (hN : IsNormalSet D) {x w y : G}
    (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) :
    Commute (x * y * (x * y * w) ^ n) x := by
  obtain ⟨-, -, hzx, -, -, -⟩ := ht.third_kind hD hN hn hord
  have hxyx : Commute (x * y) x := (Commute.refl x).mul_left ht.2.2.2.2.1.symm
  exact hxyx.mul_left hzx

omit [Finite G] in
theorem commute_mul_mul_pow_right (hD : IsOddTransp D) (hN : IsNormalSet D) {x w y : G}
    (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) :
    Commute (x * y * (x * y * w) ^ n) y := by
  obtain ⟨-, -, -, hzy, -, -⟩ := ht.third_kind hD hN hn hord
  have hxyy : Commute (x * y) y := ht.2.2.2.2.1.mul_left (Commute.refl y)
  exact hxyy.mul_left hzy

omit [Finite G] in
theorem not_commute_mul_mul_pow (hD : IsOddTransp D) (hN : IsNormalSet D) {x w y : G}
    (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) :
    ¬ Commute (x * y * (x * y * w) ^ n) w := by
  intro hew
  obtain ⟨hzz, -, -, -, hzw, -⟩ := ht.third_kind hD hN hn hord
  have hc : Commute ((x * y * (x * y * w) ^ n) * (x * y * w) ^ n) w :=
    hew.mul_left hzw
  have heq : (x * y * (x * y * w) ^ n) * (x * y * w) ^ n = x * y := by
    rw [mul_assoc (x * y) ((x * y * w) ^ n) ((x * y * w) ^ n), hzz, mul_one]
  rw [heq] at hc
  exact ht.not_commute_mul hD hc.symm

omit [Finite G] in
theorem mul_mul_mul_mul_cancel_of_isTriangle (hD : IsOddTransp D) {x w y : G}
    (ht : IsTriangle D x w y) (a : G) : x * y * (x * y * a) = a := by
  rw [← mul_assoc (x * y), ht.uv_mul_self hD, one_mul]

theorem mul_mul_pow_mem_DalphaStar (hC : HypothesisC D) {x w y : G}
    (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) :
    x * y * (x * y * w) ^ n ∈ DalphaStar D hC.alpha := by
  obtain ⟨-, -, -, -, -, heD⟩ := ht.third_kind hC.setup.oddT hC.setup.normal hn hord
  have hxH : x ∈ Halpha D hC.alpha := Subgroup.subset_closure hx
  have hyH : y ∈ Halpha D hC.alpha := Subgroup.subset_closure hy
  have hwH : w ∈ Halpha D hC.alpha := Subgroup.subset_closure hw
  have hxyH : x * y ∈ Halpha D hC.alpha := Subgroup.mul_mem _ hxH hyH
  have hzH : (x * y * w) ^ n ∈ Halpha D hC.alpha :=
    Subgroup.pow_mem _ (Subgroup.mul_mem _ hxyH hwH) n
  have heH : x * y * (x * y * w) ^ n ∈ Halpha D hC.alpha :=
    Subgroup.mul_mem _ hxyH hzH
  have heα : x * y * (x * y * w) ^ n ∉ hC.alpha := by
    intro he
    obtain ⟨β, hβ, hwβ⟩ := hw
    exact not_commute_mul_mul_pow hC.setup.oddT hC.setup.normal ht hn hord
      ((mem_Dalpha_iff.mp hβ).2.2.2 _ he w hwβ)
  have hcent := CFSG.OddTranspositions.Halpha_le_centralizer D hC.alpha heH
  have hcommd : Commute hC.d (x * y * (x * y * w) ^ n) :=
    Subgroup.mem_centralizer_iff.mp hcent hC.d hC.d_mem_alpha
  rcases mem_block_or_DalphaStar_of_commute hC (mem_blockClass_self hC.alpha)
      hC.d_mem_alpha heD hcommd with he | he
  · exact absurd he heα
  · exact he

theorem mem_block_or_mem_DalphaStar_of_isTriangle (hC : HypothesisC D) {ζ : Set G}
    (hζ : ζ ∈ blockClass hC.alpha) {x w y z : G} (ht : IsTriangle D x w y) (hzζ : z ∈ ζ)
    (hzx : Commute z x) (hzy : Commute z y) (hzw : Commute z w) :
    (x ∈ ζ ∧ y ∈ ζ ∧ w ∈ ζ) ∨
      (x ∈ DalphaStar D ζ ∧ y ∈ DalphaStar D ζ ∧ w ∈ DalphaStar D ζ) := by
  have hx' : x ∈ ζ ∨ x ∈ DalphaStar D ζ :=
    mem_block_or_DalphaStar_of_commute hC hζ hzζ ht.1 hzx
  have hy' : y ∈ ζ ∨ y ∈ DalphaStar D ζ :=
    mem_block_or_DalphaStar_of_commute hC hζ hzζ ht.2.1 hzy
  have hw' : w ∈ ζ ∨ w ∈ DalphaStar D ζ :=
    mem_block_or_DalphaStar_of_commute hC hζ hzζ ht.2.2.1 hzw
  have hcommDS : ∀ a ∈ ζ, ∀ b ∈ DalphaStar D ζ, Commute a b :=
    fun _ ha _ hb => commute_of_mem_of_mem_DalphaStar ha hb
  by_cases hall : x ∈ DalphaStar D ζ ∧ y ∈ DalphaStar D ζ ∧ w ∈ DalphaStar D ζ
  · exact Or.inr hall
  · left
    have hsome : x ∈ ζ ∨ y ∈ ζ ∨ w ∈ ζ := by
      rcases hx' with hxζ | hxS
      · exact Or.inl hxζ
      rcases hy' with hyζ | hyS
      · exact Or.inr (Or.inl hyζ)
      rcases hw' with hwζ | hwS
      · exact Or.inr (Or.inr hwζ)
      exact absurd ⟨hxS, hyS, hwS⟩ hall
    have hwζ : w ∈ ζ := by
      rcases hsome with hxζ | hyζ | hwζ
      · by_contra hwζ
        exact ht.2.2.2.2.2.1 (hcommDS x hxζ w (hw'.resolve_left hwζ))
      · by_contra hwζ
        exact ht.2.2.2.2.2.2 (hcommDS y hyζ w (hw'.resolve_left hwζ))
      · exact hwζ
    have hxζ : x ∈ ζ := by
      by_cases hxζ : x ∈ ζ
      · exact hxζ
      · exact absurd (hcommDS w hwζ x (hx'.resolve_left hxζ)).symm ht.2.2.2.2.2.1
    have hyζ : y ∈ ζ := by
      by_cases hyζ : y ∈ ζ
      · exact hyζ
      · exact absurd (hcommDS w hwζ y (hy'.resolve_left hyζ)).symm ht.2.2.2.2.2.2
    exact ⟨hxζ, hyζ, hwζ⟩

omit [Finite G] in
theorem mem_Halpha_and_commute_of_pow_mem {ζ : Set G}
    {x w y : G} (hxS : x ∈ DalphaStar D ζ) (hyS : y ∈ DalphaStar D ζ)
    (hwS : w ∈ DalphaStar D ζ) {n : ℕ} (hzζ : (x * y * w) ^ n ∈ ζ) :
    (x * y * w) ^ n ∈ Halpha D ζ ∧
      ∀ d ∈ DalphaStar D ζ, Commute ((x * y * w) ^ n) d := by
  refine ⟨?_, ?_⟩
  · have hxywH : x * y * w ∈ Halpha D ζ :=
      Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.subset_closure hxS) (Subgroup.subset_closure hyS))
        (Subgroup.subset_closure hwS)
    exact Subgroup.pow_mem _ hxywH n
  · exact fun d hd => commute_of_mem_of_mem_DalphaStar hzζ hd

theorem exists_mem_blockClass_of_pow_mem (hC : HypothesisC D)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) (hz : (x * y * w) ^ n ∈ D) :
    ∃ β ∈ blockClass hC.alpha, x ∈ β ∧ y ∈ β ∧ w ∈ β ∧ (x * y * w) ^ n ∈ β := by
  obtain ⟨hzz, -, hzx, hzy, hzw, -⟩ := ht.third_kind hC.setup.oddT hC.setup.normal hn hord
  obtain ⟨ζ, hζ, hzζ⟩ :=
    exists_mem_blockClass_of_mem hC.setup.isClass hC.isBlock_alpha hz
  rcases mem_block_or_mem_DalphaStar_of_isTriangle hC hζ ht hzζ hzx hzy hzw with
    ⟨hxζ, hyζ, hwζ⟩ | ⟨hxS, hyS, hwS⟩
  · exact ⟨ζ, hζ, hxζ, hyζ, hwζ, hzζ⟩
  · exfalso
    obtain ⟨hzH, hzcomm⟩ := mem_Halpha_and_commute_of_pow_mem hxS hyS hwS hzζ
    have hzN : (x * y * w) ^ n ∈ fibreSubgroup D ζ :=
      mem_fibreSubgroup_of_forall_commute hC hne hζ hzH hzcomm hzz
    have hxyN : x * y ∈ fibreSubgroup D ζ :=
      mul_mem_fibreSubgroup_of_commute hC hζ hxS hyS ht.2.2.2.2.1
    have hw2 : w * w = 1 := hC.setup.oddT.mul_self_eq_one ht.2.2.1
    exact (notMem_fibreSubgroup hC hne hζ hwS)
      (CFSG.GroupTheory.mem_of_mul_pow_mem_of_conj_mem hxyN
        (conj_mem_fibreSubgroup D ζ (Subgroup.subset_closure hwS) hxyN) hw2 hn hzN)

end CFSG.OddTranspositions.PartThree.EightEight

end
