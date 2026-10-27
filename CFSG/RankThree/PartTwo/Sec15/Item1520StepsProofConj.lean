module

public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofTools
public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

namespace Proof1520

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_zpow_mul_of_mem {A L : Subgroup G} {c : G} (hcA : c ∈ A)
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) {a : G} (ha : a ∈ A)
    (haL : a ∈ Subgroup.zpowers c ⊔ L) : ∃ j : ℤ, ∃ l ∈ A, l ∈ L ∧ a = c ^ j * l := by
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun l hl =>
        (Subgroup.mem_centralizer_singleton_iff.mp (hLc hl))))
  have ha' : a ∈ (Subgroup.zpowers c : Set G) * (L : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN]
    exact haL
  obtain ⟨_, hj, l, hl, rfl⟩ := ha'
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hj
  have hlA : l ∈ A := by
    have : l = (c ^ j)⁻¹ * (c ^ j * l) := by group
    rw [this]
    exact A.mul_mem (A.inv_mem (A.zpow_mem hcA j)) ha
  exact ⟨j, l, hlA, hl, rfl⟩

omit [Finite G] in
theorem mem_normalizer_of_mem_normalizer_subgroupOf {A L : Subgroup G} {c : G} (hcA : c ∈ A)
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hAle : A ≤ Subgroup.zpowers c ⊔ L)
    {w : ↥L} (hw : w ∈ Subgroup.normalizer ((A.subgroupOf L : Subgroup ↥L) : Set ↥L)) :
    (w : G) ∈ Subgroup.normalizer (A : Set G) := by
  have key : ∀ v : ↥L, v ∈ Subgroup.normalizer ((A.subgroupOf L : Subgroup ↥L) : Set ↥L) →
      ∀ a ∈ A, (v : G) * a * (v : G)⁻¹ ∈ A := by
    intro v hv a ha
    obtain ⟨j, l, hlA, hlL, rfl⟩ := exists_zpow_mul_of_mem hcA hLc ha (hAle ha)
    have hvl : v * ⟨l, hlL⟩ * v⁻¹ ∈ A.subgroupOf L :=
      (Subgroup.mem_normalizer_iff.mp hv _).mp (Subgroup.mem_subgroupOf.mpr hlA)
    have hvl' : (v : G) * l * (v : G)⁻¹ ∈ A := Subgroup.mem_subgroupOf.mp hvl
    have hvc : (v : G) * c = c * v :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hLc v.2))
    have hvcj : (v : G) * c ^ j = c ^ j * v := ((Commute.zpow_right hvc j))
    have : (v : G) * (c ^ j * l) * (v : G)⁻¹ = c ^ j * ((v : G) * l * (v : G)⁻¹) := by
      rw [← mul_assoc, hvcj]
      group
    rw [this]
    exact A.mul_mem (A.zpow_mem hcA j) hvl'
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · exact key w hw a
  · intro ha
    have := key w⁻¹ (inv_mem hw) _ ha
    simpa [mul_assoc] using this

end Proof1520

open Proof1520

theorem step1522Conj_of (h1517 : Step1517R) (h138 : Item138N) (hT : KS1522TorusMeet)
    (hH : KS1522HessTrans) : Step1522Conj := by
  intro G _ _ A c L h Y hctx p P hP a haA hac
  obtain ⟨m, hm1, hisoL, h9, -, -, h9AL, hAle⟩ := config_of h1517 h138 h hctx hP
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := h.toSec13Data.le_centralizer
  have hp : p.Prime := hP.1
  have hPL : P ≤ L := hP.2.2.2.2.2.1.1.2
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := hP.2.2.2.2.2.1.1.1.1.2.2
  obtain ⟨k, f, hfA, hfL, rfl⟩ := exists_zpow_mul_of_mem hcA hLc haA (hAle haA)
  have hf1 : (⟨f, hfL⟩ : ↥L) ≠ 1 := by
    intro h1
    apply hac
    have hf : f = 1 := congrArg Subtype.val h1
    rw [hf, mul_one]
    exact Subgroup.zpow_mem_zpowers c k
  set E : Subgroup ↥L := A.subgroupOf L with hE
  have hEab : CFSG.Assembly.IsElemAbelian 3 E :=
    isElemAbelian_subgroupOf L h.toSec13Data.isElemAbelian
  have hE9 : Nat.card ↥E = 9 := by
    rw [hE, ← Subgroup.inf_subgroupOf_right, card_subgroupOf_inf, h9AL]
  set P' : Subgroup ↥L := P.subgroupOf L with hP'
  have hP'ab : CFSG.Assembly.IsElemAbelian p P' := isElemAbelian_subgroupOf L hP.2.2.2.1
  have hP'card : Nat.card ↥P' = p ^ 2 := by
    rw [hP', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv, hP.2.2.2.2.1]
  have hEN : E ≤ Subgroup.normalizer (P' : Set ↥L) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hP', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (hAP (Subgroup.mem_subgroupOf.mp he)) (x : G)
  obtain ⟨z, hzE, hz1, hzC⟩ := hT ↥L m hm1 hisoL p hp hP.2.1 P' hP'ab hP'card E hEab hE9 hEN
  obtain ⟨w, hwN, hwfz⟩ := hH ↥L m hm1 hisoL h9 E hEab hE9 ⟨f, hfL⟩
    (Subgroup.mem_subgroupOf.mpr hfA) z hzE hf1 hz1
  have hwA : ((w : ↥L) : G) ∈ Subgroup.normalizer (A : Set G) :=
    mem_normalizer_of_mem_normalizer_subgroupOf hcA hLc hAle hwN
  refine ⟨((w : ↥L) : G)⁻¹, inv_mem hwA, ?_⟩
  have hwf : (w : G) * f * (w : G)⁻¹ = (z : G) := congrArg Subtype.val hwfz
  have hwc : Commute (w : G) (c ^ k) :=
    Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hLc w.2)) k
  rintro _ ⟨x, hxP, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  rw [Set.mem_singleton_iff] at hb
  subst hb
  have hxL : x ∈ L := hPL hxP
  have hzx : (z : G) * x = x * (z : G) := by
    have := Subgroup.mem_centralizer_iff.mp hzC ⟨x, hxL⟩ (Subgroup.mem_subgroupOf.mpr hxP)
    exact (congrArg Subtype.val this).symm
  have hcx : c ^ k * x = x * c ^ k :=
    (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp (hLc hxL)).symm k).eq
  have hcf : c ^ k * f = (w : G)⁻¹ * (c ^ k * (z : G)) * (w : G) := by
    have hf' : f = (w : G)⁻¹ * (z : G) * (w : G) := by
      rw [← hwf]
      group
    have hwc' : (w : G)⁻¹ * c ^ k = c ^ k * (w : G)⁻¹ := hwc.inv_left.eq
    rw [hf', ← mul_assoc, ← mul_assoc, ← hwc', mul_assoc, mul_assoc, mul_assoc, mul_assoc]
  have hczx : c ^ k * (z : G) * x = x * (c ^ k * (z : G)) := by
    rw [mul_assoc, hzx, ← mul_assoc, hcx, mul_assoc]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rw [hcf]
  calc (w : G)⁻¹ * (c ^ k * (z : G)) * (w : G) * ((w : G)⁻¹ * x * (w : G))
      = (w : G)⁻¹ * (c ^ k * (z : G) * x) * (w : G) := by group
    _ = (w : G)⁻¹ * (x * (c ^ k * (z : G))) * (w : G) := by rw [hczx]
    _ = ((w : G)⁻¹ * x * (w : G)) * ((w : G)⁻¹ * (c ^ k * (z : G)) * (w : G)) := by group

end CFSG.RankThree.PartTwo.Sec15
