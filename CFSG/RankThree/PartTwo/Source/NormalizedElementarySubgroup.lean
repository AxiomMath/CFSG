module

public import CFSG.Assembly.Defs
import CFSG.RankThree.PartTwo.Source.MinimalFaithfulCentralProduct
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
import CFSG.LieType.BorelTits.Basic

public section

open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Source

variable {G : Type*} [Group G]

@[expose] def omegaSubgroup (Y : Subgroup G) (hY : IsMulCommutative Y) (r : ℕ) :
    Subgroup G where
  carrier := {y | y ∈ Y ∧ y ^ r = 1}
  one_mem' := ⟨Y.one_mem, one_pow r⟩
  mul_mem' := by
    rintro a b ⟨haY, ha⟩ ⟨hbY, hb⟩
    refine ⟨Y.mul_mem haY hbY, ?_⟩
    have hab : Commute a b := congrArg Subtype.val (hY.is_comm.comm ⟨a, haY⟩ ⟨b, hbY⟩)
    rw [hab.mul_pow, ha, hb, one_mul]
  inv_mem' := by
    rintro a ⟨haY, ha⟩
    exact ⟨Y.inv_mem haY, by rw [inv_pow, ha, inv_one]⟩

theorem mem_normalizer_omegaSubgroup {Y : Subgroup G} (hY : IsMulCommutative Y) (r : ℕ) {g : G}
    (hg : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer (omegaSubgroup Y hY r : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hgY := Subgroup.mem_normalizer_iff.mp hg y
  constructor
  · rintro ⟨hyY, hy⟩
    exact ⟨hgY.mp hyY, by rw [conj_pow, hy, mul_one, mul_inv_cancel]⟩
  · rintro ⟨hyY, hy⟩
    refine ⟨hgY.mpr hyY, ?_⟩
    rw [conj_pow] at hy
    calc y ^ r = g⁻¹ * (g * y ^ r * g⁻¹) * g := by group
      _ = 1 := by rw [hy]; group

theorem exists_elementary_normalized [Finite G] {X N : Subgroup G} (hX1 : X ≠ ⊥)
    (hXs : Group.IsSolvable X) (hX3 : ¬ 3 ∣ Nat.card X) (hO2 : CFSG.Assembly.pCoreOf 2 X = ⊥)
    (hN : N ≤ Subgroup.normalizer (X : Set G)) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ ∃ Y : Subgroup G, Y ≠ ⊥ ∧ Y ≤ X ∧ IsMulCommutative Y ∧
      (∀ y ∈ Y, y ^ r = 1) ∧ IsPGroup r Y ∧ N ≤ Subgroup.normalizer (Y : Set G) := by
  classical
  obtain ⟨Y, ⟨hY1, hYX, hXY, hNY⟩, hmin⟩ := exists_minimal_subgroup
    (fun Y : Subgroup G => Y ≠ ⊥ ∧ Y ≤ X ∧ X ≤ Subgroup.normalizer (Y : Set G) ∧
      N ≤ Subgroup.normalizer (Y : Set G)) ⟨hX1, le_rfl, Subgroup.le_normalizer, hN⟩
  have := hXs
  have hYs : Group.IsSolvable Y :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hYX)
  have : Nontrivial Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hY1
  have hYc : IsMulCommutative Y := by
    have hlt := CFSG.commutator_lt_self_of_isSolvable Y
    have hcomm : ⁅Y, Y⁆ = ⊥ := by
      by_contra hne
      have hYY := hmin ⁅Y, Y⁆ hlt.le ⟨hne, hlt.le.trans hYX,
        fun x hx => mem_normalizer_commutator (hXY hx) (hXY hx),
        fun x hx => mem_normalizer_commutator (hNY hx) (hNY hx)⟩
      exact hlt.ne hYY
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have h := Subgroup.commutator_mem_commutator a.2 b.2
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  obtain ⟨r, hr, hrY⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card_iff_nontrivial.mpr this).ne'
  have : Fact r.Prime := ⟨hr⟩
  have hΩY : omegaSubgroup Y hYc r ≤ Y := fun y hy => hy.1
  have hΩ : omegaSubgroup Y hYc r = Y := by
    refine hmin (omegaSubgroup Y hYc r) hΩY ⟨?_, hΩY.trans hYX,
      fun x hx => mem_normalizer_omegaSubgroup hYc r (hXY hx),
      fun x hx => mem_normalizer_omegaSubgroup hYc r (hNY hx)⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' r hrY
    intro hbot
    have hgΩ : (g : G) ∈ omegaSubgroup Y hYc r := ⟨g.2, by
      rw [← Subgroup.coe_pow, ← hg, pow_orderOf_eq_one, Subgroup.coe_one]⟩
    rw [hbot, Subgroup.mem_bot] at hgΩ
    have : orderOf g = 1 := by
      rw [orderOf_eq_one_iff]
      exact Subtype.ext hgΩ
    rw [hg] at this
    exact hr.one_lt.ne' this
  have hYr : ∀ y ∈ Y, y ^ r = 1 := fun y hy => by
    rw [← hΩ] at hy
    exact hy.2
  have hYp : IsPGroup r Y := fun y => ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow,
    hYr _ y.2, Subgroup.coe_one])⟩
  have hr3 : r ≠ 3 := by
    rintro rfl
    exact hX3 (hrY.trans (Subgroup.card_dvd_of_le hYX))
  have hr2 : r ≠ 2 := by
    rintro rfl
    apply hY1
    have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hYX hXY hYp
    rw [eq_bot_iff]
    exact hle.trans (le_of_eq hO2)
  refine ⟨r, hr, ?_, Y, hY1, hYX, hYc, hYr, hYp, hNY⟩
  have := hr.two_le
  have h4 : r ≠ 4 := fun h => by rw [h] at hr; exact absurd hr (by decide)
  omega

end CFSG.RankThree.PartTwo.Source
