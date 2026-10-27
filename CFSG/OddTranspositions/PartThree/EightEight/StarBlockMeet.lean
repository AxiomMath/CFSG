module

public import CFSG.OddTranspositions.PartThree.EightEight.StarConj

import CFSG.OddTranspositions.PartThree.EightFive.Transitive
import CFSG.OddTranspositions.PartThree.EightSeven
import CFSG.OddTranspositions.SixSevenLocalStep
import CFSG.GroupTheory.CardSupInf
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.OddTranspositions.BlockAction2
import CFSG.OddTranspositions.CommutatorSize
import CFSG.OddTranspositions.WidthOne

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem commute_of_mem_of_mem_conjOrbit (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {ρ : Set G} (hρ : ρ ∈ blockClass hC.alpha)
    {a a' b : G} (ha : a ∈ ρ)
    (ha'O : a' ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x) (hane : a' ≠ a)
    (haa' : Commute a a') (hb : b ∈ ρ) : Commute a' b := by
  classical
  let z : G := (x * y * w) ^ n
  obtain ⟨hxC, -, -, -⟩ := thirdKind_mem_centSet hC.setup ht hn hord
  have ha'C : a' ∈ centSet D z := conjOrbit_subset_centSet hC.setup.normal hxC ha'O
  obtain ⟨σ, hσ, ha'σ⟩ :=
    exists_mem_blockClass_of_mem hC.setup.isClass hC.isBlock_alpha ha'C.1
  have ha'ρ : a' ∉ ρ := by
    intro h
    exact (not_commute_of_mem_of_mem h86 h87 hC hrad hO4 hF hne hρ ha h hane.symm) haa'
  have hσρ : σ ≠ ρ := by
    intro h
    exact ha'ρ (h ▸ ha'σ)
  have hρDσ : ρ ∈ Dalpha D σ :=
    mem_Dalpha_of_commute_mem hC.setup.normal hC.setup.oddT hC.isBlock_alpha hσ hρ hσρ
      ha'σ ha haa'.symm
  exact (mem_Dalpha_iff.mp hρDσ).2.2.2 a' ha'σ b hb

theorem mem_Dalpha_iff_commute (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {ρ σ : Set G} (hρ : ρ ∈ blockClass hC.alpha) (hσ : σ ∈ blockClass hC.alpha) {a b : G}
    (ha : a ∈ ρ) (hb : b ∈ σ) (hab : a ≠ b) : σ ∈ Dalpha D ρ ↔ Commute a b := by
  constructor
  · intro h
    exact (mem_Dalpha_iff.mp h).2.2.2 a ha b hb
  · intro hcomm
    have hσρ : σ ≠ ρ := by
      intro h
      exact (not_commute_of_mem_of_mem h86 h87 hC hrad hO4 hF hne hρ ha (h ▸ hb) hab) hcomm
    exact mem_Dalpha_of_commute_mem hC.setup.normal hC.setup.oddT hC.isBlock_alpha hρ hσ
      hσρ.symm ha hb hcomm

theorem eq_of_mem_of_mem_conjOrbit (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {ρ : Set G} (hρ : ρ ∈ blockClass hC.alpha) {a b : G}
    (ha : a ∈ ρ) (hb : b ∈ ρ) (haO : a ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x)
    (hbO : b ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x) : a = b := by
  classical
  let z : G := (x * y * w) ^ n
  obtain ⟨hxC, -, -, -⟩ := thirdKind_mem_centSet hC.setup ht hn hord
  by_contra hab
  obtain ⟨a', ha'O, ha'ne, haa', -⟩ :=
    exists_setOf_commute_mem_conjOrbit_eq h86 h87 hC hrad hO4 hF hne ht hn hord haO
  have hbC : b ∈ centSet D z := conjOrbit_subset_centSet hC.setup.normal hxC hbO
  have hcomm_a'b : Commute a' b :=
    commute_of_mem_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn hord hρ ha ha'O
      ha'ne haa' hb
  have hcomm_ba : Commute b a :=
    (commute_iff_of_commute_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn hord
      haO ha'O haa' hbC).mpr hcomm_a'b.symm
  exact (not_commute_of_mem_of_mem h86 h87 hC hrad hO4 hF hne hρ ha hb hab) hcomm_ba.symm

theorem exists_conjOrbit_pow_eq_mul_mul (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {a : G}
    (haO : a ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x) :
    ∃ a' e : G, a' ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x ∧
      e ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x ∧ a' ≠ a ∧ e ≠ a ∧
      Commute a a' ∧ Commute a e ∧ (x * y * w) ^ n = a * a' * e := by
  classical
  let z : G := (x * y * w) ^ n
  obtain ⟨hxC, -, -, -⟩ := thirdKind_mem_centSet hC.setup ht hn hord
  obtain ⟨a', ha'O, ha'ne, haa', -⟩ :=
    exists_setOf_commute_mem_conjOrbit_eq h86 h87 hC hrad hO4 hF hne ht hn hord haO
  obtain ⟨heO, hea⟩ := mul_mul_pow_mem_conjOrbit_and_commute h86 h87 hC hrad hO4 hF hne ht hn
    hord haO ha'O ha'ne haa'
  have hea_ne := (mul_mul_pow_ne_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn hord haO
    ha'O).1
  have ha2 : a * a = 1 :=
    hC.setup.oddT.mul_self_eq_one (conjOrbit_subset_centSet hC.setup.normal hxC haO).1
  have ha'2 : a' * a' = 1 :=
    hC.setup.oddT.mul_self_eq_one (conjOrbit_subset_centSet hC.setup.normal hxC ha'O).1
  have haa'2 : (a * a') * (a * a') = 1 := by
    calc (a * a') * (a * a') = a * (a' * a) * a' := by group
      _ = a * (a * a') * a' := by rw [haa'.eq]
      _ = (a * a) * (a' * a') := by group
      _ = 1 := by rw [ha2, ha'2, mul_one]
  refine ⟨a', a * a' * z, ha'O, heO, ha'ne, hea_ne, haa', hea, ?_⟩
  calc z = (a * a') * (a * a') * z := by rw [haa'2, one_mul]
    _ = a * a' * (a * a' * z) := by group

theorem pow_mul_mul_inv_eq_of_mem (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {ρ : Set G} (hρ : ρ ∈ blockClass hC.alpha) {a : G}
    (ha : a ∈ ρ) (haO : a ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x) {r : G}
    (hr : r ∈ ρ) : (x * y * w) ^ n * r * ((x * y * w) ^ n)⁻¹ = a * r * a⁻¹ := by
  classical
  let z : G := (x * y * w) ^ n
  obtain ⟨a', e, ha'O, heO, ha'ne, hea_ne, haa', hea, hz_eq⟩ :=
    exists_conjOrbit_pow_eq_mul_mul h86 h87 hC hrad hO4 hF hne ht hn hord haO
  have hz_eq' : z = a * a' * e := hz_eq
  have ha'ρ : a' ∉ ρ := by
    intro h
    exact ha'ne (eq_of_mem_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn hord hρ ha h
      haO ha'O).symm
  have heρ : e ∉ ρ := by
    intro h
    exact hea_ne (eq_of_mem_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn hord hρ ha h
      haO heO).symm
  have hcomm_a'r : Commute a' r :=
    commute_of_mem_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn hord hρ ha ha'O
      ha'ne haa' hr
  have hcomm_er : Commute e r :=
    commute_of_mem_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn hord hρ ha heO
      hea_ne hea hr
  have h1 : a' * r * a'⁻¹ = r := hcomm_a'r.mul_inv_cancel
  have h2 : e * r * e⁻¹ = r := hcomm_er.mul_inv_cancel
  change z * r * z⁻¹ = a * r * a⁻¹
  calc z * r * z⁻¹ = (a * a' * e) * r * (a * a' * e)⁻¹ := by rw [hz_eq']
    _ = a * (a' * (e * r * e⁻¹) * a'⁻¹) * a⁻¹ := by group
    _ = a * (a' * r * a'⁻¹) * a⁻¹ := by rw [h2]
    _ = a * r * a⁻¹ := by rw [h1]

theorem eq_of_mem_of_commute_pow (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {ρ : Set G} (hρ : ρ ∈ blockClass hC.alpha) {a : G}
    (ha : a ∈ ρ) (haO : a ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x) {r : G}
    (hr : r ∈ ρ) (hrz : Commute r ((x * y * w) ^ n)) : r = a := by
  classical
  let z : G := (x * y * w) ^ n
  by_contra hra
  have hzr : z * r * z⁻¹ = r := hrz.symm.mul_inv_cancel
  have har : a * r * a⁻¹ = r := by
    rw [← pow_mul_mul_inv_eq_of_mem h86 h87 hC hrad hO4 hF hne ht hn hord hρ ha haO hr, hzr]
  have hcomm : Commute a r := by
    rw [commute_iff_eq]
    have h := congrArg (fun t => t * a) har
    simpa [mul_assoc, inv_mul_cancel] using h
  exact (not_commute_of_mem_of_mem h86 h87 hC hrad hO4 hF hne hρ ha hr
    (fun h : a = r => hra h.symm)) hcomm

end CFSG.OddTranspositions.PartThree.EightEight
