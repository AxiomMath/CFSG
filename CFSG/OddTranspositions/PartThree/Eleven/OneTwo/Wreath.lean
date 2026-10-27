module

public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Hyp
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Pair
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.Quandle
public import CFSG.OddTranspositions.PartThree.EightFive.KBarSetup
public import Certificates.Certificate2326
public import CFSG.OddTranspositions.WreathBase
public import CFSG.OddTranspositions.WreathBaseMinimal
public import CFSG.OddTranspositions.PartThree.Ten.SetupPerfect
public import CFSG.Timmesfeld.Bridge.OddTranspGenL2
public import CFSG.Certificates.CosetTableShort

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

section Wreath

private theorem card_l2Wreath (f n : ℕ) :
    Nat.card (L2Wreath f n) =
      Nat.card (CFSG.Theory.Comparator.PSL2Model f) ^ n * n.factorial := by
  rw [SemidirectProduct.card, Nat.card_fun, Nat.card_fin, Nat.card_perm, Nat.card_fin]

private theorem commutator_le_of_index_le_two {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    [K.Normal] (h : K.index ≤ 2) : commutator G ≤ K := by
  have hpos : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (by omega : K.index = 1 ∨ K.index = 2) with h1 | h2
  · rw [Subgroup.index_eq_one] at h1
    rw [h1]
    exact le_top
  · rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
    have hcard : Nat.card (G ⧸ K) = 2 := by rw [← Subgroup.index_eq_card]; exact h2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : IsCyclic (G ⧸ K) := isCyclic_of_prime_card hcard
    infer_instance

theorem card_l2Wreath_two_two : Nat.card (L2Wreath 2 2) = 7200 := by
  rw [card_l2Wreath, CFSG.Timmesfeld.Bridge.OddTransp.card_psl2Model (by norm_num)]
  norm_num [Nat.factorial]

theorem dvd_card_l2Wreath {f n : ℕ} (hf : 2 ≤ f) (hn : n = 3 ∨ n = 4) :
    128 ∣ Nat.card (L2Wreath f n) := by
  rcases hn with rfl | rfl
  · have hgoal : Nat.card (L2Wreath f 3) =
        (2 ^ f * ((2 ^ f) ^ 2 - 1)) ^ 3 * 6 := by
      rw [card_l2Wreath, CFSG.Timmesfeld.Bridge.OddTransp.card_psl2Model (by omega)]
      norm_num [Nat.factorial]
    rw [hgoal]
    have hcube : (2 ^ f) ^ 3 ∣ (2 ^ f * ((2 ^ f) ^ 2 - 1)) ^ 3 :=
      pow_dvd_pow_of_dvd (dvd_mul_right _ _) 3
    have hmul : (2 ^ f) ^ 3 * 2 ^ 1 ∣ (2 ^ f * ((2 ^ f) ^ 2 - 1)) ^ 3 * 6 :=
      mul_dvd_mul hcube (by norm_num : 2 ^ 1 ∣ 6)
    have h128 : 128 ∣ (2 ^ f) ^ 3 * 2 ^ 1 := by
      have hval : (2 ^ f) ^ 3 * 2 ^ 1 = 2 ^ (3 * f + 1) := by
        rw [← pow_mul, ← pow_add, show f * 3 + 1 = 3 * f + 1 by ring]
      rw [hval]
      simpa using pow_dvd_pow (2 : ℕ) (by omega : 7 ≤ 3 * f + 1)
    exact dvd_trans h128 hmul
  · have hgoal : Nat.card (L2Wreath f 4) =
        (2 ^ f * ((2 ^ f) ^ 2 - 1)) ^ 4 * 24 := by
      rw [card_l2Wreath, CFSG.Timmesfeld.Bridge.OddTransp.card_psl2Model (by omega)]
      norm_num [Nat.factorial]
    rw [hgoal]
    have hfour : (2 ^ f) ^ 4 ∣ (2 ^ f * ((2 ^ f) ^ 2 - 1)) ^ 4 :=
      pow_dvd_pow_of_dvd (dvd_mul_right _ _) 4
    have hmul : (2 ^ f) ^ 4 * 2 ^ 3 ∣ (2 ^ f * ((2 ^ f) ^ 2 - 1)) ^ 4 * 24 :=
      mul_dvd_mul hfour (by norm_num : 2 ^ 3 ∣ 24)
    have h128 : 128 ∣ (2 ^ f) ^ 4 * 2 ^ 3 := by
      have hval : (2 ^ f) ^ 4 * 2 ^ 3 = 2 ^ (4 * f + 3) := by
        rw [← pow_mul, ← pow_add, show f * 4 + 3 = 4 * f + 3 by ring]
      rw [hval]
      simpa using pow_dvd_pow (2 : ℕ) (by omega : 7 ≤ 4 * f + 3)
    exact dvd_trans h128 hmul

theorem not_isSimpleGroup_of_index_le_two_l2Wreath {Y : Type} [Group Y] {f : ℕ} (hf : 2 ≤ f)
    (φ : Y ≃* L2Wreath f 2) (M : Subgroup Y) (hM : M.Normal) (hidx : M.index ≤ 2) :
    ¬ IsSimpleGroup M := by
  classical
  haveI : Finite Y := Finite.of_injective φ φ.injective
  haveI : M.Normal := hM
  let B' : Subgroup Y := (l2WreathBase f 2).map φ.symm.toMonoidHom
  have hbase := CFSG.OddTranspositions.base_isMinimalNormal f 2 hf (by norm_num)
  have hBbaseNormal : (l2WreathBase f 2).Normal := hbase.1
  have hB'normal : B'.Normal := hBbaseNormal.map φ.symm.toMonoidHom φ.symm.surjective
  have hBne : l2WreathBase f 2 ≠ ⊥ := hbase.2.1
  have hB'ne : B' ≠ ⊥ := by
    change (l2WreathBase f 2).map φ.symm.toMonoidHom ≠ ⊥
    intro hbot
    exact hBne ((Subgroup.map_eq_bot_iff_of_injective (l2WreathBase f 2)
      φ.symm.injective).mp hbot)
  have hB'perf : ⁅B', B'⁆ = B' := by
    have hBperf : ⁅l2WreathBase f 2, l2WreathBase f 2⁆ = l2WreathBase f 2 :=
      commutator_l2WreathBase hf 2
    have hmap := Subgroup.map_commutator (H₁ := l2WreathBase f 2)
      (H₂ := l2WreathBase f 2) φ.symm.toMonoidHom
    rw [hBperf] at hmap
    exact hmap.symm
  have hB'le : B' ≤ M := by
    have hcomm : commutator Y ≤ M := commutator_le_of_index_le_two hidx
    calc B' = ⁅B', B'⁆ := hB'perf.symm
      _ ≤ commutator Y := Subgroup.commutator_mono le_top le_top
      _ ≤ M := hcomm
  have hB'notSimple : ¬ IsSimpleGroup B' := by
    have heq : l2WreathBase f 2 ≃* B' :=
      Subgroup.equivMapOfInjective (l2WreathBase f 2) φ.symm.toMonoidHom φ.symm.injective
    exact fun hs => CFSG.OddTranspositions.l2WreathBase_not_isSimpleGroup hf (by norm_num)
      ((MulEquiv.isSimpleGroup_congr heq).mpr hs)
  intro hsimple
  have hB'subNormal : (B'.subgroupOf M).Normal := hB'normal.subgroupOf M
  rcases (Subgroup.isSimpleGroup_iff.mp hsimple).2 B' hB'le hB'subNormal with h | h
  · exact hB'ne h
  · exact hB'notSimple (h ▸ hsimple)

end Wreath

end CFSG.OddTranspositions.PartThree
