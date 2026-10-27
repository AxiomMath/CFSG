module

public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Center
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.M11Order
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.Quasithin.F420

open CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.ClassicalOrders Matrix
open scoped LinearAlgebra.Projectivization

theorem card_of_statedPSL_two_two {X : Type} [Group X] {n : ℕ}
    (h : StatedClassicalModel X .PSL 2 2 n) : Nat.card X = 2 ^ n * (4 ^ n - 1) := by
  obtain ⟨⟨-, hf, -, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, card_statedProj_statedSL (by norm_num : 1 ≤ 2), hK]
  have hgcd : Nat.gcd 2 (2 ^ n - 1) = 1 := by
    have hodd : Odd (2 ^ n - 1) := by
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have h2 : Even (2 ^ n) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
      obtain ⟨m, hm⟩ := h2
      exact ⟨m - 1, by omega⟩
    exact (Nat.coprime_two_left.mpr hodd)
  have h4 : (2 ^ n) ^ 2 = 4 ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [hgcd, Nat.div_one]
  simp [h4]

theorem two_mul_card_of_statedPSL_two_odd {X : Type} [Group X] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (h : StatedClassicalModel X .PSL 2 q 1) : 2 * Nat.card X = q * (q ^ 2 - 1) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, card_statedProj_statedSL (by norm_num : 1 ≤ 2), hK]
  simp only [pow_one, Finset.Icc_self, Finset.prod_singleton,
    show 2 * (2 - 1) / 2 = 1 from rfl]
  have hodd : Odd q := hq.odd_of_ne_two hq2
  have hq1 : 1 ≤ q := hq.one_lt.le
  have hgcd : Nat.gcd 2 (q - 1) = 2 := by
    obtain ⟨m, hm⟩ := hodd
    rw [hm, Nat.add_sub_cancel]
    exact Nat.gcd_eq_left (dvd_mul_right 2 m)
  have hdvd : 2 ∣ q * (q ^ 2 - 1) := by
    obtain ⟨m, hm⟩ := hodd
    refine Dvd.dvd.mul_left ?_ q
    refine ⟨2 * m * m + 2 * m, ?_⟩
    rw [hm]
    have : (2 * m + 1) ^ 2 = 2 * (2 * m * m + 2 * m) + 1 := by ring
    omega
  rw [hgcd]
  exact Nat.mul_div_cancel' hdvd

theorem card_statedSL_three_three : Nat.card (StatedSL 3 (ZMod 3)) = 5616 := by
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 3 (ZMod 3)).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod]
  decide

theorem card_of_l33 {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL 3 3 1 ∨ Nonempty (X ≃* ↥(StatedSL 3 (ZMod 3)))) :
    Nat.card X = 5616 := by
  rcases h with ⟨-, K, _, _, hK, ⟨e⟩⟩ | h
  · rw [Nat.card_congr e.toEquiv, card_statedProj_statedSL (by norm_num : 1 ≤ 3), hK]
    decide
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, card_statedSL_three_three]

theorem card_of_m11 {X : Type} [Group X]
    (h : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) : Nat.card X = 7920 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Semidihedral.GL2Recognition.card_nativeM11

theorem card_of_l42 {X : Type} [Group X] (h : StatedClassicalModel X .PSL 4 2 1) :
    Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two h

theorem card_of_l52 {X : Type} [Group X] (h : StatedClassicalModel X .PSL 5 2 1) :
    Nat.card X = 9999360 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two h

theorem card_of_u33 {X : Type} [Group X] (h : StatedClassicalModel X .PSU 3 3 1) :
    Nat.card X = 6048 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three h

theorem center_eq_bot_of_mulEquiv' {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [← Subgroup.map_center_eq e.symm, h, Subgroup.map_bot]

theorem center_projectiveSpecialLinearGroup_eq_bot {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) : Subgroup.center (ProjectiveSpecialLinearGroup (Fin n) K) = ⊥ := by
  obtain ⟨-, -, -, -, hfaith, h2, -⟩ := CFSG.LinearGroups.linear_projective_action (K := K) hn
  have hcard : 3 ≤ Nat.card (ℙ K (Fin n → K)) := by
    rw [Projectivization.card_of_finrank K (Fin n → K) (by simp : Module.finrank K (Fin n → K) = n)]
    have hK : 2 ≤ Nat.card K := Finite.one_lt_card
    have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range n := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rw [Finset.mem_range]
      omega
    have hle := Finset.sum_le_sum_of_subset (f := fun i => Nat.card K ^ i) hsub
    rw [Finset.sum_pair (by norm_num)] at hle
    simp only [pow_zero, pow_one] at hle
    omega
  exact CFSG.GorensteinWalter.center_eq_bot_of_two_pretransitive h2 hcard

theorem center_eq_bot_of_statedPSL {X : Type} [Group X] {n p f : ℕ}
    (h : StatedClassicalModel X .PSL n p f) : Subgroup.center X = ⊥ := by
  obtain ⟨⟨-, -, hn, -, -⟩, K, _, _, -, ⟨e⟩⟩ := h
  exact center_eq_bot_of_mulEquiv' (e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm)
    (center_projectiveSpecialLinearGroup_eq_bot hn)

theorem center_statedSL_three_three : Subgroup.center (StatedSL 3 (ZMod 3)) = ⊥ := by
  refine center_eq_bot_of_mulEquiv' (specialLinearGroupEquivStatedSL 3 (ZMod 3)).symm ?_
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr1 : r = 1 := by
    rw [Fintype.card_fin] at hr
    have key : ∀ c : ZMod 3, c ^ 3 = 1 → c = 1 := by decide
    exact key r hr
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hA, hr1]
  simp [Matrix.one_apply]

end CFSG.Quasithin.F420
