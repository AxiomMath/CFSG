module

public import CFSG.Quasithin.Vol2.Ch11SecBL2UPSU

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Assembly.LowTwoRank

theorem exists_autOn_surjective {G : Type} [Group G] {Kp V : Subgroup G}
    (hKpN : Kp ≤ Subgroup.normalizer (V : Set G)) :
    ∃ f : ↥Kp →* ↥(autOn Kp V), Function.Surjective f :=
  ⟨((conjAct V).subgroupMap (Kp.subgroupOf (Subgroup.normalizer (V : Set G)))).comp
      (Subgroup.subgroupOfEquivOfLe hKpN).symm.toMonoidHom,
    (MonoidHom.subgroupMap_surjective _ _).comp (Subgroup.subgroupOfEquivOfLe hKpN).symm.surjective⟩

theorem card_psl_eq_ordA {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin n) K) = ordA (n - 1) (Nat.card K) := by
  rw [Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj n K).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by omega), ordA,
    Nat.sub_add_cancel (by omega : 1 ≤ n), mul_comm (n - 1) n]

theorem card_SL_four_two : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod]
  decide

theorem card_statedSp_two_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K) = 720 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK]
  decide

theorem ordBC_two_eq {n : ℕ} (hn : 1 ≤ n) :
    ordBC 2 (2 ^ n) = (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) := by
  have hgcd : Nat.gcd 2 (2 ^ n - 1) = 1 := by
    have : Odd (2 ^ n - 1) :=
      Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
    exact Nat.coprime_two_left.mpr this
  rw [ordBC, show 2 * 2 = 4 from rfl, prod_Icc_one_two, hgcd, Nat.div_one,
    show 2 * 1 = 2 from rfl, show 2 * 2 = 4 from rfl]

theorem ordBC_two_ne_ordTwistedA_two {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ordBC 2 (2 ^ n) ≠ ordTwistedA 2 (2 ^ k) := by
  intro h
  have hq : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hX := gcd_dvd_U3 (2 ^ k) hq
  set d := Nat.gcd 3 (2 ^ k + 1) with hd
  set X := ((2 ^ k) ^ 2 - 1) * ((2 ^ k) ^ 3 + 1) with hXdef
  have hd3 : d ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left _ (by norm_num)
  set A := ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1) with hA
  have hAodd : Odd A := Odd.mul (CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))
    (CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))
  have hXodd : Odd (X / d) := Odd.of_dvd_nat
    (Odd.mul (CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))
      (CFSG.Timmesfeld.Orders.odd_pow_add_one (by omega) (by norm_num)))
    (Nat.div_dvd_of_dvd hX)
  have h0 : (2 ^ n) ^ 4 * A = (2 ^ k) ^ 3 * (X / d) := by
    rw [← ordBC_two_eq hn, ← Nat.mul_div_assoc _ hX, ← ordTwistedA_two_eq hq]
    exact h
  have h1 : 2 ^ (4 * n) * A = 2 ^ (3 * k) * (X / d) := by
    rw [show 2 ^ (4 * n) = (2 ^ n) ^ 4 by rw [mul_comm, pow_mul],
      show 2 ^ (3 * k) = (2 ^ k) ^ 3 by rw [mul_comm, pow_mul]]
    exact h0
  have h2 := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hAodd hXodd h1
  rw [h2] at h1
  have hAX : A = X / d := Nat.eq_of_mul_eq_mul_left (by positivity) h1
  obtain ⟨j, rfl, rfl⟩ : ∃ j, n = 3 * j ∧ k = 4 * j := ⟨n / 3, by omega, by omega⟩
  set x := 2 ^ (2 * j) with hx
  have hx4 : 4 ≤ x := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * j) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hqn : 2 ^ (3 * j) = 2 ^ (3 * j) := rfl
  have e1 : (2 ^ (3 * j)) ^ 2 = x ^ 3 := by rw [hx, ← pow_mul, ← pow_mul]; ring_nf
  have e2 : (2 ^ (3 * j)) ^ 4 = x ^ 6 := by rw [hx, ← pow_mul, ← pow_mul]; ring_nf
  have e3 : (2 ^ (4 * j)) ^ 2 = x ^ 4 := by rw [hx, ← pow_mul, ← pow_mul]; ring_nf
  have e4 : (2 ^ (4 * j)) ^ 3 = x ^ 6 := by rw [hx, ← pow_mul, ← pow_mul]; ring_nf
  rw [hA, e1, e2] at hAX
  rw [hXdef, e3, e4] at hAX
  have hdA : d * ((x ^ 3 - 1) * (x ^ 6 - 1)) = (x ^ 4 - 1) * (x ^ 6 + 1) := by
    rw [hAX]
    exact Nat.mul_div_cancel' (by rw [← e3, ← e4]; exact hX)
  have h1 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h2' : 1 ≤ x ^ 6 := Nat.one_le_pow _ _ (by omega)
  have h3' : 1 ≤ x ^ 4 := Nat.one_le_pow _ _ (by omega)
  have hlt : 3 * ((x ^ 3 - 1) * (x ^ 6 - 1)) < (x ^ 4 - 1) * (x ^ 6 + 1) := by
    zify [h1, h2', h3']
    have hx' : (4 : ℤ) ≤ x := by exact_mod_cast hx4
    nlinarith [mul_le_mul_of_nonneg_left hx' (by positivity : (0 : ℤ) ≤ (x : ℤ) ^ 8),
      mul_le_mul_of_nonneg_left hx' (by positivity : (0 : ℤ) ≤ (x : ℤ) ^ 9)]
  have hle : d * ((x ^ 3 - 1) * (x ^ 6 - 1)) ≤ 3 * ((x ^ 3 - 1) * (x ^ 6 - 1)) :=
    Nat.mul_le_mul_right _ hd3
  omega

end CFSG.Quasithin.Vol2.Ch11.SecB
