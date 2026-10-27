module

public import CFSG.RankThree.PartTwo.Sec18.Item187F5Pair
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.FixedPoints

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open scoped commutatorElement Pointwise

variable {V : Type} [Group V] [Finite V]

theorem two_pow_eq_sixteen_pow_of_mod_five {j : ℕ} (h : 2 ^ j % 5 = 1) :
    ∃ k : ℕ, 2 ^ j = 16 ^ k := by
  have hq : (16 : ℕ) ^ (j / 4) % 5 = 1 := by
    rw [Nat.pow_mod]; norm_num
  have key : 2 ^ j = 16 ^ (j / 4) * 2 ^ (j % 4) := by
    conv_lhs => rw [← Nat.div_add_mod j 4]
    rw [pow_add, pow_mul]
    norm_num
  have hr : j % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hmod : 2 ^ (j % 4) % 5 = 1 := by
    rw [key, Nat.mul_mod, hq, one_mul, Nat.mod_mod] at h
    exact h
  have h0 : j % 4 = 0 := by
    generalize j % 4 = r at hr hmod ⊢
    interval_cases r <;> simp_all
  exact ⟨j / 4, by rw [key, h0, pow_zero, mul_one]⟩

theorem mem_fix_zpowers_iff {g : MulAut V} {x : V} :
    x ∈ Fix (Subgroup.zpowers g) ↔ g x = x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact (FixedPoints.mem_subgroup _ _ _).mp h ⟨g, Subgroup.mem_zpowers g⟩
  · refine (FixedPoints.mem_subgroup _ _ _).mpr fun m => ?_
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp m.2
    have hx : x ∈ MulAction.fixedBy V g := by
      rw [MulAction.mem_fixedBy, MulAut.smul_def]; exact h
    have hk' := MulAction.mem_fixedBy_zpow hx k
    rw [MulAction.mem_fixedBy, MulAut.smul_def] at hk'
    show (m : MulAut V) • x = x
    rw [← hk, MulAut.smul_def]
    exact hk'

theorem card_V_eq_two_pow (hV : ∀ v : V, v * v = 1) : ∃ n : ℕ, Nat.card V = 2 ^ n := by
  have h2 : IsPGroup 2 V := fun v => ⟨1, by norm_num [pow_two, hV]⟩
  exact (IsPGroup.iff_card).mp h2

theorem index_fix_zpowers_eq_pow_sixteen (hV : ∀ v : V, v * v = 1) {y : MulAut V} {k : ℕ}
    (hy : y ^ 5 ^ k = 1) : ∃ j : ℕ, (Fix (Subgroup.zpowers y)).index = 16 ^ j := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨n, hn⟩ := card_V_eq_two_pow hV
  have hH : IsPGroup 5 (Subgroup.zpowers y) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp
      (orderOf_dvd_of_pow_eq_one hy)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hi])
  have hmod := IsPGroup.card_modEq_card_fixedPoints hH V
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers y) V) =
      Nat.card (Fix (Subgroup.zpowers y)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x =>
      (MulAction.mem_fixedPoints).trans (FixedPoints.mem_subgroup _ _ _).symm)
  rw [hfix] at hmod
  have hidx : Nat.card (Fix (Subgroup.zpowers y)) * (Fix (Subgroup.zpowers y)).index =
      Nat.card V := Subgroup.card_mul_index _
  have hcd : Nat.card (Fix (Subgroup.zpowers y)) ∣ 2 ^ n := by
    rw [← hn]; exact Dvd.intro _ hidx
  have hid : (Fix (Subgroup.zpowers y)).index ∣ 2 ^ n := by
    rw [← hn]; exact Dvd.intro_left _ hidx
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hcd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hid
  have hcop : Nat.Coprime 5 (Nat.card (Fix (Subgroup.zpowers y))) := by
    rw [ha]; exact Nat.Coprime.pow_right a (by norm_num)
  have h1 : (Fix (Subgroup.zpowers y)).index * Nat.card (Fix (Subgroup.zpowers y)) ≡
      1 * Nat.card (Fix (Subgroup.zpowers y)) [MOD 5] := by
    rw [mul_comm, hidx, one_mul]; exact hmod
  have h2 := Nat.ModEq.cancel_right_of_coprime hcop h1
  rw [hj] at h2
  have h3 : 2 ^ j % 5 = 1 := by
    unfold Nat.ModEq at h2; simpa using h2
  obtain ⟨k', hk'⟩ := two_pow_eq_sixteen_pow_of_mod_five h3
  exact ⟨k', by rw [hj, hk']⟩

theorem twentyfive_dvd_card_of_not_isCyclic {K : Subgroup (MulAut V)} (hK5 : IsPGroup 5 K)
    (hKnc : ¬ IsCyclic K) : 25 ∣ Nat.card K := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hK5
  rcases m with _ | _ | m
  · exfalso
    apply hKnc
    have : Subsingleton K := (Nat.card_eq_one_iff_unique.mp (by simpa using hm)).1
    infer_instance
  · exfalso
    exact hKnc (isCyclic_of_prime_card (p := 5) (by simpa using hm))
  · rw [hm]
    have := pow_dvd_pow 5 (show 2 ≤ m + 1 + 1 by omega)
    simpa using this

theorem sixteen_pow_eq_sixteen {j : ℕ} (h1 : 16 ^ j ≠ 1) (h2 : 16 ^ j < 2 ^ 8) :
    16 ^ j = 16 := by
  rcases j with _ | _ | j
  · exact absurd (pow_zero 16) h1
  · norm_num
  · exfalso
    have h3 : (2 : ℕ) ^ 8 ≤ 16 ^ (j + 1 + 1) := by
      calc (2 : ℕ) ^ 8 = 16 ^ 2 := by norm_num
        _ ≤ 16 ^ (j + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact absurd h2 (not_lt.mpr h3)

theorem card_fixedBy_mul_index (g : MulAut V) :
    Nat.card (MulAction.fixedBy V g) * (Fix (Subgroup.zpowers g)).index = Nat.card V := by
  have hc : Nat.card (Fix (Subgroup.zpowers g)) = Nat.card (MulAction.fixedBy V g) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [mem_fix_zpowers_iff, MulAction.mem_fixedBy, MulAut.smul_def])
  rw [← hc]
  exact Subgroup.card_mul_index _

theorem exists_two_pow_eight_of_five_group (hV : ∀ v : V, v * v = 1) {G : Subgroup (MulAut V)}
    (hG : IsPGroup 5 G) (h25 : 25 ∣ Nat.card G) :
    ∃ y ∈ G, 2 ^ 8 ≤ (Fix (Subgroup.zpowers y)).index := by
  classical
  by_contra hcon
  push Not at hcon
  have hV5 : ¬ 5 ∣ Nat.card V := by
    obtain ⟨n, hn⟩ := card_V_eq_two_pow hV
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h
    norm_num at this
  have h16 : ∀ g : G, g ≠ 1 → (Fix (Subgroup.zpowers (g : MulAut V))).index = 16 := by
    intro g hg
    obtain ⟨k, hk⟩ := hG g
    have hk' : (g : MulAut V) ^ 5 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    obtain ⟨j, hj⟩ := index_fix_zpowers_eq_pow_sixteen hV hk'
    have hne1 : (Fix (Subgroup.zpowers (g : MulAut V))).index ≠ 1 := by
      intro h1
      rw [Subgroup.index_eq_one, eq_top_iff] at h1
      apply hg
      apply Subtype.ext
      apply MulEquiv.ext
      intro x
      show (g : MulAut V) x = (1 : MulAut V) x
      rw [MulAut.one_apply]
      exact mem_fix_zpowers_iff.mp (h1 (Subgroup.mem_top x))
    have hlt := hcon (g : MulAut V) g.2
    rw [hj] at hne1 hlt ⊢
    exact sixteen_pow_eq_sixteen hne1 hlt
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype G := Fintype.ofFinite G
  haveI : ∀ g : G, Fintype (MulAction.fixedBy V g) := fun g => Fintype.ofFinite _
  haveI : Fintype (Quotient (MulAction.orbitRel G V)) := Fintype.ofFinite _
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G V
  simp only [← Nat.card_eq_fintype_card] at hB
  have hfb : ∀ g : G, MulAction.fixedBy V g = MulAction.fixedBy V (g : MulAut V) :=
    fun g => rfl
  have hpt : ∀ g : G, 16 * Nat.card (MulAction.fixedBy V g) =
      Nat.card V + if g = 1 then 15 * Nat.card V else 0 := by
    intro g
    rw [hfb g]
    by_cases hg : g = 1
    · rw [if_pos hg, hg]
      have h1 : MulAction.fixedBy V ((1 : G) : MulAut V) = Set.univ := by
        ext x; simp [MulAction.mem_fixedBy]
      rw [h1, Nat.card_univ]
      ring
    · rw [if_neg hg, add_zero]
      have hid := card_fixedBy_mul_index (g : MulAut V)
      rw [h16 g hg] at hid
      omega
  have hsum : 16 * ∑ g : G, Nat.card (MulAction.fixedBy V g) =
      Nat.card G * Nat.card V + 15 * Nat.card V := by
    rw [Finset.mul_sum]
    simp only [hpt, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
  rw [hB] at hsum
  obtain ⟨t, ht⟩ := h25
  have h1 : 25 ∣ Nat.card G * Nat.card V := ⟨t * Nat.card V, by rw [ht]; ring⟩
  have h2 : 25 ∣ 16 * (Nat.card (Quotient (MulAction.orbitRel G V)) * Nat.card G) :=
    ⟨16 * Nat.card (Quotient (MulAction.orbitRel G V)) * t, by rw [ht]; ring⟩
  rw [hsum] at h2
  have h3 : 25 ∣ 15 * Nat.card V := (Nat.dvd_add_right h1).mp h2
  have h4 : 5 ∣ Nat.card V := by omega
  exact hV5 h4

theorem abelian_case_sixteen (hV : ∀ v : V, v * v = 1) {K : Subgroup (MulAut V)}
    (hK5 : IsPGroup 5 K) (hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (hKnc : ¬ IsCyclic K)
    {e : MulAut V} (he : e * e = 1) (hinv : ∀ y ∈ K, e * y * e⁻¹ = y⁻¹) :
    2 ^ 8 ≤ (Fix (Subgroup.zpowers e)).index ^ 2 := by
  obtain ⟨y, hyK, hy⟩ :=
    exists_two_pow_eight_of_five_group hV hK5 (twentyfive_dvd_card_of_not_isCyclic hK5 hKnc)
  obtain ⟨k, hk⟩ := hK5 ⟨y, hyK⟩
  have hk' : y ^ 5 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hodd : Odd (orderOf y) :=
    Odd.of_dvd_nat (Odd.pow (⟨2, by norm_num⟩ : Odd 5)) (orderOf_dvd_of_pow_eq_one hk')
  exact le_trans hy (index_fix_zpowers_le_sq he (hinv y hyK) hodd)

end CFSG.RankThree.PartTwo.Sec18.Item187Proof

