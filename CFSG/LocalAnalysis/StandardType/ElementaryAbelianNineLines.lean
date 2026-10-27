module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.StandardType.ElementaryAbelianNine

@[expose] def line {H : Type*} [Group H] (a b : H) : Fin 4 → Subgroup H :=
  ![Subgroup.zpowers a, Subgroup.zpowers b, Subgroup.zpowers (a * b),
    Subgroup.zpowers (a * b ^ 2)]

theorem pow_mod_three_eq_of_cube_eq_one {G : Type*} [Group G] {x : G} (hx : x ^ 3 = 1)
    (i : ℕ) : x ^ i = x ^ (i % 3) := by
  have h : x ^ i = x ^ (i / 3 * 3) * x ^ (i % 3) := by
    rw [← pow_add, Nat.div_add_mod']
  rw [h, mul_comm (i / 3) 3, pow_mul, hx, one_pow, one_mul]

theorem zpowers_sq_eq_zpowers_of_cube_eq_one {G : Type*} [Group G] {x : G} (hx : x ^ 3 = 1) :
    Subgroup.zpowers (x ^ 2) = Subgroup.zpowers x := by
  have hx2 : x ^ 2 = x⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hx
  rw [hx2, Subgroup.zpowers_inv]

theorem zpowers_eq_of_mem_zpowers_of_cube_eq_one {G : Type*} [Group G] {x y : G}
    (hx : x ^ 3 = 1) (hx1 : x ≠ 1) (hy : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hyx : y ∈ Subgroup.zpowers x) : Subgroup.zpowers y = Subgroup.zpowers x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : orderOf x = 3 := orderOf_eq_prime (p := 3) hx hx1
  have hy3 : orderOf y = 3 := orderOf_eq_prime (p := 3) hy hy1
  haveI : Finite ↥(Subgroup.zpowers x) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hx3]; norm_num)
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyx) ?_
  simp [Nat.card_zpowers, hx3, hy3]

theorem exists_generators {H : Type*} [Group H] (hcomm : ∀ x y : H, x * y = y * x)
    (hexp : ∀ x : H, x ^ 3 = 1) (hcard : Nat.card H = 9) :
    ∃ a b : H, a ≠ 1 ∧ b ∉ Subgroup.zpowers a ∧ ∀ x : H, ∃ i j : ℕ, x = a ^ i * b ^ j := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : CommGroup H := { ‹Group H› with mul_comm := hcomm }
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hnt : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨a, ha⟩ := exists_ne (1 : H)
  have ha3 : orderOf a = 3 := orderOf_eq_prime (p := 3) (hexp a) ha
  have hacard : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, ha3]
  have hane : Subgroup.zpowers a ≠ ⊤ := by
    intro htop
    have h9 : Nat.card (Subgroup.zpowers a) = Nat.card H := by rw [htop, Subgroup.card_top]
    rw [hacard, hcard] at h9
    norm_num at h9
  obtain ⟨b, hb⟩ : ∃ b : H, b ∉ Subgroup.zpowers a := by
    by_contra h
    push Not at h
    exact hane ((Subgroup.eq_top_iff' (Subgroup.zpowers a)).mpr h)
  refine ⟨a, b, ha, hb, ?_⟩
  let S : Subgroup H := Subgroup.zpowers a ⊔ Subgroup.zpowers b
  have hlt : Subgroup.zpowers a < S := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    have hbS : b ∈ S := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
    rw [← heq] at hbS
    exact hb hbS
  have hcardS_gt : 3 < Nat.card S := by
    have h := Subgroup.card_lt_of_lt hlt
    rwa [hacard] at h
  have hdiv : Nat.card S ∣ 9 := by
    have h := Subgroup.card_subgroup_dvd_card S
    rwa [hcard] at h
  have hcardS : Nat.card S = 9 := by
    have hdiv' : Nat.card S ∣ 3 ^ 2 := by rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact hdiv
    obtain ⟨k, hk, hkS⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdiv'
    have hk2 : k = 2 := by
      have hgt := hcardS_gt
      rw [hkS] at hgt
      interval_cases k <;> first | rfl | (norm_num at hgt)
    rw [hk2] at hkS
    simpa using hkS
  have hS_top : S = ⊤ := Subgroup.eq_top_of_card_eq S (by rw [hcardS, hcard])
  intro x
  have hxS : x ∈ S := by rw [hS_top]; trivial
  rw [Subgroup.mem_sup] at hxS
  obtain ⟨y, hy, z, hz, hyz⟩ := hxS
  obtain ⟨mm, hmm⟩ := Subgroup.mem_zpowers_iff.mp hy
  obtain ⟨nn, hnn⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine ⟨(mm % 3).toNat, (nn % 3).toNat, ?_⟩
  have hm' : a ^ (mm % 3).toNat = y := by
    rw [← zpow_natCast a (mm % 3).toNat,
      Int.toNat_of_nonneg (Int.emod_nonneg mm (by norm_num : (3 : ℤ) ≠ 0)),
      ← zpow_eq_zpow_emod mm (by simpa using hexp a)]
    exact hmm
  have hn' : b ^ (nn % 3).toNat = z := by
    rw [← zpow_natCast b (nn % 3).toNat,
      Int.toNat_of_nonneg (Int.emod_nonneg nn (by norm_num : (3 : ℤ) ≠ 0)),
      ← zpow_eq_zpow_emod nn (by simpa using hexp b)]
    exact hnn
  rw [hm', hn']
  exact hyz.symm

theorem card_line {H : Type*} [Group H] (hexp : ∀ x : H, x ^ 3 = 1) {a b : H} (ha : a ≠ 1)
    (hb : b ∉ Subgroup.zpowers a) (k : Fin 4) : Nat.card (line a b k) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb1 : b ≠ 1 := fun h => hb (by simpa [h] using Subgroup.one_mem (Subgroup.zpowers a))
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hb
    rw [eq_inv_of_mul_eq_one_right h]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)
  have hab2 : a * b ^ 2 ≠ 1 := by
    intro h
    apply hb
    have hb2 : b ^ 2 = a⁻¹ := eq_inv_of_mul_eq_one_right h
    have hb2mem : b ^ 2 ∈ Subgroup.zpowers a := by
      rw [hb2]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)
    have hb4 : b = (b ^ 2) ^ 2 := by
      rw [← pow_mul, show (2 : ℕ) * 2 = 3 + 1 by norm_num, pow_add, hexp b, one_mul, pow_one]
    rw [hb4]
    exact Subgroup.pow_mem _ hb2mem 2
  have ho_a : orderOf a = 3 := orderOf_eq_prime (p := 3) (hexp a) ha
  have ho_b : orderOf b = 3 := orderOf_eq_prime (p := 3) (hexp b) hb1
  have ho_ab : orderOf (a * b) = 3 := orderOf_eq_prime (p := 3) (hexp (a * b)) hab1
  have ho_ab2 : orderOf (a * b ^ 2) = 3 := orderOf_eq_prime (p := 3) (hexp (a * b ^ 2)) hab2
  fin_cases k <;> simp [line, Nat.card_zpowers, ho_a, ho_b, ho_ab, ho_ab2]

theorem line_injective {H : Type*} [Group H] (hcomm : ∀ x y : H, x * y = y * x)
    (hexp : ∀ x : H, x ^ 3 = 1) {a b : H} (ha : a ≠ 1) (hb : b ∉ Subgroup.zpowers a) :
    Function.Injective (line a b) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : CommGroup H := { ‹Group H› with mul_comm := hcomm }
  have hb1 : b ≠ 1 := fun h => hb (by simpa [h] using Subgroup.one_mem (Subgroup.zpowers a))
  have ho_a : orderOf a = 3 := orderOf_eq_prime (p := 3) (hexp a) ha
  have ha_not_mem_b : a ∉ Subgroup.zpowers b := by
    intro hab
    have h_eq : Subgroup.zpowers a = Subgroup.zpowers b :=
      zpowers_eq_of_mem_zpowers_of_cube_eq_one (x := b) (y := a) (hexp b) hb1 (hexp a) ha hab
    exact hb (h_eq.symm ▸ Subgroup.mem_zpowers b)
  have hab_not_mem_a : a * b ∉ Subgroup.zpowers a := by
    intro h
    apply hb
    have hb_eq : b = a⁻¹ * (a * b) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    rw [hb_eq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) h
  have hab_not_mem_b : a * b ∉ Subgroup.zpowers b := by
    intro h
    apply ha_not_mem_b
    have ha_eq : a = (a * b) * b⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
    rw [ha_eq]
    exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ (Subgroup.mem_zpowers b))
  have hab2_not_mem_a : a * b ^ 2 ∉ Subgroup.zpowers a := by
    intro h
    apply hb
    have hb2mem : b ^ 2 ∈ Subgroup.zpowers a := by
      have hb2 : b ^ 2 = a⁻¹ * (a * b ^ 2) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      rw [hb2]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) h
    have hb4 : b = (b ^ 2) ^ 2 := by
      rw [← pow_mul, show (2 : ℕ) * 2 = 3 + 1 by norm_num, pow_add, hexp b, one_mul, pow_one]
    rw [hb4]
    exact Subgroup.pow_mem _ hb2mem 2
  have hab2_not_mem_b : a * b ^ 2 ∉ Subgroup.zpowers b := by
    intro h
    apply ha_not_mem_b
    have ha_eq : a = (a * b ^ 2) * (b ^ 2)⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
    rw [ha_eq]
    exact Subgroup.mul_mem _ h
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) 2))
  have h01 : line a b 0 ≠ line a b 1 := by
    intro h
    have hmem : b ∈ line a b 0 := by rw [h]; simpa [line] using Subgroup.mem_zpowers b
    exact hb (by simpa [line] using hmem)
  have h02 : line a b 0 ≠ line a b 2 := by
    intro h
    have hmem : a * b ∈ line a b 0 := by
      rw [h]; simpa [line] using Subgroup.mem_zpowers (a * b)
    exact hab_not_mem_a (by simpa [line] using hmem)
  have h03 : line a b 0 ≠ line a b 3 := by
    intro h
    have hmem : a * b ^ 2 ∈ line a b 0 := by
      rw [h]; simpa [line] using Subgroup.mem_zpowers (a * b ^ 2)
    exact hab2_not_mem_a (by simpa [line] using hmem)
  have h12 : line a b 1 ≠ line a b 2 := by
    intro h
    have hmem : a * b ∈ line a b 1 := by
      rw [h]; simpa [line] using Subgroup.mem_zpowers (a * b)
    exact hab_not_mem_b (by simpa [line] using hmem)
  have h13 : line a b 1 ≠ line a b 3 := by
    intro h
    have hmem : a * b ^ 2 ∈ line a b 1 := by
      rw [h]; simpa [line] using Subgroup.mem_zpowers (a * b ^ 2)
    exact hab2_not_mem_b (by simpa [line] using hmem)
  have h23 : line a b 2 ≠ line a b 3 := by
    intro h
    have hmem : a * b ^ 2 ∈ line a b 2 := by
      rw [h]; simpa [line] using Subgroup.mem_zpowers (a * b ^ 2)
    have hmem' : a * b ^ 2 ∈ Subgroup.zpowers (a * b) := by simpa [line] using hmem
    have hbmem : b ∈ Subgroup.zpowers (a * b) := by
      have hb_eq : b = (a * b ^ 2) * (a * b)⁻¹ := by
        rw [mul_inv, pow_two]
        simp [mul_assoc, mul_comm, mul_left_comm]
      have hmem'' : (a * b ^ 2) * (a * b)⁻¹ ∈ Subgroup.zpowers (a * b) :=
        Subgroup.mul_mem (Subgroup.zpowers (a * b)) hmem'
          (Subgroup.inv_mem (Subgroup.zpowers (a * b)) (Subgroup.mem_zpowers (a * b)))
      rw [← hb_eq] at hmem''
      exact hmem''
    have hamem : a ∈ Subgroup.zpowers (a * b) := by
      have ha_eq : a = (a * b) * b⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
      have hamem' : (a * b) * b⁻¹ ∈ Subgroup.zpowers (a * b) :=
        Subgroup.mul_mem (Subgroup.zpowers (a * b)) (Subgroup.mem_zpowers (a * b))
          (Subgroup.inv_mem (Subgroup.zpowers (a * b)) hbmem)
      rw [← ha_eq] at hamem'
      exact hamem'
    have hab1 : a * b ≠ 1 := fun hh => hab_not_mem_a (hh.symm ▸ Subgroup.one_mem _)
    have heq : Subgroup.zpowers a = Subgroup.zpowers (a * b) :=
      zpowers_eq_of_mem_zpowers_of_cube_eq_one (x := a * b) (y := a) (hexp (a * b)) hab1
        (hexp a) ha hamem
    exact hab_not_mem_a (heq.symm ▸ Subgroup.mem_zpowers (a * b))
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [line]

theorem exists_line_eq {H : Type*} [Group H] (hcomm : ∀ x y : H, x * y = y * x)
    (hexp : ∀ x : H, x ^ 3 = 1) {a b : H}
    (hgen : ∀ x : H, ∃ i j : ℕ, x = a ^ i * b ^ j) {M : Subgroup H} (hM : Nat.card M = 3) :
    ∃ k, M = line a b k := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : CommGroup H := { ‹Group H› with mul_comm := hcomm }
  haveI : Finite M := Nat.finite_of_card_ne_zero (by rw [hM]; norm_num)
  have hMne : M ≠ ⊥ :=
    (Subgroup.one_lt_card_iff_ne_bot M).mp (by rw [hM]; norm_num)
  obtain ⟨m, hm1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hMne
  have hm1' : (m : H) ≠ 1 := fun h => hm1 (Subtype.ext h)
  have hm3 : orderOf (m : H) = 3 := orderOf_eq_prime (p := 3) (hexp (m : H)) hm1'
  have hzm : Subgroup.zpowers (m : H) = M := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr m.2) ?_
    simp [hM, Nat.card_zpowers, hm3]
  obtain ⟨i, j, hmij⟩ := hgen (m : H)
  set r : ℕ := i % 3 with hr
  set s : ℕ := j % 3 with hs
  have hmrs : (m : H) = a ^ r * b ^ s := by
    rw [hmij, hr, hs, ← pow_mod_three_eq_of_cube_eq_one (hexp a) i,
      ← pow_mod_three_eq_of_cube_eq_one (hexp b) j]
  have hrlt : r < 3 := by rw [hr]; exact Nat.mod_lt i (by norm_num)
  have hslt : s < 3 := by rw [hs]; exact Nat.mod_lt j (by norm_num)
  interval_cases r <;> interval_cases s
  · exfalso
    exact hm1' (by rw [hmrs]; simp)
  · refine ⟨1, ?_⟩
    rw [← hzm, hmrs]
    simp [line]
  · refine ⟨1, ?_⟩
    rw [← hzm, hmrs]
    simp [line, zpowers_sq_eq_zpowers_of_cube_eq_one (hexp b)]
  · refine ⟨0, ?_⟩
    rw [← hzm, hmrs]
    simp [line]
  · refine ⟨2, ?_⟩
    rw [← hzm, hmrs]
    simp [line]
  · refine ⟨3, ?_⟩
    rw [← hzm, hmrs]
    simp [line]
  · refine ⟨0, ?_⟩
    rw [← hzm, hmrs]
    simp [line, zpowers_sq_eq_zpowers_of_cube_eq_one (hexp a)]
  · refine ⟨3, ?_⟩
    rw [← hzm, hmrs]
    simp only [pow_one]
    have h : a ^ 2 * b = (a * b ^ 2) ^ 2 := by
      rw [mul_pow]
      congr 1
      rw [← pow_mul, show (2 : ℕ) * 2 = 3 + 1 by norm_num, pow_add, hexp b, one_mul, pow_one]
    rw [h, zpowers_sq_eq_zpowers_of_cube_eq_one (hexp (a * b ^ 2))]
    simp [line]
  · refine ⟨2, ?_⟩
    rw [← hzm, hmrs]
    have h : a ^ 2 * b ^ 2 = (a * b) ^ 2 := (mul_pow a b 2).symm
    rw [h, zpowers_sq_eq_zpowers_of_cube_eq_one (hexp (a * b))]
    simp [line]

theorem line_facts {H : Type*} [Group H] (hcomm : ∀ x y : H, x * y = y * x)
    (hexp : ∀ x : H, x ^ 3 = 1) (hcard : Nat.card H = 9) {a b : H} (ha : a ≠ 1)
    (hb : b ∉ Subgroup.zpowers a) (hgen : ∀ x : H, ∃ i j : ℕ, x = a ^ i * b ^ j) :
    (∀ k, Nat.card (line a b k) = 3) ∧ Function.Injective (line a b) ∧
      ∀ M : Subgroup H, Nat.card M = 3 → ∃ k, M = line a b k :=
  ⟨card_line hexp ha hb, line_injective hcomm hexp ha hb, fun _ hM =>
    exists_line_eq hcomm hexp hgen hM⟩

end CFSG.StandardType.ElementaryAbelianNine
