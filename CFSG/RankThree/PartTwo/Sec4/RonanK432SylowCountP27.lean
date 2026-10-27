module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

theorem card_center_eq_three_of_card_27 {P : Type} [Group P] (hP : Nat.card P = 27)
    (hna : ∃ a b : P, a * b ≠ b * a) : Nat.card (Subgroup.center P) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  obtain ⟨k, hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow (p := 3) (n := 3)
    (by rw [hP]; norm_num) (by norm_num)
  have hdvd : Nat.card (Subgroup.center P) ∣ 27 := hP ▸ Subgroup.card_subgroup_dvd_card _
  rw [hk] at hdvd ⊢
  have hk3 : k ≤ 3 := by
    by_contra h
    push Not at h
    have h4 : 3 ^ 4 ∣ 3 ^ k := pow_dvd_pow 3 h
    have := h4.trans hdvd
    norm_num at this
  obtain ⟨a, b, hab⟩ := hna
  interval_cases k
  · rfl
  · exfalso
    have hq : Nat.card (P ⧸ Subgroup.center P) = 3 := by
      have h1 := Subgroup.card_mul_index (Subgroup.center P)
      rw [hk, hP] at h1
      rw [← Subgroup.index_eq_card]
      omega
    haveI : IsCyclic (P ⧸ Subgroup.center P) := isCyclic_of_prime_card hq
    exact hab ((isMulCommutative_of_isCyclic_quotient_center_self P).is_comm.comm a b)
  · exfalso
    have htop : Subgroup.center P = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hk, hP]; norm_num)
    have hb : b ∈ Subgroup.center P := htop ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.mp hb a)

theorem exists_commutator_data {P : Type} [Group P] (hP : Nat.card P = 27)
    (hna : ∃ a b : P, a * b ≠ b * a) (x y : P) :
    ∃ c : P, (∀ g : P, g * c = c * g) ∧ c ^ 3 = 1 ∧ y * x = x * y * c := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  have hZ := card_center_eq_three_of_card_27 hP hna
  have hq : Nat.card (P ⧸ Subgroup.center P) = 3 ^ 2 := by
    have h1 := Subgroup.card_mul_index (Subgroup.center P)
    rw [hZ, hP] at h1
    rw [← Subgroup.index_eq_card]
    omega
  have hcomm := (IsPGroup.isMulCommutative_of_card_eq_prime_sq hq).is_comm.comm
  have hmem : (x * y)⁻¹ * (y * x) ∈ Subgroup.center P := by
    have := hcomm (QuotientGroup.mk x) (QuotientGroup.mk y)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at this
    exact this
  refine ⟨(x * y)⁻¹ * (y * x), fun g => (Subgroup.mem_center_iff.mp hmem g), ?_, by group⟩
  have h3 : (⟨(x * y)⁻¹ * (y * x), hmem⟩ : Subgroup.center P) ^ 3 = 1 := by
    have := pow_card_eq_one' (G := Subgroup.center P) (x := ⟨(x * y)⁻¹ * (y * x), hmem⟩)
    rwa [hZ] at this
  exact congrArg Subtype.val h3

theorem mul_pow_three_of_commutator {P : Type} [Group P] {x y c : P} (hc : ∀ g : P, g * c = c * g)
    (hyx : y * x = x * y * c) : (x * y) ^ 3 = x ^ 3 * y ^ 3 * c ^ 3 := by
  have hcx : c * x = x * c := (hc x).symm
  have hcy : c * y = y * c := (hc y).symm
  have hcy3 : y * (c * c * c) = c * c * c * y := by
    have := (Commute.pow_right (hc y) 3).eq
    rwa [pow_three'] at this
  calc (x * y) ^ 3 = x * (y * x) * (y * x) * y := by rw [pow_three']; group
    _ = x * (x * y * c) * (x * y * c) * y := by rw [hyx]
    _ = x * x * y * (c * x) * y * c * y := by group
    _ = x * x * y * (x * c) * y * c * y := by rw [hcx]
    _ = x * x * (y * x) * (c * y) * c * y := by group
    _ = x * x * (x * y * c) * (y * c) * c * y := by rw [hyx, hcy]
    _ = x * x * x * y * (c * y) * c * c * y := by group
    _ = x * x * x * y * (y * c) * c * c * y := by rw [hcy]
    _ = x * x * x * y * y * (c * c * c * y) := by group
    _ = x * x * x * y * y * (y * (c * c * c)) := by rw [hcy3]
    _ = x ^ 3 * y ^ 3 * c ^ 3 := by rw [pow_three' x, pow_three' y, pow_three' c]; group

theorem mul_pow_three_of_card_27 {P : Type} [Group P] (hP : Nat.card P = 27)
    (hna : ∃ a b : P, a * b ≠ b * a) (x y : P) : (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  obtain ⟨c, hc, hc3, hyx⟩ := exists_commutator_data hP hna x y
  rw [mul_pow_three_of_commutator hc hyx, hc3, mul_one]

theorem pow_three_mem_center_of_card_27 {P : Type} [Group P] (hP : Nat.card P = 27)
    (hna : ∃ a b : P, a * b ≠ b * a) (x : P) : x ^ 3 ∈ Subgroup.center P := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨c, hc, hc3, hyx⟩ := exists_commutator_data hP hna x y
  have h1 : y * x * y⁻¹ = x * c := by
    calc y * x * y⁻¹ = x * y * c * y⁻¹ := by rw [hyx]
      _ = x * (y * c * y⁻¹) := by group
      _ = x * (c * y * y⁻¹) := by rw [hc y]
      _ = x * c := by group
  have h2 : y * x ^ 3 * y⁻¹ = x ^ 3 := by
    calc y * x ^ 3 * y⁻¹ = (y * x * y⁻¹) ^ 3 := (conj_pow).symm
      _ = (x * c) ^ 3 := by rw [h1]
      _ = x ^ 3 * c ^ 3 := mul_pow_three_of_card_27 hP hna x c
      _ = x ^ 3 := by rw [hc3, mul_one]
  calc y * x ^ 3 = (y * x ^ 3 * y⁻¹) * y := by group
    _ = x ^ 3 * y := by rw [h2]

theorem card_pow_three_eq_one_of_card_27 {P : Type} [Group P] (hP : Nat.card P = 27)
    (hna : ∃ a b : P, a * b ≠ b * a) :
    Nat.card {x : P // x ^ 3 = 1} = 9 ∨ Nat.card {x : P // x ^ 3 = 1} = 27 := by
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  let φ : P →* P := MonoidHom.mk' (fun x => x ^ 3) (mul_pow_three_of_card_27 hP hna)
  have hker : Nat.card φ.ker = Nat.card {x : P // x ^ 3 = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => MonoidHom.mem_ker)
  have hrange : φ.range ≤ Subgroup.center P := by
    rintro _ ⟨x, rfl⟩
    exact pow_three_mem_center_of_card_27 hP hna x
  have hdvd : Nat.card φ.range ∣ 3 :=
    (card_center_eq_three_of_card_27 hP hna) ▸ Subgroup.card_dvd_of_le hrange
  have hmul := Subgroup.card_ker_mul_card_range φ
  rw [hP] at hmul
  rw [← hker]
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
  · right
    rw [h] at hmul
    omega
  · left
    rw [h] at hmul
    omega

end CFSG.RankThree.PartTwo.Sec4.RonanK432
