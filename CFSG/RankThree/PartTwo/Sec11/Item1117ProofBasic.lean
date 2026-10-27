module

public import CFSG.RankThree.PartTwo.Sec11.Item1125Proof
public import CFSG.RankThree.PartTwo.Sec11.Skeleton
import CFSG.RankThree.PartTwo.Sec11.Item1116Proof
import CFSG.RankThree.PartTwo.Sec11.Item1123Proof
import CFSG.RankThree.PartTwo.Sec11.RFactsK

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace Item1117Proof

section Elementary

variable {G : Type*} [Group G]

theorem mul_pow_three_eq {y u z : G} (hu : u * y = y * z * u) (hzy : z * y = y * z)
    (hzu : z * u = u * z) (hz3 : z ^ 3 = 1) (hu3 : u ^ 3 = 1) : (y * u) ^ 3 = y ^ 3 := by
  have h1 : y⁻¹ * u * y = z * u := by
    calc y⁻¹ * u * y = y⁻¹ * (u * y) := by group
      _ = y⁻¹ * (y * z * u) := by rw [hu]
      _ = z * u := by group
  have hzy' : y⁻¹ * z * y = z := by
    calc y⁻¹ * z * y = y⁻¹ * (z * y) := by group
      _ = y⁻¹ * (y * z) := by rw [hzy]
      _ = z := by group
  have h2 : y⁻¹ * y⁻¹ * u * y * y = z * (z * u) := by
    calc y⁻¹ * y⁻¹ * u * y * y = y⁻¹ * (y⁻¹ * u * y) * y := by group
      _ = y⁻¹ * (z * u) * y := by rw [h1]
      _ = (y⁻¹ * z * y) * (y⁻¹ * u * y) := by group
      _ = z * (z * u) := by rw [hzy', h1]
  have e : (y * u) ^ 3 = y ^ 3 * ((y⁻¹ * y⁻¹ * u * y * y) * (y⁻¹ * u * y) * u) := by
    rw [pow_three, pow_three]
    group
  rw [e, h2, h1]
  have h3 : z * (z * u) * (z * u) * u = z ^ 3 * u ^ 3 := by
    have hzu2 : (z * u) * (z * u) = z * z * (u * u) := by
      calc (z * u) * (z * u) = z * (u * z) * u := by group
        _ = z * (z * u) * u := by rw [hzu]
        _ = z * z * (u * u) := by group
    calc z * (z * u) * (z * u) * u = z * ((z * u) * (z * u)) * u := by group
      _ = z * (z * z * (u * u)) * u := by rw [hzu2]
      _ = z ^ 3 * u ^ 3 := by rw [pow_three, pow_three]; group
  rw [h3, hz3, hu3, one_mul, mul_one]

theorem three_pow_dvd_three_mul_of_dvd {j m : ℕ} (hm : 1 ≤ m) (h : 3 ^ j ∣ m ^ 3 - 1) :
    3 ^ j ∣ 3 * (m - 1) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  have h3 : 3 ∣ m ^ 3 - 1 := (dvd_pow_self 3 hj.ne').trans h
  have hm1 : m % 3 = 1 := by
    have hm3 : m ^ 3 % 3 = m % 3 := by
      have : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
      rw [Nat.pow_mod]
      interval_cases (m % 3) <;> rfl
    have hpos : 1 ≤ m ^ 3 := Nat.one_le_pow _ _ hm
    omega
  obtain ⟨t, rfl⟩ : ∃ t, m = 3 * t + 1 := ⟨m / 3, by omega⟩
  have e : (3 * t + 1) ^ 3 - 1 = 3 * (3 * t + 1 - 1) * (3 * t ^ 2 + 3 * t + 1) := by
    have : (3 * t + 1) ^ 3 = 3 * (3 * t) * (3 * t ^ 2 + 3 * t + 1) + 1 := by ring
    rw [this, Nat.add_sub_cancel, show 3 * t + 1 - 1 = 3 * t by omega]
  rw [e] at h
  have hcop : Nat.Coprime (3 ^ j) (3 * t ^ 2 + 3 * t + 1) := by
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    omega
  exact hcop.dvd_of_dvd_mul_right h

theorem conj_pow_three_eq_of_pow_three_eq_one {u y : G} (hu3 : u ^ 3 = 1)
    (hy : ∃ k : ℕ, y ^ 3 ^ k = 1) (huy : u * y * u⁻¹ ∈ Subgroup.zpowers y) :
    u * y ^ 3 * u⁻¹ = y ^ 3 := by
  obtain ⟨k, hk⟩ := hy
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  have hpos : 0 < orderOf y := by rw [hj]; positivity
  obtain ⟨m, hm⟩ : ∃ m : ℕ, u * y * u⁻¹ = y ^ m := by
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp huy
    refine ⟨(z % (orderOf y : ℤ)).toNat, ?_⟩
    have e1 : (((z % (orderOf y : ℤ)).toNat : ℕ) : ℤ) = z % (orderOf y : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hpos.ne'))
    rw [← hz, ← zpow_natCast, e1]
    exact zpow_eq_zpow_emod' z (pow_orderOf_eq_one y)
  have hconj : ∀ n : ℕ, u ^ n * y * (u ^ n)⁻¹ = y ^ (m ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc u ^ (n + 1) * y * (u ^ (n + 1))⁻¹ = u * (u ^ n * y * (u ^ n)⁻¹) * u⁻¹ := by
            rw [pow_succ']
            group
        _ = (u * y * u⁻¹) ^ (m ^ n) := by rw [ih, conj_pow]
        _ = y ^ (m ^ (n + 1)) := by rw [hm, ← pow_mul, pow_succ', mul_comm]
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  ·
    have hy1 : y = 1 := by
      have h1 : u * y * u⁻¹ = 1 := by rw [hm, pow_zero]
      calc y = u⁻¹ * (u * y * u⁻¹) * u := by group
        _ = 1 := by rw [h1]; group
    rw [hy1, one_pow, mul_one, mul_inv_cancel]
  have h3 := hconj 3
  rw [hu3, one_mul, inv_one, mul_one] at h3
  have hdvd : orderOf y ∣ m ^ 3 - 1 := by
    apply orderOf_dvd_of_pow_eq_one
    have h1 : 1 ≤ m ^ 3 := Nat.one_le_pow _ _ hm0
    have e : y ^ (m ^ 3 - 1) * y = y := by
      rw [← pow_succ, Nat.sub_add_cancel h1, ← h3]
    calc y ^ (m ^ 3 - 1) = y ^ (m ^ 3 - 1) * y * y⁻¹ := by group
      _ = 1 := by rw [e, mul_inv_cancel]
  rw [hj] at hdvd
  have h4 := three_pow_dvd_three_mul_of_dvd hm0 hdvd
  rw [← hj] at h4
  have h5 : y ^ (3 * (m - 1)) = 1 := orderOf_dvd_iff_pow_eq_one.mp h4
  calc u * y ^ 3 * u⁻¹ = (u * y * u⁻¹) ^ 3 := by rw [conj_pow]
    _ = y ^ (3 * (m - 1)) * y ^ 3 := by
      rw [hm, ← pow_mul, ← pow_add]
      congr 1
      have : 1 ≤ m := hm0
      rw [mul_comm m 3]
      omega
    _ = y ^ 3 := by rw [h5, one_mul]

theorem mem_zpowers_of_pow_three_eq_one [Finite G] {x d z : G} (hd : d ∈ Subgroup.zpowers x)
    (hd3 : orderOf d = 3) (hz : z ∈ Subgroup.zpowers x) (hz3 : z ^ 3 = 1) :
    z ∈ Subgroup.zpowers d := by
  set S := Subgroup.zpowers x with hS
  set D := (Subgroup.zpowers d).subgroupOf S with hD
  set Z := (Subgroup.zpowers z).subgroupOf S with hZ
  have hDcard : Nat.card D = 3 := by
    rw [hD, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hd)).toEquiv,
      Nat.card_zpowers, hd3]
  have hZcard : Nat.card Z ∣ 3 := by
    rw [hZ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hz)).toEquiv,
      Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hz3
  have hle : Z ≤ D := (IsCyclic.subgroup_le_iff_card_dvd).mpr (hDcard ▸ hZcard)
  have hzZ : (⟨z, hz⟩ : S) ∈ Z := Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers z)
  exact Subgroup.mem_subgroupOf.mp (hle hzZ)

theorem closure_pair_eq_of_mem {c d e : G} (hcd : c * d = d * c) (hc3 : c ^ 3 = 1)
    (hd3 : d ^ 3 = 1) (he : e ∈ Subgroup.closure ({c, d} : Set G))
    (hed : e ∉ Subgroup.zpowers d) :
    Subgroup.closure ({e, d} : Set G) = Subgroup.closure {c, d} := by
  obtain ⟨i, j, hi, -, rfl⟩ := KFacts.exists_pow_mul_pow_of_mem_closure_pair hcd hc3 hd3 he
  have hdD : d ∈ Subgroup.closure ({c ^ i * d ^ j, d} : Set G) := Subgroup.subset_closure (by simp)
  have heD : c ^ i * d ^ j ∈ Subgroup.closure ({c ^ i * d ^ j, d} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hci : c ^ i ∈ Subgroup.closure ({c ^ i * d ^ j, d} : Set G) := by
    have h1 := Subgroup.mul_mem _ heD (Subgroup.inv_mem _ (Subgroup.pow_mem _ hdD j))
    rwa [mul_inv_cancel_right] at h1
  have hcD : c ∈ Subgroup.closure ({c ^ i * d ^ j, d} : Set G) := by
    interval_cases i
    · exfalso
      apply hed
      rw [pow_zero, one_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) j
    · simpa only [pow_one] using hci
    · have h2 := Subgroup.pow_mem _ hci 2
      have e : (c ^ 2) ^ 2 = c := by
        rw [← pow_mul]
        calc c ^ (2 * 2) = c ^ 3 * c := by rw [← pow_succ]
          _ = c := by rw [hc3, one_mul]
      rwa [e] at h2
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact he
    · exact Subgroup.subset_closure (by simp)
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hcD
    · exact hdD

theorem normalizer_le_normalizer_commutator (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer ((⁅P, P⁆ : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hn ⊢
  rw [Subgroup.map_commutator, hn]

theorem mem_normalizer_closure_pair [Finite G] {t e d : G}
    (he : t * e * t⁻¹ ∈ Subgroup.closure ({e, d} : Set G))
    (hd : t * d * t⁻¹ ∈ Subgroup.closure ({e, d} : Set G)) :
    t ∈ Subgroup.normalizer ((Subgroup.closure ({e, d} : Set G) : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have hle : Subgroup.closure ({e, d} : Set G) ≤
      (Subgroup.closure ({e, d} : Set G)).comap (MulAut.conj t).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact he
    · exact hd
  exact hle hz

end Elementary

section Data


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem R_eq_closure (h : Sec11Data G A c L a R Y d x s r g)
    (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) :
    R = Subgroup.closure {a, x, c} := by
  rw [(h.of_closure_eq hrs).R_eq]
  have hsc' : s ∈ Subgroup.zpowers c := by rw [← hsc]; exact Subgroup.mem_zpowers s
  have hcs' : c ∈ Subgroup.zpowers s := by rw [hsc]; exact Subgroup.mem_zpowers c
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hsc'
  · rw [Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hcs'

theorem d_mem_A (h : Sec11Data G A c L a R Y d x s r g) : d ∈ A := by
  have hd : d ∈ A ⊓ L := by
    rw [h.inf_eq]
    exact Subgroup.mem_zpowers d
  exact hd.1

theorem d_mem_zpowers_x (h : Sec11Data G A c L a R Y d x s r g) : d ∈ Subgroup.zpowers x := by
  have hd : d ∈ A ⊓ L := by
    rw [h.inf_eq]
    exact Subgroup.mem_zpowers d
  rw [← h.inf_L_eq]
  exact ⟨le_R_of_hyp91 h.toHyp91 hd.1, hd.2⟩

theorem orderOf_d (h : Sec11Data G A c L a R Y d x s r g) : orderOf d = 3 :=
  orderOf_eq_prime (h.mem_partTwoF.1.2 d (d_mem_A h))
    (h.toSec11Std.not_mem_facts h.inf_eq h.closure_eq).2.2

theorem commute_of_mem_A (h : Sec11Data G A c L a R Y d x s r g) {u v : G} (hu : u ∈ A)
    (hv : v ∈ A) : u * v = v * u :=
  congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)

theorem pow_three_of_mem_A (h : Sec11Data G A c L a R Y d x s r g) {u : G} (hu : u ∈ A) :
    u ^ 3 = 1 :=
  h.mem_partTwoF.1.2 u hu

theorem R_le_centralizer_c (h : Sec11Data G A c L a R Y d x s r g) :
    R ≤ Subgroup.centralizer ({c} : Set G) :=
  le_centralizer_of_le_normalizer_zpowers
    (orderOf_eq_prime (h.mem_partTwoF.1.2 c h.mem_A) h.ne_one) h.isSylowOf.isPGroup
    h.isSylowOf.le

theorem conj_a_x_mem (h : Sec11Data G A c L a R Y d x s r g) :
    a * x * a⁻¹ ∈ Subgroup.zpowers x := by
  have haR : a ∈ R := le_R_of_hyp91 h.toHyp91 h.a_mem
  have hN := Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer haR, h.toHyp81.a_mem_normalizer⟩
  rw [h.inf_L_eq] at hN
  exact (Subgroup.mem_normalizer_iff.mp hN x).mp (Subgroup.mem_zpowers x)

theorem x_pow_eq_one (h : Sec11Data G A c L a R Y d x s r g) : ∃ k : ℕ, x ^ 3 ^ k = 1 :=
  Item1116Proof.exists_pow_eq_one_of_mem h (Item1116Proof.mem_R h).2.1

theorem conj_a_x_cube (h : Sec11Data G A c L a R Y d x s r g) :
    a * x ^ 3 * a⁻¹ = x ^ 3 :=
  conj_pow_three_eq_of_pow_three_eq_one (pow_three_of_mem_A h h.a_mem) (x_pow_eq_one h)
    (conj_a_x_mem h)

theorem commutator_a_x_mem (h : Sec11Data G A c L a R Y d x s r g) :
    a * x * a⁻¹ * x⁻¹ ∈ Subgroup.zpowers d := by
  have hp := conj_a_x_mem h
  have hq : x⁻¹ ∈ Subgroup.zpowers x := Subgroup.inv_mem _ (Subgroup.mem_zpowers x)
  have hpq : Commute (a * x * a⁻¹) x⁻¹ := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hp
    rw [← hi]
    exact (Commute.zpow_left (Commute.refl x) i).inv_right
  refine mem_zpowers_of_pow_three_eq_one (d_mem_zpowers_x h) (orderOf_d h)
    (Subgroup.mul_mem _ hp hq) ?_
  rw [hpq.mul_pow, conj_pow, conj_a_x_cube h, inv_pow, mul_inv_cancel]

theorem nine_dvd_orderOf_x (h : Sec11Data G A c L a R Y d x s r g) : 9 ∣ orderOf x := by
  obtain ⟨k, hk⟩ := x_pow_eq_one h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  have h3 : 3 ∣ orderOf x := by
    rw [← orderOf_d h]
    exact orderOf_dvd_of_mem_zpowers (d_mem_zpowers_x h)
  have hj2 : 2 ≤ j := by
    by_contra hj2
    interval_cases j
    · rw [hj, pow_zero] at h3
      norm_num at h3
    ·
      have hxd : Subgroup.zpowers x = Subgroup.zpowers d :=
        (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (d_mem_zpowers_x h))
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hj, orderOf_d h, pow_one])).symm
      apply Item1116Proof.not_le_centralizer_of_isSylowOf h.toSec11Std
        h.toSec11Std.isSylowOf_inf_L
      rw [h.inf_L_eq, hxd, Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_of_mem_A h h.a_mem (d_mem_A h)).symm
  rw [hj]
  exact (pow_dvd_pow 3 hj2 : 3 ^ 2 ∣ 3 ^ j)

theorem d_mem_zpowers_x_cube (h : Sec11Data G A c L a R Y d x s r g) :
    d ∈ Subgroup.zpowers (x ^ 3) :=
  Item1125Proof.mem_zpowers_pow_three (pow_three_of_mem_A h (d_mem_A h)) (d_mem_zpowers_x h)
    (nine_dvd_orderOf_x h)

theorem commute_d_x (h : Sec11Data G A c L a R Y d x s r g) : d * x = x * d := by
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (d_mem_zpowers_x h)
  rw [← hi]
  exact (Commute.zpow_left (Commute.refl x) i).eq

theorem exists_conj_x_of_mem_A (h : Sec11Data G A c L a R Y d x s r g) {u : G} (hu : u ∈ A) :
    ∃ z ∈ Subgroup.zpowers d, u * x * u⁻¹ = x * z := by
  have hdA := d_mem_A h
  have hzA : Subgroup.zpowers d ≤ A := Subgroup.zpowers_le.mpr hdA
  have hu' : u ∈ Subgroup.closure ({c, a, d} : Set G) := h.closure_eq ▸ hu
  clear hu
  induction hu' using Subgroup.closure_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      have hyx : y * x = x * y := (Subgroup.mem_centralizer_singleton_iff.mp
        (R_le_centralizer_c h (Item1116Proof.mem_R h).2.1)).symm
      rw [mul_one, hyx, mul_inv_cancel_right]
    · refine ⟨x⁻¹ * (y * x * y⁻¹), ?_, by group⟩
      have h1 := commutator_a_x_mem h
      have e : x⁻¹ * (y * x * y⁻¹) = x⁻¹ * (y * x * y⁻¹ * x⁻¹) * x := by group
      rw [e]
      have hcomm : Commute (y * x * y⁻¹ * x⁻¹) x := by
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h1
        rw [← hi]
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (d_mem_zpowers_x h)
        rw [← hj, ← zpow_mul]
        exact Commute.zpow_left (Commute.refl x) _
      rw [mul_assoc, hcomm.eq, ← mul_assoc, inv_mul_cancel, one_mul]
      exact h1
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [mul_one, commute_d_x h, mul_inv_cancel_right]
  | one => exact ⟨1, Subgroup.one_mem _, by group⟩
  | mul u v hu hv ihu ihv =>
    obtain ⟨z, hz, hzu⟩ := ihu
    obtain ⟨w, hw, hwv⟩ := ihv
    have huA : u ∈ A := h.closure_eq ▸ hu
    have hwu : u * w * u⁻¹ = w := by
      rw [commute_of_mem_A h huA (hzA hw), mul_inv_cancel_right]
    refine ⟨z * w, Subgroup.mul_mem _ hz hw, ?_⟩
    calc u * v * x * (u * v)⁻¹ = u * (v * x * v⁻¹) * u⁻¹ := by group
      _ = (u * x * u⁻¹) * (u * w * u⁻¹) := by rw [hwv]; group
      _ = x * (z * w) := by rw [hzu, hwu]; group
  | inv u hu ihu =>
    obtain ⟨z, hz, hzu⟩ := ihu
    have huA : u ∈ A := h.closure_eq ▸ hu
    refine ⟨z⁻¹, Subgroup.inv_mem _ hz, ?_⟩
    have hzc : u * z = z * u := commute_of_mem_A h huA (hzA hz)
    have e : x = (u⁻¹ * x * u) * z := by
      calc x = u⁻¹ * (u * x * u⁻¹) * u := by group
        _ = u⁻¹ * (x * z) * u := by rw [hzu]
        _ = (u⁻¹ * x * u) * (u⁻¹ * z * u) := by group
        _ = (u⁻¹ * x * u) * z := by
          congr 1
          rw [mul_assoc, ← hzc, ← mul_assoc, inv_mul_cancel, one_mul]
    calc u⁻¹ * x * u⁻¹⁻¹ = (u⁻¹ * x * u) * z * z⁻¹ := by group
      _ = x * z⁻¹ := by rw [← e]

theorem commute_x_of_mem_zpowers_d (h : Sec11Data G A c L a R Y d x s r g) {z : G}
    (hz : z ∈ Subgroup.zpowers d) : Commute x z := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (d_mem_zpowers_x h)
  rw [← hj, ← zpow_mul]
  exact (Commute.zpow_left (Commute.refl x) _).symm

theorem exists_conj_of_mem_A (h : Sec11Data G A c L a R Y d x s r g) {v : G} (hv : v ∈ A) :
    ∃ z ∈ Subgroup.zpowers d, x * v * x⁻¹ = v * z := by
  obtain ⟨z, hz, hzv⟩ := exists_conj_x_of_mem_A h (A.inv_mem hv)
  refine ⟨z, hz, ?_⟩
  have hxz := commute_x_of_mem_zpowers_d h hz
  calc x * v * x⁻¹ = v * (v⁻¹ * x * v⁻¹⁻¹) * x⁻¹ := by group
    _ = v * (x * z) * x⁻¹ := by rw [hzv]
    _ = v * z := by rw [hxz.eq]; group

theorem exists_eq_zpow_mul (h : Sec11Data G A c L a R Y d x s r g)
    (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) {y : G} (hy : y ∈ R) :
    ∃ (m : ℤ) (u : G), u ∈ A ∧ y = x ^ m * u := by
  rw [R_eq_closure h hsc hrs] at hy
  have hzA : Subgroup.zpowers d ≤ A := Subgroup.zpowers_le.mpr (d_mem_A h)
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact ⟨0, y, h.a_mem, by simp⟩
    · exact ⟨1, 1, A.one_mem, by simp⟩
    · exact ⟨0, y, h.mem_A, by simp⟩
  | one => exact ⟨0, 1, A.one_mem, by simp⟩
  | mul y y' _ _ ihy ihy' =>
    obtain ⟨m, u, hu, rfl⟩ := ihy
    obtain ⟨n, v, hv, rfl⟩ := ihy'
    obtain ⟨z, hz, hzu⟩ := exists_conj_x_of_mem_A h hu
    have hxz := commute_x_of_mem_zpowers_d h hz
    have h1 : u * x ^ n * u⁻¹ = x ^ n * z ^ n := by
      rw [← conj_zpow, hzu, hxz.mul_zpow]
    refine ⟨m + n, z ^ n * u * v, A.mul_mem (A.mul_mem (A.zpow_mem (hzA hz) n) hu) hv, ?_⟩
    calc x ^ m * u * (x ^ n * v) = x ^ m * (u * x ^ n * u⁻¹) * u * v := by group
      _ = x ^ (m + n) * (z ^ n * u * v) := by rw [h1, zpow_add]; group
  | inv y _ ihy =>
    obtain ⟨m, u, hu, rfl⟩ := ihy
    obtain ⟨z, hz, hzu⟩ := exists_conj_x_of_mem_A h (A.inv_mem hu)
    have hxz := commute_x_of_mem_zpowers_d h hz
    have h1 : u⁻¹ * x ^ (-m) * u⁻¹⁻¹ = x ^ (-m) * z ^ (-m) := by
      rw [← conj_zpow, hzu, hxz.mul_zpow]
    refine ⟨-m, z ^ (-m) * u⁻¹, A.mul_mem (A.zpow_mem (hzA hz) _) (A.inv_mem hu), ?_⟩
    calc (x ^ m * u)⁻¹ = (u⁻¹ * x ^ (-m) * u⁻¹⁻¹) * u⁻¹ := by group
      _ = x ^ (-m) * (z ^ (-m) * u⁻¹) := by rw [h1]; group

theorem zpow_mul_pow_three (h : Sec11Data G A c L a R Y d x s r g) {u : G} (hu : u ∈ A)
    (m : ℤ) : (x ^ m * u) ^ 3 = (x ^ 3) ^ m := by
  have hzA : Subgroup.zpowers d ≤ A := Subgroup.zpowers_le.mpr (d_mem_A h)
  obtain ⟨z, hz, hzu⟩ := exists_conj_x_of_mem_A h hu
  have hxz := commute_x_of_mem_zpowers_d h hz
  have h1 : u * x ^ m = x ^ m * z ^ m * u := by
    have e : u * x ^ m * u⁻¹ = x ^ m * z ^ m := by rw [← conj_zpow, hzu, hxz.mul_zpow]
    calc u * x ^ m = (u * x ^ m * u⁻¹) * u := by group
      _ = x ^ m * z ^ m * u := by rw [e]
  have hzy : z ^ m * x ^ m = x ^ m * z ^ m := ((hxz.zpow_zpow m m).eq).symm
  have hzu' : z ^ m * u = u * z ^ m := commute_of_mem_A h (A.zpow_mem (hzA hz) m) hu
  have hz3 : (z ^ m) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      pow_three_of_mem_A h (hzA hz), one_zpow]
  rw [mul_pow_three_eq h1 hzy hzu' hz3 (pow_three_of_mem_A h hu), ← zpow_natCast, ← zpow_mul,
    ← zpow_natCast x 3, ← zpow_mul, mul_comm]

theorem pow_three_mem_zpowers (h : Sec11Data G A c L a R Y d x s r g)
    (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) {y : G} (hy : y ∈ R) :
    y ^ 3 ∈ Subgroup.zpowers (x ^ 3) := by
  obtain ⟨m, u, hu, rfl⟩ := exists_eq_zpow_mul h hsc hrs hy
  rw [zpow_mul_pow_three h hu m]
  exact Subgroup.zpow_mem_zpowers _ m

theorem conj_pow_three_mem (h : Sec11Data G A c L a R Y d x s r g)
    (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) :
    g * x ^ 3 * g⁻¹ ∈ Subgroup.zpowers (x ^ 3) := by
  rw [← conj_pow]
  exact pow_three_mem_zpowers h hsc hrs
    ((Subgroup.mem_normalizer_iff.mp h.g_mem_normalizer x).mp (Item1116Proof.mem_R h).2.1)

theorem g_mem_normalizer_d (h117 : Item117) (h : Sec11Data G A c L a R Y d x s r g) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
  (h117 G A c L a R Y h.toSec11Std d h.inf_eq (Subgroup.zpowers d)
    (Subgroup.zpowers_le.mpr (d_mem_A h)) (by rw [Nat.card_zpowers, orderOf_d h])).mpr rfl
    h.g_mem.2

theorem conj_g_d (h117 : Item117) (h : Sec11Data G A c L a R Y d x s r g) :
    g * d * g⁻¹ = d :=
  conj_eq_self_of_threeElement (pow_three_of_mem_A h (d_mem_A h)) h.pow_eq_one
    ((Subgroup.mem_normalizer_iff.mp (g_mem_normalizer_d h117 h) d).mp (Subgroup.mem_zpowers d))

theorem commute_g_a (h : Sec11Data G A c L a R Y d x s r g) : g * a = a * g :=
  Subgroup.mem_centralizer_singleton_iff.mp
    (Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y h.g_mem.1)

theorem conj_g_c_mem (h117 : Item117) (h : Sec11Data G A c L a R Y d x s r g) :
    g * c * g⁻¹ * c⁻¹ ∈ Subgroup.zpowers d := by
  have hcd : c * d = d * c := commute_of_mem_A h h.mem_A (d_mem_A h)
  obtain ⟨i, j, -, -, hij⟩ := KFacts.exists_pow_mul_pow_of_mem_closure_pair hcd
    (pow_three_of_mem_A h h.mem_A) (pow_three_of_mem_A h (d_mem_A h)) h.conj_mem
  refine Item1123Proof.conj_mul_inv_mem_of_pow_three_mem (g_mem_normalizer_d h117 h) ?_ ?_
    h.pow_eq_one (k := (i : ℤ)) ?_
  · refine Sec10.mem_normalizer_zpowers_of_conj_mem ?_
    rw [hcd, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers d
  · rw [pow_three_of_mem_A h h.mem_A]
    exact Subgroup.one_mem _
  · rw [hij, zpow_natCast, inv_mul_cancel_left]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) j

theorem conj_g_mem_of_mem_A (h117 : Item117) (h : Sec11Data G A c L a R Y d x s r g) {u : G}
    (hu : u ∈ A) : g * u * g⁻¹ * u⁻¹ ∈ Subgroup.zpowers d := by
  have hzA : Subgroup.zpowers d ≤ A := Subgroup.zpowers_le.mpr (d_mem_A h)
  have hu' : u ∈ Subgroup.closure ({c, a, d} : Set G) := h.closure_eq ▸ hu
  clear hu
  induction hu' using Subgroup.closure_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact conj_g_c_mem h117 h
    · rw [commute_g_a h, mul_inv_cancel_right, mul_inv_cancel]
      exact Subgroup.one_mem _
    · rw [conj_g_d h117 h, mul_inv_cancel]
      exact Subgroup.one_mem _
  | one => simp
  | mul u v hu _ ihu ihv =>
    have huA : u ∈ A := h.closure_eq ▸ hu
    have e : g * (u * v) * g⁻¹ * (u * v)⁻¹ =
        (g * u * g⁻¹ * u⁻¹) * (u * (g * v * g⁻¹ * v⁻¹) * u⁻¹) := by group
    have hw : u * (g * v * g⁻¹ * v⁻¹) * u⁻¹ = g * v * g⁻¹ * v⁻¹ := by
      rw [commute_of_mem_A h huA (hzA ihv), mul_inv_cancel_right]
    rw [e, hw]
    exact Subgroup.mul_mem _ ihu ihv
  | inv u hu ihu =>
    have huA : u ∈ A := h.closure_eq ▸ hu
    have e : g * u⁻¹ * g⁻¹ * u⁻¹⁻¹ = u⁻¹ * (g * u * g⁻¹ * u⁻¹)⁻¹ * u := by group
    have hw : u⁻¹ * (g * u * g⁻¹ * u⁻¹)⁻¹ * u = (g * u * g⁻¹ * u⁻¹)⁻¹ := by
      rw [commute_of_mem_A h (A.inv_mem huA) (hzA (Subgroup.inv_mem _ ihu)), mul_assoc,
        inv_mul_cancel, mul_one]
    rw [e, hw]
    exact Subgroup.inv_mem _ ihu

theorem commutator_g_x_mem (h : Sec11Data G A c L a R Y d x s r g)
    (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s})
    (hgx3 : g * x ^ 3 * g⁻¹ = x ^ 3) : g * x * g⁻¹ * x⁻¹ ∈ A := by
  have hgx : g * x * g⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff.mp h.g_mem_normalizer x).mp (Item1116Proof.mem_R h).2.1
  obtain ⟨m, u, hu, hmu⟩ := exists_eq_zpow_mul h hsc hrs hgx
  have h3 : (x ^ 3) ^ m = x ^ 3 := by
    rw [← zpow_mul_pow_three h hu m, ← hmu, conj_pow, hgx3]
  have hw3 : (x ^ (m - 1)) ^ 3 = 1 := by
    have e : (x ^ (m - 1)) ^ 3 = (x ^ 3) ^ m * (x ^ 3)⁻¹ := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast x 3, ← zpow_mul, ← zpow_neg_one,
        ← zpow_mul, ← zpow_add]
      congr 1
      push_cast
      ring
    rw [e, h3, mul_inv_cancel]
  have hwd : x ^ (m - 1) ∈ Subgroup.zpowers d :=
    mem_zpowers_of_pow_three_eq_one (d_mem_zpowers_x h) (orderOf_d h)
      (Subgroup.zpow_mem_zpowers x _) hw3
  have hwA : x ^ (m - 1) * u ∈ A :=
    A.mul_mem (Subgroup.zpowers_le.mpr (d_mem_A h) hwd) hu
  have hxm : x ^ m = x * x ^ (m - 1) := by rw [← zpow_one_add, add_sub_cancel]
  obtain ⟨z, hz, hxz⟩ := exists_conj_of_mem_A h hwA
  have e : g * x * g⁻¹ * x⁻¹ = x * (x ^ (m - 1) * u) * x⁻¹ := by
    rw [hmu, hxm]
    group
  rw [e, hxz]
  exact A.mul_mem hwA (Subgroup.zpowers_le.mpr (d_mem_A h) hz)

theorem sec11P_eq_closure (h : Sec11Data G A c L a R Y d x s r g)
    (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) :
    sec11P R g = Subgroup.closure {a, x, c, g} := by
  rw [sec11P, R_eq_closure h hsc hrs, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
  congr 1
  ext y
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem commutator_eq_closure (h117 : Item117) (h : Sec11Data G A c L a R Y d x s r g)
    (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s})
    (he : g * x * g⁻¹ * x⁻¹ ∈ A) :
    ⁅sec11P R g, sec11P R g⁆ = Subgroup.closure {g * x * g⁻¹ * x⁻¹, d} := by
  set e := g * x * g⁻¹ * x⁻¹ with he_def
  set E := Subgroup.closure ({e, d} : Set G) with hE
  have hdA := d_mem_A h
  have hzA : Subgroup.zpowers d ≤ A := Subgroup.zpowers_le.mpr hdA
  have heE : e ∈ E := Subgroup.subset_closure (by simp)
  have hdE : d ∈ E := Subgroup.subset_closure (by simp)
  have hDE : Subgroup.zpowers d ≤ E := Subgroup.zpowers_le.mpr hdE
  have hcR : c ∈ R := le_R_of_hyp91 h.toHyp91 h.mem_A
  have hxc : x * c = c * x :=
    Subgroup.mem_centralizer_singleton_iff.mp (R_le_centralizer_c h (Item1116Proof.mem_R h).2.1)
  have hac : a * c = c * a := commute_of_mem_A h h.a_mem h.mem_A
  have hga := commute_g_a h
  have hconjA : ∀ u ∈ A, u * e * u⁻¹ = e := fun u hu => by
    rw [commute_of_mem_A h hu he, mul_inv_cancel_right]
  have hconjAd : ∀ u ∈ A, u * d * u⁻¹ = d := fun u hu => by
    rw [commute_of_mem_A h hu hdA, mul_inv_cancel_right]
  have hNx : x ∈ Subgroup.normalizer (E : Set G) := by
    refine mem_normalizer_closure_pair ?_ ?_
    · obtain ⟨z, hz, hxz⟩ := exists_conj_of_mem_A h he
      rw [hxz]
      exact E.mul_mem heE (hDE hz)
    · rw [← commute_d_x h, mul_inv_cancel_right]
      exact hdE
  have hNg : g ∈ Subgroup.normalizer (E : Set G) := by
    refine mem_normalizer_closure_pair ?_ ?_
    · have e1 : g * e * g⁻¹ = (g * e * g⁻¹ * e⁻¹) * e := by group
      rw [e1]
      exact E.mul_mem (hDE (conj_g_mem_of_mem_A h117 h he)) heE
    · rw [conj_g_d h117 h]
      exact hdE
  have hNA : ∀ u ∈ A, u ∈ Subgroup.normalizer (E : Set G) := fun u hu =>
    mem_normalizer_closure_pair (by rw [hconjA u hu]; exact heE)
      (by rw [hconjAd u hu]; exact hdE)
  have hax : ⁅a, x⁆ ∈ E := by
    rw [commutatorElement_def]
    exact hDE (commutator_a_x_mem h)
  have hgx : ⁅g, x⁆ ∈ E := by
    rw [commutatorElement_def]
    exact heE
  have hgc : ⁅g, c⁆ ∈ E := by
    rw [commutatorElement_def]
    exact hDE (conj_g_mem_of_mem_A h117 h h.mem_A)
  have hone : ∀ u v : G, u * v = v * u → ⁅u, v⁆ ∈ E := fun u v huv => by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr huv]
    exact E.one_mem
  have hinv : ∀ u v : G, ⁅u, v⁆ ∈ E → ⁅v, u⁆ ∈ E := fun u v huv => by
    rw [← commutatorElement_inv]
    exact E.inv_mem huv
  have hgP : g ∈ sec11P R g :=
    (le_sup_right : Subgroup.zpowers g ≤ sec11P R g) (Subgroup.mem_zpowers g)
  have hxP : x ∈ sec11P R g := le_sup_left (a := R) (Item1116Proof.mem_R h).2.1
  have hcP : c ∈ sec11P R g := le_sup_left (a := R) hcR
  apply le_antisymm
  · rw [sec11P_eq_closure h hsc hrs]
    refine commutator_closure_le ?_ ?_
    · rw [Subgroup.closure_le]
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact hNA t h.a_mem
      · exact hNx
      · exact hNA t h.mem_A
      · exact hNg
    · intro t ht t' ht'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht ht'
      rcases ht with rfl | rfl | rfl | rfl <;> rcases ht' with rfl | rfl | rfl | rfl
      all_goals first
        | exact hone _ _ rfl
        | exact hax
        | exact hinv _ _ hax
        | exact hgx
        | exact hinv _ _ hgx
        | exact hgc
        | exact hinv _ _ hgc
        | exact hone _ _ hac
        | exact hone _ _ hac.symm
        | exact hone _ _ hxc
        | exact hone _ _ hxc.symm
        | exact hone _ _ hga
        | exact hone _ _ hga.symm
  · rw [hE, Subgroup.closure_le]
    rintro y (rfl | rfl)
    · rw [he_def, ← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator hgP hxP
    ·
      have hw := conj_g_mem_of_mem_A h117 h h.mem_A
      have hw1 : g * c * g⁻¹ * c⁻¹ ≠ 1 := by
        intro h1
        apply h.g_not_mem
        refine Sec10.mem_normalizer_zpowers_of_conj_mem ?_
        rw [mul_inv_eq_one.mp h1]
        exact Subgroup.mem_zpowers c
      have hw3 : orderOf (g * c * g⁻¹ * c⁻¹) = 3 := by
        have h1 := orderOf_dvd_of_mem_zpowers hw
        rw [orderOf_d h] at h1
        rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h1 | h1
        · exact absurd (orderOf_eq_one_iff.mp h1) hw1
        · exact h1
      have heq : Subgroup.zpowers (g * c * g⁻¹ * c⁻¹) = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hw)
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hw3, orderOf_d h])
      have hdw : y ∈ Subgroup.zpowers (g * c * g⁻¹ * c⁻¹) := heq ▸ Subgroup.mem_zpowers y
      have hwP : g * c * g⁻¹ * c⁻¹ ∈ ⁅sec11P R g, sec11P R g⁆ := by
        rw [← commutatorElement_def]
        exact Subgroup.commutator_mem_commutator hgP hcP
      exact Subgroup.zpowers_le.mpr hwP hdw

theorem false_of_commutator_eq_closure_c_d (h45 : Sec4.Item4_5) (h113 : Item113)
    (h117 : Item117) (h : Sec11Data G A c L a R Y d x s r g)
    (hsc : Subgroup.zpowers s = Subgroup.zpowers c)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s})
    (hPP : ⁅sec11P R g, sec11P R g⁆ = Subgroup.closure {c, d}) : False := by
  have h' := h.of_closure_eq hrs
  have hcdN : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) := by
    rw [← hPP]
    exact normalizer_le_normalizer_commutator _
  have hNd := h'.normalizer_sec11P_le_normalizer_zpowers_d h113 h117 hcdN
  have htrans := h'.htrans hcdN hNd
  obtain ⟨-, hxR, hsR⟩ := Item1116Proof.mem_R h
  have haR : a ∈ R := le_R_of_hyp91 h.toHyp91 h.a_mem
  have hgP : g ∈ sec11P R g :=
    (le_sup_right : Subgroup.zpowers g ≤ sec11P R g) (Subgroup.mem_zpowers g)
  have hVP : Subgroup.closure ({s, x} : Set G) ≤ sec11P R g := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact le_sup_left (a := R) hsR
    · exact le_sup_left (a := R) hxR
  have hcdV : Subgroup.closure ({c, d} : Set G) ≤ Subgroup.closure {s, x} := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) h.c_mem_zpowers_s
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) (d_mem_zpowers_x h)
  have hgV : g ∈ Subgroup.normalizer
      ((Subgroup.closure ({s, x} : Set G) : Subgroup G) : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    have e : g * v * g⁻¹ = ⁅g, v⁆ * v := by rw [commutatorElement_def]; group
    rw [e]
    refine Subgroup.mul_mem _ (hcdV ?_) hv
    rw [← hPP]
    exact Subgroup.commutator_mem_commutator hgP (hVP hv)
  have hag : a * g = g * a := (commute_g_a h).symm
  exact rank3II_11_15_of h' hag h'.commute_s_x (h'.R_le_normalizer_V h45) hgV
    (h'.normalizer_P_le_normalizer_V h45 h113) (h'.commutator_mem_V h45 h113 outAbelian1016 haR)
    h'.r_not_mem_V hcdN hNd htrans

end Data

end Item1117Proof

end CFSG.RankThree.PartTwo.Sec11
