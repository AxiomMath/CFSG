module

public import CFSG.Quasithin.Vol2.Ch3E213MKer
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6 E2 CFSG.Timmesfeld

theorem odd_two_pow_sub_one {m : ℕ} (hm : 0 < m) : Odd (2 ^ m - 1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, hm.ne'⟩) odd_one

variable {G : Type*} [Group G] [Finite G] {X T M V : Subgroup G} {g : G}

omit [Finite G] in
theorem relIndex_dvd_relIndex (h : Pair X T M V g) :
    (kerIn M X ⊓ V).relIndex V ∣ (kerIn M X).relIndex X := by
  have hJX : kerIn M X ≤ X := kerIn_le.trans h.le_X
  have : ((kerIn M X).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJX).2 (le_normalizer_kerIn M X)
  rw [Subgroup.inf_relIndex_right, ← Subgroup.relIndex_subgroupOf h.V_le]
  exact Subgroup.relIndex_dvd_index_of_normal _ _

theorem exists_relIndex_eq_two_pow (h : Pair X T M V g) :
    ∃ j : ℕ, (kerIn M X ⊓ V).relIndex V = 2 ^ j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv⟩ := IsPGroup.iff_card.mp (B6.isPGroup_of_isElemAbelian h.elem)
  obtain ⟨j, -, hj⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).1 (hv ▸ Subgroup.relIndex_dvd_card (kerIn M X ⊓ V) V)
  exact ⟨j, hj⟩

theorem relIndex_le_two_pow (h : Pair X T M V g) {n u : ℕ} (hu : Odd u)
    (hcard : (kerIn M X).relIndex X = 2 ^ n * u) : (kerIn M X ⊓ V).relIndex V ≤ 2 ^ n := by
  obtain ⟨j, hj⟩ := exists_relIndex_eq_two_pow h
  have hdvd := relIndex_dvd_relIndex h
  rw [hj, hcard] at hdvd
  have hcop : Nat.Coprime (2 ^ j) u := Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hu)
  rw [hj]
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right hdvd)

theorem relIndex_le_of_primitive (h : Pair X T M V g) (hchar : CharTwo X) {r k : ℕ}
    (hk : 0 < k) (hr : IsPrimitivePrimeDivisor r k) (hrX : r ∣ Nat.card X)
    (hV : ((kerIn M X ⊓ V).relIndex V) ^ 2 ≤ 2 ^ k) :
    (kerIn M X ⊓ V).relIndex V ≤ (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) := by
  have : Fact r.Prime := ⟨hr.prime⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hrX
  refine relIndex_le_of_orderOf h hchar x.2 (a := 0) hr.prime (hr.ne_two hk)
    (by rw [pow_one, Subgroup.orderOf_coe, hx]) fun m hm hdvd => ?_
  rw [zero_add, pow_one] at hdvd
  exact hV.trans (Nat.pow_le_pow_right two_pos
    (Nat.le_of_dvd hm ((hr.dvd_sub_one_iff hk m).1 hdvd)))

theorem relIndex_le_of_orderOf_nine (h : Pair X T M V g) (hchar : CharTwo X) {c : G}
    (hcX : c ∈ X) (hc : orderOf c = 9) (hV : (kerIn M X ⊓ V).relIndex V ≤ 8) :
    (kerIn M X ⊓ V).relIndex V ≤ (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) := by
  refine relIndex_le_of_orderOf h hchar hcX (ℓ := 3) (a := 1) Nat.prime_three (by norm_num)
    (by rw [hc]; norm_num) fun m hm hdvd => ?_
  have h6 : 6 ∣ m := six_dvd_of_nine_dvd_two_pow_sub_one (by simpa using hdvd)
  calc ((kerIn M X ⊓ V).relIndex V) ^ 2 ≤ 8 ^ 2 := Nat.pow_le_pow_left hV 2
    _ = 2 ^ 6 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right two_pos (Nat.le_of_dvd hm h6)

theorem relIndex_le_of_prime (h : Pair X T M V g) (hchar : CharTwo X) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpX : p ∣ Nat.card X) (hV : (kerIn M X ⊓ V).relIndex V ≤ 2) :
    (kerIn M X ⊓ V).relIndex V ≤ (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpX
  refine relIndex_le_of_orderOf h hchar x.2 (a := 0) hp hp2
    (by rw [pow_one, Subgroup.orderOf_coe, hx]) fun m hm hdvd => ?_
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hm1 : m = 1 := by omega
    rw [hm1] at hdvd
    norm_num at hdvd
    exact hp.one_lt.ne' hdvd
  calc ((kerIn M X ⊓ V).relIndex V) ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left hV 2
    _ ≤ 2 ^ m := Nat.pow_le_pow_right two_pos hm2

theorem relIndex_le_of_dihedral (h : Pair X T M V g) (hchar : CharTwo X) {p a : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : 1 ≤ a) (hcard : (kerIn M X).relIndex X = 2 * p ^ a) :
    (kerIn M X ⊓ V).relIndex V ≤ (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) := by
  have hV := relIndex_le_two_pow h (n := 1) ((hp.odd_of_ne_two hp2).pow) (by rw [hcard, pow_one])
  refine relIndex_le_of_prime h hchar hp hp2 ?_ (by simpa using hV)
  exact ((dvd_pow_self p (by omega)).trans (Dvd.intro_left 2 hcard.symm)).trans
    (Subgroup.relIndex_dvd_card _ _)

theorem relIndex_le_of_psl2 (h : Pair X T M V g) (hchar : CharTwo X) {n : ℕ} (hn : 2 ≤ n)
    (hcard : (kerIn M X).relIndex X = 2 ^ n * ((2 ^ n) ^ 2 - 1))
    (h9 : n = 3 → ∃ c ∈ X, orderOf c = 9) :
    (kerIn M X ⊓ V).relIndex V ≤ (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) := by
  have hq : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, mul_comm]
  have hVle := relIndex_le_two_pow h (by rw [hq]; exact odd_two_pow_sub_one (by omega)) hcard
  by_cases hn3 : n = 3
  · subst hn3
    obtain ⟨c, hcX, hc⟩ := h9 rfl
    exact relIndex_le_of_orderOf_nine h hchar hcX hc (by simpa using hVle)
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 2 * n) (by omega) (by omega)
  refine relIndex_le_of_primitive h hchar (k := 2 * n) (by omega) hr ?_ ?_
  · have h1 : r ∣ (2 ^ n) ^ 2 - 1 := by rw [hq]; exact hr.dvd
    exact (h1.trans (Dvd.intro_left _ hcard.symm)).trans (Subgroup.relIndex_dvd_card _ _)
  · calc ((kerIn M X ⊓ V).relIndex V) ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hVle 2
      _ = 2 ^ (2 * n) := hq

theorem primitive_dvd_sq_add_one {n r : ℕ} (hn : 1 ≤ n) (hr : IsPrimitivePrimeDivisor r (4 * n)) :
    r ∣ (2 ^ n) ^ 2 + 1 := by
  rw [← pow_mul, mul_comm n 2]
  refine (hr.dvd_add_one_iff (by omega) (2 * n)).2 ⟨⟨1, by ring⟩, fun h4 => ?_⟩
  have := Nat.le_of_dvd (by omega) h4
  omega

theorem relIndex_le_of_sz (h : Pair X T M V g) (hchar : CharTwo X) {n : ℕ} (hn : 3 ≤ n)
    (hcard : (kerIn M X).relIndex X = (2 ^ n) ^ 2 * (((2 ^ n) ^ 2 + 1) * (2 ^ n - 1))) :
    (kerIn M X ⊓ V).relIndex V ≤ (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) := by
  have hq : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul, mul_comm]
  have hodd : Odd (((2 ^ n) ^ 2 + 1) * (2 ^ n - 1)) := by
    refine Odd.mul ?_ (odd_two_pow_sub_one (by omega))
    rw [hq]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  have hVle := relIndex_le_two_pow h hodd (by rw [hcard, hq])
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 4 * n) (by omega) (by omega)
  refine relIndex_le_of_primitive h hchar (k := 4 * n) (by omega) hr ?_ ?_
  · refine (((primitive_dvd_sq_add_one (by omega) hr).trans (Dvd.intro _ rfl)).trans
      (Dvd.intro_left _ hcard.symm)).trans (Subgroup.relIndex_dvd_card _ _)
  · calc ((kerIn M X ⊓ V).relIndex V) ^ 2 ≤ (2 ^ (2 * n)) ^ 2 := Nat.pow_le_pow_left hVle 2
      _ = 2 ^ (4 * n) := by rw [← pow_mul]; ring_nf

theorem relIndex_le_of_sp4 (h : Pair X T M V g) (hchar : CharTwo X) {n : ℕ} (hn : 1 ≤ n)
    (hdvd : (2 ^ n) ^ 2 + 1 ∣ (kerIn M X).relIndex X)
    (hV : (kerIn M X ⊓ V).relIndex V ≤ 2 ^ (2 * n)) :
    (kerIn M X ⊓ V).relIndex V ≤ (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) := by
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 4 * n) (by omega) (by omega)
  refine relIndex_le_of_primitive h hchar (k := 4 * n) (by omega) hr
    (((primitive_dvd_sq_add_one hn hr).trans hdvd).trans (Subgroup.relIndex_dvd_card _ _)) ?_
  calc ((kerIn M X ⊓ V).relIndex V) ^ 2 ≤ (2 ^ (2 * n)) ^ 2 := Nat.pow_le_pow_left hV 2
    _ = 2 ^ (4 * n) := by rw [← pow_mul]; ring_nf

end CFSG.Quasithin.Ch3E213M
