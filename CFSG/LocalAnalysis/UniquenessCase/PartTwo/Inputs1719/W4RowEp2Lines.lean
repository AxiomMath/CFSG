module

import TauCeti.GroupTheory.ExponentPrime
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {a b : G}

private theorem mem_sup_zpowers_iff_exists_zpow {a b z : G} (hc : Commute a b) :
    z ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b ↔ ∃ i j : ℤ, z = a ^ i * b ^ j := by
  rw [Subgroup.zpowers_eq_closure a, Subgroup.zpowers_eq_closure b, ← Subgroup.closure_union]
  have hpair : ({a} ∪ {b} : Set G) = {a, b} := by
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
  rw [hpair]
  constructor
  · intro hz
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
    | one => exact ⟨0, 0, by simp⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨i, j, rfl⟩ := ihx
      obtain ⟨i', j', rfl⟩ := ihy
      refine ⟨i + i', j + j', ?_⟩
      have hcomm : b ^ j * a ^ i' = a ^ i' * b ^ j := (hc.zpow_zpow i' j).eq.symm
      calc a ^ i * b ^ j * (a ^ i' * b ^ j')
          = a ^ i * (b ^ j * a ^ i') * b ^ j' := by group
        _ = a ^ i * (a ^ i' * b ^ j) * b ^ j' := by rw [hcomm]
        _ = a ^ (i + i') * b ^ (j + j') := by
          rw [zpow_add, zpow_add]
          group
    | inv x _ ihx =>
      obtain ⟨i, j, rfl⟩ := ihx
      refine ⟨-i, -j, ?_⟩
      rw [mul_inv_rev, zpow_neg, zpow_neg, ← zpow_neg, ← zpow_neg]
      exact (hc.zpow_zpow (-i) (-j)).eq.symm
  · rintro ⟨i, j, rfl⟩
    exact Subgroup.mul_mem _
      (Subgroup.zpow_mem (Subgroup.closure {a, b})
        (Subgroup.subset_closure (by simp)) i)
      (Subgroup.zpow_mem (Subgroup.closure {a, b})
        (Subgroup.subset_closure (by simp)) j)

omit [Fact p.Prime] in
private theorem exists_pow_pow_of_mem_sup_zpowers (hp : p.Prime) (ha : a ^ p = 1)
    (hb : b ^ p = 1) (hc : Commute a b) {z : G}
    (hz : z ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) :
    ∃ k < p, ∃ l < p, z = a ^ k * b ^ l := by
  obtain ⟨i, j, rfl⟩ := (mem_sup_zpowers_iff_exists_zpow hc).1 hz
  have hp0 : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h0i : 0 ≤ i % (p : ℤ) := Int.emod_nonneg i hpne
  have h0j : 0 ≤ j % (p : ℤ) := Int.emod_nonneg j hpne
  have hlti : (i % (p : ℤ)).toNat < p := by
    have h := Int.emod_lt_of_pos i hp0
    rw [← Int.toNat_of_nonneg h0i] at h
    exact_mod_cast h
  have hltj : (j % (p : ℤ)).toNat < p := by
    have h := Int.emod_lt_of_pos j hp0
    rw [← Int.toNat_of_nonneg h0j] at h
    exact_mod_cast h
  refine ⟨(i % (p : ℤ)).toNat, hlti, (j % (p : ℤ)).toNat, hltj, ?_⟩
  rw [zpow_eq_zpow_emod' i ha, zpow_eq_zpow_emod' j hb, ← zpow_natCast, ← zpow_natCast,
    Int.toNat_of_nonneg h0i, Int.toNat_of_nonneg h0j]

omit [Fact p.Prime] in
theorem not_mem_zpowers_of_forall_ne_pow_lt {n : ℕ} (hn : 0 < n) (ha : a ^ n = 1)
    (hba : ∀ k < n, b ≠ a ^ k) : b ∉ Subgroup.zpowers a := by
  intro hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  refine hba (k % n).toNat ?_ ?_
  · have := Int.emod_lt_of_pos k (by exact_mod_cast hn : (0 : ℤ) < n)
    omega
  · rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hn')]
    conv_lhs => rw [← Int.emod_add_mul_ediv k n]
    rw [zpow_add, zpow_mul, zpow_natCast, ha, one_zpow, mul_one]

private theorem not_mem_zpowers_of_mem_zpowers {x y : G} (hx : x ^ p = 1) (hy1 : y ≠ 1)
    (hyx : x ∉ Subgroup.zpowers y) : y ∉ Subgroup.zpowers x := by
  intro hyx'
  have heq : Subgroup.zpowers y = Subgroup.zpowers x :=
    TauCeti.zpowers_eq_zpowers_of_mem_zpowers Fact.out hx hy1 hyx'
  exact hyx (heq.symm.le (Subgroup.mem_zpowers x))

private theorem a_not_mem_zpowers_b (ha : a ^ p = 1) (hb : b ^ p = 1) (ha1 : a ≠ 1)
    (hba : ∀ j < p, b ≠ a ^ j) : a ∉ Subgroup.zpowers b := by
  have hb1 : b ≠ 1 := by
    have := hba 0 (Fact.out : p.Prime).pos
    simpa using this
  exact not_mem_zpowers_of_mem_zpowers hb ha1
    (not_mem_zpowers_of_forall_ne_pow_lt (Fact.out : p.Prime).pos ha hba)

omit [Fact p.Prime] in
private theorem pow_mul_pow_eq_one (ha : a ^ p = 1) (hb : b ^ p = 1)
    (hab : a * b = b * a) (i : ℕ) : (a * b ^ i) ^ p = 1 := by
  have hcomm : Commute a b := hab
  rw [(hcomm.pow_right i).mul_pow p, ha]
  have hbi : (b ^ i) ^ p = 1 := by
    rw [← pow_mul, mul_comm i p, pow_mul, hb, one_pow]
  rw [hbi, mul_one]

private theorem mul_pow_ne_one (ha : a ^ p = 1) (hb : b ^ p = 1) (ha1 : a ≠ 1)
    (hba : ∀ j < p, b ≠ a ^ j) (i : ℕ) : a * b ^ i ≠ 1 := by
  intro h
  have ha_mem : a ∈ Subgroup.zpowers b := by
    have h1 : a = (b ^ i)⁻¹ := by
      calc a = (a * b ^ i) * (b ^ i)⁻¹ := by group
        _ = 1 * (b ^ i)⁻¹ := by rw [h]
        _ = (b ^ i)⁻¹ := one_mul _
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨-(i : ℤ), ?_⟩
    rw [zpow_neg, zpow_natCast]
    exact h1.symm
  exact a_not_mem_zpowers_b ha hb ha1 hba ha_mem

theorem eq_zpowers_of_le_sup_zpowers (ha : a ^ p = 1) (hb : b ^ p = 1) (hab : a * b = b * a)
    {D : Subgroup G} (hD : D ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    (hcard : Nat.card D = p) :
    D = Subgroup.zpowers b ∨ ∃ i < p, D = Subgroup.zpowers (a * b ^ i) := by
  classical
  have hp : p.Prime := Fact.out
  have hcomm : Commute a b := hab
  have hDbot : D ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    exact hp.ne_one hcard.symm
  rcases Subgroup.bot_or_exists_ne_one D with hbot | ⟨d, hdD, hd1⟩
  · exact absurd hbot hDbot
  have hdvd : orderOf d ∣ p := by
    simpa [hcard] using Subgroup.orderOf_dvd_natCard D hdD
  have hdorder : orderOf d = p := by
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hd1
    · exact h
  have hcardd : Nat.card (Subgroup.zpowers d) = p := by
    rw [Nat.card_zpowers, hdorder]
  have hDle : Subgroup.zpowers d ≤ D := Subgroup.zpowers_le.mpr hdD
  have hfinD : Finite ↥D := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  have hDd : D = Subgroup.zpowers d :=
    (Subgroup.eq_of_le_of_card_ge hDle (by rw [hcard, hcardd])).symm
  obtain ⟨k, hklt, l, _, hd_eq⟩ :=
    exists_pow_pow_of_mem_sup_zpowers hp ha hb hab (hD hdD)
  by_cases hk : k = 0
  · have hd_eq_b : d = b ^ l := by rw [hd_eq, hk, pow_zero, one_mul]
    have hdmem : d ∈ Subgroup.zpowers b := by
      rw [hd_eq_b]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers b) l
    have hdeq : Subgroup.zpowers d = Subgroup.zpowers b :=
      TauCeti.zpowers_eq_zpowers_of_mem_zpowers hp hb hd1 hdmem
    exact Or.inl (hDd.trans hdeq)
  · have hcop : k.Coprime p := (Nat.coprime_of_lt_prime hk hklt hp).symm
    obtain ⟨k', _, hk'mul⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    have hdpow : d ^ p = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rw [hdorder])
    have hkk' : k' * k % p = 1 := by rw [mul_comm, hk'mul]
    have hd_eq_pow : d = (d ^ k') ^ k := by
      rw [← pow_mul, ← pow_mod_orderOf d (k' * k), hdorder, hkk', pow_one]
    have hdk'_ne : d ^ k' ≠ 1 := by
      intro h1
      apply hd1
      rw [hd_eq_pow, h1, one_pow]
    have hzk : Subgroup.zpowers (d ^ k') = Subgroup.zpowers d :=
      TauCeti.zpowers_eq_zpowers_of_mem_zpowers hp hdpow hdk'_ne
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers d) k')
    have hpow : d ^ k' = a * b ^ ((l * k') % p) := by
      rw [hd_eq, (hcomm.pow_pow k l).mul_pow k', ← pow_mul, ← pow_mul]
      have hak : a ^ (k * k') = a := by
        rw [pow_eq_pow_mod (n := p) (m := k * k') ha, hk'mul, pow_one]
      have hbl : b ^ (l * k') = b ^ ((l * k') % p) :=
        pow_eq_pow_mod (n := p) (m := l * k') hb
      rw [hak, hbl]
    have hDfinal : D = Subgroup.zpowers (a * b ^ ((l * k') % p)) := by
      rw [hDd, ← hzk, hpow]
    exact Or.inr ⟨(l * k') % p, Nat.mod_lt _ hp.pos, hDfinal⟩

theorem card_zpowers_mul_pow (ha : a ^ p = 1) (hb : b ^ p = 1) (ha1 : a ≠ 1)
    (hab : a * b = b * a) (hba : ∀ j < p, b ≠ a ^ j) (i : ℕ) :
    Nat.card (Subgroup.zpowers (a * b ^ i)) = p := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (pow_mul_pow_eq_one ha hb hab i)
    (mul_pow_ne_one ha hb ha1 hba i)

theorem zpowers_ne_zpowers_mul_pow (ha : a ^ p = 1) (hb : b ^ p = 1) (ha1 : a ≠ 1)
    (hab : a * b = b * a) (hba : ∀ j < p, b ≠ a ^ j) (i : ℕ) :
    Subgroup.zpowers b ≠ Subgroup.zpowers (a * b ^ i) := by
  intro h
  have _ : Commute a b := hab
  have hxmem : a * b ^ i ∈ Subgroup.zpowers b := by
    rw [h]
    exact Subgroup.mem_zpowers (a * b ^ i)
  have hamem : a ∈ Subgroup.zpowers b := by
    have hbi : b ^ i ∈ Subgroup.zpowers b :=
      Subgroup.pow_mem _ (Subgroup.mem_zpowers b) i
    have hprod : (a * b ^ i) * (b ^ i)⁻¹ ∈ Subgroup.zpowers b :=
      Subgroup.mul_mem _ hxmem (Subgroup.inv_mem _ hbi)
    have haeq : (a * b ^ i) * (b ^ i)⁻¹ = a := by group
    simpa [haeq] using hprod
  exact a_not_mem_zpowers_b ha hb ha1 hba hamem

private theorem pow_not_mem_zpowers_of_lt (ha : a ^ p = 1) (hab : a ∉ Subgroup.zpowers b)
    {d : ℕ} (hd0 : 0 < d) (hdp : d < p) : a ^ d ∉ Subgroup.zpowers b := by
  intro hdmem
  have hp : p.Prime := Fact.out
  obtain ⟨d', _, hd'mul⟩ :=
    Nat.exists_mul_mod_eq_one_of_coprime (Nat.coprime_of_lt_prime hd0.ne' hdp hp).symm hp.one_lt
  have ha_eq : a = (a ^ d) ^ d' := by
    rw [← pow_mul, pow_eq_pow_mod (n := p) (m := d * d') ha, hd'mul, pow_one]
  exact hab (ha_eq ▸ Subgroup.pow_mem _ hdmem d')

private theorem not_mul_pow_eq_pow (ha : a ^ p = 1) (hab : a * b = b * a)
    (hanb : a ∉ Subgroup.zpowers b) {i j k : ℕ} (hk1 : 1 < k) (hkp : k < p)
    (hkx : (a * b ^ i) ^ k = a * b ^ j) : False := by
  have hxy : a * (a ^ (k - 1) * b ^ (i * k)) = a * b ^ j := by
    rw [← hkx, ((Commute.pow_right hab i).mul_pow k), ← pow_mul, ← mul_assoc, ← pow_succ',
      Nat.sub_add_cancel hk1.le]
  have h1 : a ^ (k - 1) = b ^ j * (b ^ (i * k))⁻¹ :=
    eq_mul_inv_of_mul_eq (mul_left_cancel hxy)
  refine pow_not_mem_zpowers_of_lt ha hanb (d := k - 1) (by omega) (by omega) ?_
  rw [h1]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) j)
    (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) (i * k)))

theorem eq_of_zpowers_mul_pow_eq (ha : a ^ p = 1) (hb : b ^ p = 1) (ha1 : a ≠ 1)
    (hab : a * b = b * a) (hba : ∀ j < p, b ≠ a ^ j) {i j : ℕ} (hi : i < p) (hj : j < p)
    (h : Subgroup.zpowers (a * b ^ i) = Subgroup.zpowers (a * b ^ j)) : i = j := by
  classical
  have hp : p.Prime := Fact.out
  have hborder : orderOf b = p := orderOf_eq_prime hb (by simpa using hba 0 hp.pos)
  have hxpow : (a * b ^ i) ^ p = 1 := pow_mul_pow_eq_one ha hb hab i
  have hxorder : orderOf (a * b ^ i) = p :=
    orderOf_eq_prime hxpow (mul_pow_ne_one ha hb ha1 hba i)
  have hyx : a * b ^ j ∈ Subgroup.zpowers (a * b ^ i) := h ▸ Subgroup.mem_zpowers _
  obtain ⟨k, hklt, hkx⟩ := Finset.mem_image.mp
    (((isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, hxpow⟩).mem_zpowers_iff_mem_range_orderOf).mp
      hyx)
  rw [Finset.mem_range, hxorder] at hklt
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact mul_pow_ne_one ha hb ha1 hba j (by rw [← hkx, pow_zero])
  rcases Nat.lt_or_ge 1 k with hk1 | hk1
  · exact (not_mul_pow_eq_pow ha hab (a_not_mem_zpowers_b ha hb ha1 hba) hk1 hklt hkx).elim
  · obtain rfl : k = 1 := by omega
    have hbij : b ^ i = b ^ j := mul_left_cancel (by rwa [pow_one] at hkx)
    exact Nat.ModEq.eq_of_lt_of_lt (hborder ▸ pow_eq_pow_iff_modEq.mp hbij) hi hj

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
