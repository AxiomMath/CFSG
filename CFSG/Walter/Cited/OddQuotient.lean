module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Walter.Suzuki

variable {M : Type*} [Group M] [Finite M] (O : Subgroup M) [O.Normal]

omit [Finite M] [O.Normal] in
theorem eq_one_of_pow_two_pow_eq_one {x : M} (hO : Odd (Nat.card O)) (hx : x ∈ O) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ Nat.card O := O.orderOf_dvd_natCard hx
  have hcop : Nat.Coprime (2 ^ k) (Nat.card O) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hO)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem exists_orderOf_eq_two_mk_eq (hO : Odd (Nat.card O)) {x : M ⧸ O} (hx : orderOf x = 2) :
    ∃ t : M, orderOf t = 2 ∧ (t : M ⧸ O) = x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hx2 : (g : M ⧸ O) ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one _
  have hmk : ((g ^ m : M) : M ⧸ O) = g := by
    obtain ⟨j, rfl⟩ := hm
    rw [QuotientGroup.mk_pow, pow_succ, pow_mul, hx2, one_pow, one_mul]
  have hpow : (g ^ m) ^ 2 ^ k = 1 := by
    rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  have hsq : (g ^ m) ^ 2 = 1 := by
    have hmem : (g ^ m) ^ 2 ∈ O := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hmk, hx2]
    refine eq_one_of_pow_two_pow_eq_one O hO hmem (k := k) ?_
    rw [← pow_mul, mul_comm, pow_mul, hpow, one_pow]
  refine ⟨g ^ m, orderOf_eq_prime hsq fun h1 => ?_, hmk⟩
  have : (g : M ⧸ O) = 1 := by rw [← hmk, h1, QuotientGroup.mk_one]
  rw [this, orderOf_one] at hx
  exact absurd hx (by norm_num)

omit [Finite M] in
theorem exists_commute_mk_eq (hO : Odd (Nat.card O)) {t : M} (ht : t * t = 1) {x : M}
    (hx : (x : M ⧸ O) * (t : M ⧸ O) = (t : M ⧸ O) * (x : M ⧸ O)) :
    ∃ c : M, c * t = t * c ∧ (c : M ⧸ O) = x := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  set u := t * (x * t * x⁻¹) with hu
  have huO : u ∈ O := by
    rw [← QuotientGroup.eq_one_iff, hu, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx, mul_inv_cancel_right,
      ← QuotientGroup.mk_mul, ht, QuotientGroup.mk_one]
  have hinv : t * u * t⁻¹ = u⁻¹ := by
    rw [hu]
    calc t * (t * (x * t * x⁻¹)) * t⁻¹ = (t * t) * (x * t * x⁻¹) * t⁻¹ := by group
      _ = x * t * x⁻¹ * t⁻¹ := by rw [ht, one_mul]
      _ = x * t⁻¹ * x⁻¹ * t⁻¹ := by rw [htinv]
      _ = (t * (x * t * x⁻¹))⁻¹ := by group
  obtain ⟨j, hj⟩ : Odd (orderOf u) := hO.of_dvd_nat (O.orderOf_dvd_natCard huO)
  set v := u ^ (j + 1) with hv
  have hvv : v * v = u := by
    rw [hv, ← pow_add, show j + 1 + (j + 1) = orderOf u + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hvO : v ∈ O := O.pow_mem huO _
  have htv : t * v * t⁻¹ = v⁻¹ := by
    rw [hv, ← conj_pow, hinv, inv_pow]
  refine ⟨v * x, ?_, ?_⟩
  · have hxt : x * t = t * u * x := by
      rw [hu, ← mul_assoc, ht, one_mul, inv_mul_cancel_right]
    have hvt : v * t = t * v⁻¹ := by
      calc v * t = t * (t⁻¹ * v * t) := by group
        _ = t * (t * v * t⁻¹) := by rw [htinv]
        _ = t * v⁻¹ := by rw [htv]
    calc v * x * t = v * (x * t) := by group
      _ = v * (t * u * x) := by rw [hxt]
      _ = v * t * (v * v) * x := by rw [hvv]; group
      _ = t * v⁻¹ * (v * v) * x := by rw [hvt]
      _ = t * (v * x) := by group
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff v).mpr hvO, one_mul]

omit [Finite M] in
theorem centralizer_mk_le_map (hO : Odd (Nat.card O)) {t : M} (ht : t * t = 1) :
    Subgroup.centralizer ({(t : M ⧸ O)} : Set (M ⧸ O)) ≤
      (Subgroup.centralizer ({t} : Set M)).map (QuotientGroup.mk' O) := by
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rw [Subgroup.mem_centralizer_singleton_iff] at hy
  obtain ⟨c, hc, hcx⟩ := exists_commute_mk_eq O hO ht hy
  exact ⟨c, Subgroup.mem_centralizer_singleton_iff.mpr hc, hcx⟩

theorem normal_of_normal_map (hO : Odd (Nat.card O)) {S : Subgroup M} (hS : IsPGroup 2 S)
    (hSO : S ≤ Subgroup.centralizer (O : Set M)) (hn : (S.map (QuotientGroup.mk' O)).Normal) :
    S.Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
  have hexp : ∀ s ∈ S, s ^ 2 ^ k = 1 := fun s hs => by
    have h : (⟨s, hs⟩ : S) ^ Nat.card S = 1 := pow_card_eq_one'
    rw [← hk]
    exact congrArg Subtype.val h
  refine ⟨fun s hs g => ?_⟩
  have hmem : ((g * s * g⁻¹ : M) : M ⧸ O) ∈ S.map (QuotientGroup.mk' O) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hn.conj_mem _ ⟨s, hs, rfl⟩ _
  obtain ⟨s', hs', hs'eq⟩ := hmem
  set o := s'⁻¹ * (g * s * g⁻¹) with ho
  have hoO : o ∈ O := by
    rw [← QuotientGroup.eq_one_iff, ho, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    change ((QuotientGroup.mk' O) s')⁻¹ * _ = 1
    rw [hs'eq, inv_mul_cancel]
  have hcomm : Commute s' o :=
    (Subgroup.mem_centralizer_iff.mp (hSO hs') o hoO).symm
  have ho1 : o = 1 := by
    refine eq_one_of_pow_two_pow_eq_one O hO hoO (k := k) ?_
    have hgs : (g * s * g⁻¹) ^ 2 ^ k = 1 := by rw [conj_pow, hexp s hs, mul_one, mul_inv_cancel]
    have h := hcomm.mul_pow (2 ^ k)
    rw [ho, mul_inv_cancel_left, hgs, hexp s' hs', one_mul] at h
    exact h.symm
  have : g * s * g⁻¹ = s' := by
    rw [ho, inv_mul_eq_one] at ho1
    exact ho1.symm
  rw [this]
  exact hs'

end CFSG.Walter.Suzuki
