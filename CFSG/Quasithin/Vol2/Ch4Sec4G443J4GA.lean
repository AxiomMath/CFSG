module

public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4R

public section

namespace CFSG.Quasithin.H13.Ch4.G443J4

open CFSG.Open CFSG.Quasithin

variable {X : Type} [Group X] [Finite X]

theorem factorization_two_pow_mul {m n : ℕ} (hn : ¬ 2 ∣ n) (hn0 : n ≠ 0) :
    (2 ^ m * n).factorization 2 = m := by
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hn0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hn, add_zero]

theorem card_modEq_card_centralizer {q : ℕ} [Fact q.Prime] {V : Subgroup X} {y : X}
    (hy : orderOf y = q) (hyV : y ∈ Subgroup.normalizer (V : Set X)) :
    Nat.card V ≡ Nat.card ↥((Subgroup.centralizer ({y} : Set X)).subgroupOf V) [MOD q] := by
  set A := Subgroup.zpowers y with hA
  have hAp : IsPGroup q ↥A := IsPGroup.of_card (n := 1) (by rw [hA, Nat.card_zpowers, hy, pow_one])
  have hAV : A ≤ Subgroup.normalizer (V : Set X) := Subgroup.zpowers_le.mpr hyV
  have hmem : ∀ (a : ↥A) (v : ↥V), (a : X) * v * (a : X)⁻¹ ∈ V := fun a v =>
    (Subgroup.mem_normalizer_iff.mp (hAV a.2) v).mp v.2
  let _ : MulAction ↥A ↥V :=
    { smul := fun a v => ⟨a * v * a⁻¹, hmem a v⟩
      one_smul := fun v => Subtype.ext (by
        show ((1 : ↥A) : X) * v * ((1 : ↥A) : X)⁻¹ = v
        simp)
      mul_smul := fun a b v => Subtype.ext (by
        show ((a * b : ↥A) : X) * v * ((a * b : ↥A) : X)⁻¹ =
          (a : X) * ((b : X) * v * (b : X)⁻¹) * (a : X)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have h := hAp.card_modEq_card_fixedPoints ↥V
  have hfix : Nat.card (MulAction.fixedPoints ↥A ↥V) =
      Nat.card ↥((Subgroup.centralizer ({y} : Set X)).subgroupOf V) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    rw [MulAction.mem_fixedPoints, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hv
      have h1 : y * (v : X) * y⁻¹ = v := congrArg Subtype.val (hv ⟨y, Subgroup.mem_zpowers y⟩)
      calc (v : X) * y = (y * (v : X) * y⁻¹) * y := by rw [h1]
        _ = y * v := by group
    · intro hv a
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp a.2
      have hc : Commute (v : X) (a : X) := hn ▸ (Commute.zpow_right hv n)
      apply Subtype.ext
      show (a : X) * v * (a : X)⁻¹ = v
      rw [← hc.eq, mul_inv_cancel_right]
  rwa [hfix] at h

theorem two_pow_eleven_le_card {V : Subgroup X} (hV2 : IsPGroup 2 ↥V) {y : X}
    (hy : orderOf y = 23) (hyV : y ∈ Subgroup.normalizer (V : Set X))
    (hyc : ¬ V ≤ Subgroup.centralizer ({y} : Set X)) : 2 ^ 11 ≤ Nat.card V := by
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := card_modEq_card_centralizer hy hyV
  set W := (Subgroup.centralizer ({y} : Set X)).subgroupOf V with hW
  obtain ⟨a, ha⟩ := hV2.exists_card_eq
  obtain ⟨b, hb⟩ := (hV2.to_subgroup W).exists_card_eq
  have hWV : Nat.card W ∣ Nat.card V := Subgroup.card_subgroup_dvd_card W
  have hne : Nat.card W ≠ Nat.card V := by
    intro hc
    apply hyc
    have htop : W = ⊤ := (Subgroup.card_eq_iff_eq_top W).mp hc
    intro v hv
    have : (⟨v, hv⟩ : ↥V) ∈ W := htop ▸ Subgroup.mem_top _
    exact this
  rw [ha, hb] at hWV hne h
  have hba : b < a := lt_of_le_of_ne ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hWV)
    fun e => hne (by rw [e])
  obtain ⟨k, rfl⟩ : ∃ k, a = b + k := ⟨a - b, by omega⟩
  have hk : 0 < k := by omega
  have h2 : 23 ∣ 2 ^ b * (2 ^ k - 1) := by
    have h3 := (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right (by norm_num) (by omega))).mp h.symm
    rwa [pow_add, ← Nat.mul_sub_one] at h3
  have h3 : 23 ∣ 2 ^ k - 1 :=
    Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_right b (by norm_num)) h2
  have hk11 : 11 ≤ k := by
    by_contra hlt
    push Not at hlt
    interval_cases k <;> norm_num at h3
  calc 2 ^ 11 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk11
    _ ≤ 2 ^ (b + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = Nat.card V := ha.symm

theorem le_centralizer_of_card_lt {q : ℕ} [Fact q.Prime] {V : Subgroup X} {y : X}
    (hy : orderOf y = q) (hyV : y ∈ Subgroup.normalizer (V : Set X)) (hVq : Nat.card V < q) :
    V ≤ Subgroup.centralizer ({y} : Set X) := by
  have h := card_modEq_card_centralizer hy hyV
  set W := (Subgroup.centralizer ({y} : Set X)).subgroupOf V with hW
  have hWV : Nat.card W ≤ Nat.card V := Subgroup.card_le_card_group W
  have heq : Nat.card W = Nat.card V := h.symm.eq_of_lt_of_lt (lt_of_le_of_lt hWV hVq) hVq
  have htop : W = ⊤ := (Subgroup.card_eq_iff_eq_top W).mp heq
  intro v hv
  have : (⟨v, hv⟩ : ↥V) ∈ W := htop ▸ Subgroup.mem_top _
  exact this

end CFSG.Quasithin.H13.Ch4.G443J4
