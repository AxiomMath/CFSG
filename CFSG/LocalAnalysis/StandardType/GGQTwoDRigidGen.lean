module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.StandardType.QTwo

variable {S : Type*} [Group S]

private lemma eq_one_of_pow_two_pow_eq_one_of_pow_odd {G : Type*} [Group G] {x : G}
    {k n : ℕ} (h2 : x ^ 2 ^ k = 1) (hn : Odd n) (hn1 : x ^ n = 1) : x = 1 := by
  have hdvd2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2
  have hdvdn : orderOf x ∣ n := orderOf_dvd_of_pow_eq_one hn1
  have hcop : Nat.Coprime n (2 ^ k) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · exact (Nat.coprime_pow_right_iff hk n 2).mpr hn.coprime_two_right
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvdn hdvd2)

theorem mulAut_apply_eq_self_of_mem_normalizer_of_odd (α : MulAut S) {A : Subgroup S}
    (hαA : ∀ a ∈ A, α a = a) (hC : ∀ y : S, (∀ a ∈ A, y * a = a * y) → y ∈ A)
    (hodd : ∀ a ∈ A, ∃ n : ℕ, Odd n ∧ a ^ n = 1) {k : ℕ} (hk : α ^ 2 ^ k = 1) {x : S}
    (hx : x ∈ Subgroup.normalizer (A : Set S)) : α x = x := by
  set τ : S := x⁻¹ * α x with hτdef
  have hτcomm : ∀ a ∈ A, τ * a = a * τ := by
    intro a ha
    have hxa : x * a * x⁻¹ ∈ A :=
      ((Subgroup.mem_normalizer_iff (H := A) (g := x)).mp hx a).mp ha
    have hα : α (x * a * x⁻¹) = x * a * x⁻¹ := hαA _ hxa
    simp only [map_mul, map_inv, hαA a ha] at hα
    have hconj : τ * a * τ⁻¹ = a := by
      rw [hτdef]
      calc
        (x⁻¹ * α x) * a * ((x⁻¹ * α x))⁻¹
            = x⁻¹ * (α x * a * (α x)⁻¹) * x := by group
        _ = x⁻¹ * (x * a * x⁻¹) * x := by rw [hα]
        _ = a := by group
    calc
      τ * a = (τ * a * τ⁻¹) * τ := by group
      _ = a * τ := by rw [hconj]
  have hτA : τ ∈ A := hC τ hτcomm
  have hατ : α τ = τ := hαA τ hτA
  have hτx : α x = x * τ := by
    rw [hτdef]
    group
  have hpow : ∀ n : ℕ, (α ^ n) x = x * τ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hατ, hτx, pow_succ]
      group
  have h2k : τ ^ 2 ^ k = 1 := by
    have h := hpow (2 ^ k)
    rw [hk, MulAut.one_apply] at h
    exact mul_left_cancel (a := x) (by simpa using h.symm)
  obtain ⟨n, hnodd, hn1⟩ := hodd τ hτA
  have hτ1 : τ = 1 := eq_one_of_pow_two_pow_eq_one_of_pow_odd h2k hnodd hn1
  rw [hτ1, mul_one] at hτx
  exact hτx

theorem commute_of_selfCentralizing_odd {U A : Subgroup S}
    (hC : ∀ y ∈ U, (∀ a ∈ A, y * a = a * y) → y ∈ A)
    (hodd : ∀ a ∈ A, ∃ n : ℕ, Odd n ∧ a ^ n = 1) {u : S} {k : ℕ} (hu : u ^ 2 ^ k = 1)
    (huU : u ∈ Subgroup.normalizer (U : Set S)) (huA : ∀ a ∈ A, u * a = a * u) {y : S}
    (hyU : y ∈ U) (hyA : y ∈ Subgroup.normalizer (A : Set S)) : u * y = y * u := by
  set τ : S := y⁻¹ * (u * y * u⁻¹) with hτdef
  have hyU' : u * y * u⁻¹ ∈ U :=
    ((Subgroup.mem_normalizer_iff (H := U) (g := u)).mp huU y).mp hyU
  have hτU : τ ∈ U := by
    rw [hτdef]
    exact U.mul_mem (U.inv_mem hyU) hyU'
  have hτcomm : ∀ a ∈ A, τ * a = a * τ := by
    intro a ha
    have hua : u⁻¹ * a * u = a := by
      calc
        u⁻¹ * a * u = u⁻¹ * (a * u) := by group
        _ = u⁻¹ * (u * a) := by rw [← huA a ha]
        _ = a := by group
    have hya : y * a * y⁻¹ ∈ A :=
      ((Subgroup.mem_normalizer_iff (H := A) (g := y)).mp hyA a).mp ha
    have huya : u * (y * a * y⁻¹) * u⁻¹ = y * a * y⁻¹ := by
      have h := huA (y * a * y⁻¹) hya
      calc
        u * (y * a * y⁻¹) * u⁻¹ = (y * a * y⁻¹) * u * u⁻¹ := by rw [h]
        _ = y * a * y⁻¹ := by group
    have hconj : τ * a * τ⁻¹ = a := by
      rw [hτdef]
      calc
        (y⁻¹ * (u * y * u⁻¹)) * a * (y⁻¹ * (u * y * u⁻¹))⁻¹
            = y⁻¹ * u * y * (u⁻¹ * a * u) * y⁻¹ * u⁻¹ * y := by group
        _ = y⁻¹ * u * (y * a * y⁻¹) * u⁻¹ * y := by rw [hua]; group
        _ = y⁻¹ * (u * (y * a * y⁻¹) * u⁻¹) * y := by group
        _ = y⁻¹ * (y * a * y⁻¹) * y := by rw [huya]
        _ = a := by group
    calc
      τ * a = (τ * a * τ⁻¹) * τ := by group
      _ = a * τ := by rw [hconj]
  have hτA : τ ∈ A := hC τ hτU hτcomm
  have huτ : u * τ * u⁻¹ = τ := by
    have h := huA τ hτA
    calc
      u * τ * u⁻¹ = τ * u * u⁻¹ := by rw [h]
      _ = τ := by group
  have huy : u * y * u⁻¹ = y * τ := by
    rw [hτdef]
    group
  have hconjpow : ∀ n : ℕ, u * τ ^ n * u⁻¹ = τ ^ n := by
    intro n
    have h : (MulAut.conj u) (τ ^ n) = τ ^ n := by
      rw [map_pow, show (MulAut.conj u) τ = τ by simpa [MulAut.conj_apply] using huτ]
    simpa [MulAut.conj_apply] using h
  have hpow : ∀ n : ℕ, u ^ n * y * (u ^ n)⁻¹ = y * τ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ']
      calc
        (u * u ^ n) * y * (u * u ^ n)⁻¹
            = u * (u ^ n * y * (u ^ n)⁻¹) * u⁻¹ := by group
        _ = u * (y * τ ^ n) * u⁻¹ := by rw [ih]
        _ = (u * y * u⁻¹) * (u * τ ^ n * u⁻¹) := by group
        _ = (y * τ) * τ ^ n := by rw [huy, hconjpow]
        _ = y * τ ^ (n + 1) := by rw [pow_succ]; group
  have h2k : τ ^ 2 ^ k = 1 := by
    have h := hpow (2 ^ k)
    rw [hu, one_mul, inv_one, mul_one] at h
    exact mul_left_cancel (a := y) (by simpa using h.symm)
  obtain ⟨n, hnodd, hn1⟩ := hodd τ hτA
  have hτ1 : τ = 1 := eq_one_of_pow_two_pow_eq_one_of_pow_odd h2k hnodd hn1
  have huy' : u * y * u⁻¹ = y := by
    rw [hτ1, mul_one] at huy
    exact huy
  calc
    u * y = (u * y * u⁻¹) * u := by group
    _ = y * u := by rw [huy']

private lemma mem_zpowers_of_commute_of_card_six {G : Type*} [Group G] [Finite G]
    (h6 : Nat.card G = 6) (hna : ¬ IsMulCommutative G) {c : G} (hc : orderOf c = 3)
    {y : G} (hy : y * c = c * y) : y ∈ Subgroup.zpowers c := by
  by_contra hyc
  let K : Subgroup G := Subgroup.closure ({y, c} : Set G)
  have hHK : Subgroup.zpowers c ≤ K := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  have hyK : y ∈ K := Subgroup.subset_closure (by simp)
  have hne : Subgroup.zpowers c ≠ K := fun hEq => hyc (hEq.symm ▸ hyK)
  have hlt : Subgroup.zpowers c < K := lt_of_le_of_ne hHK hne
  have hcardH : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, hc]
  have hdvd : Nat.card K ∣ 6 := by
    rw [← h6]
    exact Subgroup.card_subgroup_dvd_card K
  have hgt : 3 < Nat.card K := by
    rw [← hcardH]
    exact Subgroup.card_lt_of_lt hlt
  have hcardK : Nat.card K = 6 := by
    have hle : Nat.card K ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    have hcases : Nat.card K = 4 ∨ Nat.card K = 5 ∨ Nat.card K = 6 := by omega
    rcases hcases with h | h | h
    · rw [h] at hdvd
      exact absurd hdvd (by norm_num)
    · rw [h] at hdvd
      exact absurd hdvd (by norm_num)
    · exact h
  have hKtop : K = ⊤ := Subgroup.eq_top_of_card_eq K (by rw [hcardK, h6])
  have hyne : y ≠ c := by
    intro h
    rw [h] at hyc
    exact hyc (Subgroup.mem_zpowers c)
  have hpair : ({y, c} : Set G).Pairwise Commute := by
    rw [Set.pairwise_pair]
    intro _
    exact ⟨hy, hy.symm⟩
  have hKcomm : IsMulCommutative K := Subgroup.isMulCommutative_closure hpair
  refine hna (IsMulCommutative.of_comm fun a b => ?_)
  have haK : a ∈ K := by rw [hKtop]; trivial
  have hbK : b ∈ K := by rw [hKtop]; trivial
  exact congrArg Subtype.val (hKcomm.is_comm.comm ⟨a, haK⟩ ⟨b, hbK⟩)

theorem commute_of_card_six {U : Subgroup S} (h6 : Nat.card U = 6)
    (hna : ∃ a ∈ U, ∃ b ∈ U, a * b ≠ b * a) {u : S} {k : ℕ} (hu : u ^ 2 ^ k = 1)
    (huU : u ∈ Subgroup.normalizer (U : Set S)) (hc : ∀ c ∈ U, c ^ 3 = 1 → u * c = c * u) :
    ∀ y ∈ U, u * y = y * u := by
  have hfinU : Finite U := Nat.finite_of_card_ne_zero (by omega)
  have hnaU : ¬ IsMulCommutative U := by
    rintro ⟨hcomm⟩
    obtain ⟨a, ha, b, hb, hab⟩ := hna
    exact hab (congrArg Subtype.val (hcomm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  have h3prime : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨cU, hcUord⟩ :=
    @exists_prime_orderOf_dvd_card' U _ hfinU 3 h3prime (by rw [h6]; norm_num)
  let c : S := cU
  have hcU : c ∈ U := cU.2
  have hc3 : c ^ 3 = 1 := by
    have h : cU ^ 3 = 1 := by
      simpa [hcUord] using pow_orderOf_eq_one cU
    simpa [c] using congrArg Subtype.val h
  have hc_ord : orderOf c = 3 := by
    rw [show c = (cU : S) from rfl, Subgroup.orderOf_coe, hcUord]
  have huc : u * c = c * u := hc c hcU hc3
  have hodd : ∀ a ∈ Subgroup.zpowers c, ∃ n : ℕ, Odd n ∧ a ^ n = 1 := by
    intro a ha
    refine ⟨3, by decide, ?_⟩
    have hdvd : orderOf a ∣ Nat.card (Subgroup.zpowers c) :=
      (Subgroup.zpowers c).orderOf_dvd_natCard ha
    rw [Nat.card_zpowers, hc_ord] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have huA : ∀ a ∈ Subgroup.zpowers c, u * a = a * u := by
    intro a ha
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact Commute.zpow_right huc m
  have hC : ∀ y ∈ U, (∀ a ∈ Subgroup.zpowers c, y * a = a * y) →
      y ∈ Subgroup.zpowers c := by
    intro y hyU hycomm
    let yU : U := ⟨y, hyU⟩
    have hcommU : yU * cU = cU * yU := by
      apply Subtype.ext
      simpa [yU, c] using hycomm c (Subgroup.mem_zpowers c)
    have hmemU : yU ∈ Subgroup.zpowers cU :=
      @mem_zpowers_of_commute_of_card_six U _ hfinU h6 hnaU cU hcUord yU hcommU
    have hmemMap : y ∈ Subgroup.map U.subtype (Subgroup.zpowers cU) :=
      Subgroup.mem_map_of_mem U.subtype hmemU
    simpa [MonoidHom.map_zpowers, c] using hmemMap
  have hHU : Subgroup.zpowers c ≤ U := Subgroup.zpowers_le.mpr hcU
  have hcardH : Nat.card ((Subgroup.zpowers c).subgroupOf U) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHU).toEquiv, Nat.card_zpowers, hc_ord]
  have hidx : ((Subgroup.zpowers c).subgroupOf U).index = 2 := by
    have hmul := ((Subgroup.zpowers c).subgroupOf U).index_mul_card
    rw [hcardH, h6] at hmul
    omega
  have hnorm : ((Subgroup.zpowers c).subgroupOf U).Normal :=
    Subgroup.normal_of_index_eq_two hidx
  have hle : U ≤ Subgroup.normalizer (Subgroup.zpowers c) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHU).mp hnorm
  intro y hyU
  exact commute_of_selfCentralizing_odd hC hodd hu huU huA hyU (hle hyU)

end CFSG.StandardType.QTwo

end
