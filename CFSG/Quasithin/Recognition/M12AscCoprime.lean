module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin

open Subgroup

theorem fpf_inverts {A : Type*} [Group A] [Finite A] (σ : A →* A) (hσ : ∀ a, σ (σ a) = a)
    (hfix : ∀ a, σ a = a → a = 1) : ∀ a, σ a = a⁻¹ := by
  have hinj : Function.Injective (fun x : A => x⁻¹ * σ x) := by
    intro x y h
    have h' : (y * x⁻¹) = σ (y * x⁻¹) := by
      have h1 : y⁻¹ * σ y = x⁻¹ * σ x := h.symm
      calc y * x⁻¹ = y * (x⁻¹ * σ x) * (σ x)⁻¹ := by group
        _ = y * (y⁻¹ * σ y) * (σ x)⁻¹ := by rw [h1]
        _ = σ y * (σ x)⁻¹ := by group
        _ = σ (y * x⁻¹) := by rw [map_mul, map_inv]
    have h2 : y * x⁻¹ = 1 := hfix _ h'.symm
    calc x = (y * x⁻¹)⁻¹ * y := by group
      _ = y := by rw [h2]; group
  have hsurj : Function.Surjective (fun x : A => x⁻¹ * σ x) :=
    Finite.injective_iff_surjective.1 hinj
  intro a
  obtain ⟨x, rfl⟩ := hsurj a
  show σ (x⁻¹ * σ x) = (x⁻¹ * σ x)⁻¹
  rw [map_mul, map_inv, hσ]
  group

theorem exists_three_group_centralizing {G : Type*} [Group G] [Finite G] {x : G}
    (hx : orderOf x = 3) (h27 : 27 ∣ Nat.card G) :
    ∃ B : Subgroup G, B ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 3 B ∧ 9 ∣ Nat.card B := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXc : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hXp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1) (by rw [hXc]; norm_num)
  obtain ⟨T, hXT⟩ := hXp.exists_le_sylow
  have hTc : 27 ≤ Nat.card (T : Subgroup G) := by
    have h := Sylow.card_eq_multiplicity T
    have hf : 3 ≤ (Nat.card G).factorization 3 := by
      have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
      have : 3 ^ 3 ∣ Nat.card G := by simpa using h27
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hG0).1 this
    rw [h]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (Nat.card G).factorization 3 := Nat.pow_le_pow_right (by norm_num) hf
  have hlt : (zpowers x).subgroupOf (T : Subgroup G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have : Nat.card (T : Subgroup G) ≤ 3 := by
      have hle : (T : Subgroup G) ≤ zpowers x := fun g hg => by
        have : (⟨g, hg⟩ : ↥(T : Subgroup G)) ∈ (zpowers x).subgroupOf (T : Subgroup G) := by
          rw [htop]; trivial
        exact Subgroup.mem_subgroupOf.1 this
      have := Subgroup.card_le_of_le hle
      omega
    omega
  have hTnil : Group.IsNilpotent ↥(T : Subgroup G) := T.isPGroup'.isNilpotent
  obtain ⟨⟨n, hnT⟩, hnN, hnX⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hnXn : n ∉ zpowers x := fun h => hnX (Subgroup.mem_subgroupOf.2 h)
  have hnnorm : n * x * n⁻¹ ∈ zpowers x := by
    have h1 : (⟨x, hXT (Subgroup.mem_zpowers x)⟩ : ↥(T : Subgroup G)) ∈
        (zpowers x).subgroupOf (T : Subgroup G) := Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers x)
    have h2 := (Subgroup.mem_normalizer_iff.1 hnN _).1 h1
    exact Subgroup.mem_subgroupOf.1 h2
  obtain ⟨k, hk⟩ := T.isPGroup' ⟨n, hnT⟩
  have hnk : n ^ (3 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hxi : x⁻¹ = x * x := inv_eq_of_mul_eq_one_right (by
    have h3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    calc x * (x * x) = x * x * x := (mul_assoc x x x).symm
      _ = x ^ 3 := by rw [pow_succ, pow_two]
      _ = 1 := h3)
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have hcomm : n * x = x * n := by
    by_contra hne
    have hne' : n * x * n⁻¹ ≠ x := fun h => hne (by
      calc n * x = (n * x * n⁻¹) * n := by group
        _ = x * n := by rw [h])
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hnnorm
    have hjmod : x ^ j = x ^ (j % (3 : ℕ)) := by
      rw [← zpow_mod_orderOf, hx]
    have hmod : j % (3 : ℕ) = 0 ∨ j % (3 : ℕ) = 1 ∨ j % (3 : ℕ) = 2 := by omega
    have hconj : n * x * n⁻¹ = x⁻¹ := by
      rcases hmod with h | h | h
      · exfalso
        rw [h, zpow_zero] at hjmod
        rw [hjmod] at hj
        apply hx1
        have : x = n⁻¹ * (n * x * n⁻¹) * n := by group
        rw [← hj] at this
        simpa using this
      · exfalso
        rw [h, zpow_one] at hjmod
        exact hne' (by rw [← hj, hjmod])
      · rw [h] at hjmod
        rw [← hj, hjmod, hxi]
        exact zpow_two x
    have hpow : ∀ i : ℕ, n ^ i * x * (n ^ i)⁻¹ = if i % 2 = 0 then x else x⁻¹ := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have e : n ^ (i + 1) * x * (n ^ (i + 1))⁻¹ = n * (n ^ i * x * (n ^ i)⁻¹) * n⁻¹ := by
          rw [pow_succ']; group
        rw [e, ih]
        by_cases h0 : i % 2 = 0
        · have h1 : (i + 1) % 2 = 1 := by omega
          simp [h0, h1, hconj]
        · have h1 : (i + 1) % 2 = 0 := by omega
          simp only [h0, h1, ite_false, ite_true]
          have : n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ := by group
          rw [this, hconj, inv_inv]
    have hodd : 3 ^ k % 2 = 1 := by
      rw [Nat.pow_mod]
      simp
    have hx2 : x = x⁻¹ := by
      have h := hpow (3 ^ k)
      rw [hnk, hodd] at h
      simpa using h
    have hxx : x ^ 2 = 1 := by
      calc x ^ 2 = x * x := pow_two x
        _ = x * x⁻¹ := by rw [← hx2]
        _ = 1 := mul_inv_cancel x
    have := orderOf_dvd_of_pow_eq_one hxx
    rw [hx] at this
    omega
  have hBT : zpowers x ⊔ zpowers n ≤ (T : Subgroup G) :=
    sup_le hXT ((Subgroup.zpowers_le).2 hnT)
  have hBC : zpowers x ⊔ zpowers n ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le ((Subgroup.zpowers_le).2 ?_) ((Subgroup.zpowers_le).2 ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    · exact Subgroup.mem_centralizer_singleton_iff.2 hcomm
  have hBp : IsPGroup 3 ↥(zpowers x ⊔ zpowers n) := T.isPGroup'.to_le hBT
  refine ⟨zpowers x ⊔ zpowers n, hBC, hBp, ?_⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).1 hBp
  have hXB : zpowers x ≤ zpowers x ⊔ zpowers n := le_sup_left
  have hnB : n ∈ zpowers x ⊔ zpowers n := Subgroup.mem_sup_right (Subgroup.mem_zpowers n)
  have hj2 : 2 ≤ j := by
    by_contra hj2
    push Not at hj2
    have hdvd : Nat.card (zpowers x) ∣ Nat.card ↥(zpowers x ⊔ zpowers n) :=
      Subgroup.card_dvd_of_le hXB
    rw [hXc, hj] at hdvd
    interval_cases j
    · simp at hdvd
    · have : zpowers x = zpowers x ⊔ zpowers n :=
        Subgroup.eq_of_le_of_card_ge hXB (by rw [hj, hXc]; norm_num)
      exact hnXn (this ▸ hnB)
  rw [hj]
  calc 9 = 3 ^ 2 := by norm_num
    _ ∣ 3 ^ j := pow_dvd_pow 3 hj2

end CFSG.Quasithin
