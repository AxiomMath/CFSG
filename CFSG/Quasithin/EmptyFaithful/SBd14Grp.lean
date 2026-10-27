module

public import CFSG.Quasithin.EmptyFaithful.SBd14LieG

public section

namespace CFSG.Quasithin.SBd14

open scoped commutatorElement

variable {G : Type} [Group G]

theorem normal_meets_center {X : Type*} [Group X]
    (hab : ∀ a b : X, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center X) {N : Subgroup X} (hN : N.Normal)
    (hNZ : ¬ N ≤ Subgroup.center X) : ∃ w ∈ N, w ≠ 1 ∧ w ∈ Subgroup.center X := by
  by_contra hno
  push Not at hno
  apply hNZ
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro x
  have h1 : n * x * n⁻¹ * x⁻¹ ∈ N := by
    have : n * (x * n⁻¹ * x⁻¹) ∈ N := N.mul_mem hn (hN.conj_mem _ (N.inv_mem hn) x)
    simpa [mul_assoc] using this
  have h2 : n * x * n⁻¹ * x⁻¹ = 1 := by
    by_contra hc1
    exact hno _ h1 hc1 (hab n x)
  have h3 : n * x = x * n := by
    calc n * x = (n * x * n⁻¹ * x⁻¹) * (x * n) := by group
      _ = x * n := by rw [h2, one_mul]
  exact h3.symm


theorem exists_pow_mul_eq {A : Type*} [CommGroup A] [Finite A] (hA : Nat.card A = 9)
    (hA3 : ∀ x : A, x ^ 3 = 1) {a b : A} (ha : a ≠ 1) (hb : b ∉ Subgroup.zpowers a) (x : A) :
    ∃ m n : ℤ, a ^ m * b ^ n = x := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf a = 3 := orderOf_eq_prime (hA3 a) ha
  set H := Subgroup.closure ({a, b} : Set A) with hH
  have hzH : Subgroup.zpowers a ≤ H := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := Subgroup.subset_closure (by simp)
  have hcard3 : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hord]
  have hdvd1 : 3 ∣ Nat.card H := hcard3 ▸ Subgroup.card_dvd_of_le hzH
  have hdvd2 : Nat.card H ∣ 9 := hA ▸ Subgroup.card_subgroup_dvd_card H
  have hne : Nat.card H ≠ 3 := by
    intro h
    have := Subgroup.eq_of_le_of_card_ge hzH (by rw [h, hcard3])
    exact hb (this ▸ hbH)
  have hle : Nat.card H ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd2
  have h9 : Nat.card H = 9 := by
    generalize Nat.card H = k at hdvd1 hdvd2 hne hle
    interval_cases k <;> omega
  have htop : H = ⊤ := Subgroup.eq_top_of_card_eq H (by rw [h9, hA])
  have hx : x ∈ H := htop ▸ Subgroup.mem_top x
  obtain ⟨m, n, hmn⟩ := Subgroup.mem_closure_pair.mp hx
  exact ⟨m, n, hmn⟩



section N0

theorem conj_mem_N0 {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) {x : G}
    (hx : x ∈ L ⊔ Subgroup.centralizer (L : Set G)) :
    g * x * g⁻¹ ∈ L ⊔ Subgroup.centralizer (L : Set G) := by
  have hcomm : ∀ a ∈ L, ∀ b ∈ Subgroup.centralizer (L : Set G), a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp hb a ha
  obtain ⟨l, hl, c, hc, rfl⟩ := mem_sup_of_commute' hcomm hx
  have e : g * (l * c) * g⁻¹ = (g * l * g⁻¹) * (g * c * g⁻¹) := by group
  rw [e]
  refine Subgroup.mul_mem_sup ((Subgroup.mem_normalizer_iff.mp hg l).mp hl) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 : g⁻¹ * x * g ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
    simpa using this
  have h2 := Subgroup.mem_centralizer_iff.mp hc _ h1
  calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [h2]
    _ = (g * c * g⁻¹) * x := by group

theorem pow_mul_form {N : Subgroup G} {n₀ c : G} (hn₀ : n₀ ∈ N)
    (hc : c ∈ Subgroup.normalizer (N : Set G)) (m : ℕ) : ∃ n ∈ N, (n₀ * c) ^ m = n * c ^ m := by
  induction m with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨n, hn, h⟩ := ih
    refine ⟨n * (c ^ m * n₀ * (c ^ m)⁻¹), N.mul_mem hn ?_, ?_⟩
    · have hcm : c ^ m ∈ Subgroup.normalizer (N : Set G) := Subgroup.pow_mem _ hc m
      exact (Subgroup.mem_normalizer_iff.mp hcm n₀).mp hn₀
    · rw [pow_succ, h]
      group

end N0

end CFSG.Quasithin.SBd14
