module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporPlane

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

namespace Spor

variable {K : Type*} [Group K]

theorem planeOK_of_gens {A : Subgroup K} {Γ : Set K} (hΓ : Γ ⊆ centSet A) (hgen : Subgroup.closure Γ = ⊤) :
    PlaneOK A := by
  left
  rw [eq_top_iff, ← hgen]
  exact Subgroup.closure_mono hΓ

theorem le_closure_centSet {A : Subgroup K} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    A ≤ Subgroup.closure (centSet A) := by
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure ⟨x, hx, hx1, rfl⟩

theorem inv_mem_centSet {A : Subgroup K} {k : K} (hk : k ∈ centSet A) : k⁻¹ ∈ centSet A := by
  obtain ⟨a, ha, ha1, hak⟩ := hk
  refine ⟨a, ha, ha1, ?_⟩
  calc a * k⁻¹ = k⁻¹ * (k * a) * k⁻¹ := by group
    _ = k⁻¹ * (a * k) * k⁻¹ := by rw [hak]
    _ = k⁻¹ * a := by group

theorem eq_one_of_isPGroup_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {N A : Subgroup K} (hN : IsPGroup 2 N)
    (hA : IsPGroup p A) {x : K} (hxN : x ∈ N) (hxA : x ∈ A) : x = 1 := by
  obtain ⟨m, hm⟩ := hN ⟨x, hxN⟩
  obtain ⟨k, hk⟩ := hA ⟨x, hxA⟩
  have hm' : x ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hk' : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (2 ^ m) (p ^ k) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have h1 := orderOf_dvd_of_pow_eq_one hm'
  have h2 := orderOf_dvd_of_pow_eq_one hk'
  have h3 : orderOf x ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem eq_bot_of_le_closure_centSet {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup K}
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAp : IsPGroup p A)
    (hnorm : ∀ k ∈ centSet A, ∀ x ∈ A, k * x * k⁻¹ ∈ A)
    (hcent : ∀ k : K, (∀ x ∈ A, k * x = x * k) → k ∈ A)
    {N : Subgroup K} (hNH : N ≤ Subgroup.closure (centSet A)) (hN2 : IsPGroup 2 N)
    (hHN : Subgroup.closure (centSet A) ≤ normalizer (N : Set K)) : N = ⊥ := by
  have hHA : Subgroup.closure (centSet A) ≤ normalizer (A : Set K) := by
    rw [Subgroup.closure_le]
    intro k hk
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hnorm k hk x
    · intro hx
      have := hnorm k⁻¹ (inv_mem_centSet hk) _ hx
      simpa [mul_assoc] using this
  have hAH := le_closure_centSet hAc
  rw [eq_bot_iff]
  intro n hn
  have hcomm : ∀ x ∈ A, n * x = x * n := by
    intro x hx
    have hcA : n * x * n⁻¹ * x⁻¹ ∈ A :=
      A.mul_mem ((Subgroup.mem_normalizer_iff.1 (hHA (hNH hn)) x).1 hx) (A.inv_mem hx)
    have hcN : n * x * n⁻¹ * x⁻¹ ∈ N := by
      have h1 : x * n⁻¹ * x⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.1 (hHN (hAH hx)) n⁻¹).1 (N.inv_mem hn)
      have h2 := N.mul_mem hn h1
      simpa [mul_assoc] using h2
    have h1 := eq_one_of_isPGroup_two hp hp2 hN2 hAp hcN hcA
    calc n * x = (n * x * n⁻¹ * x⁻¹) * x * n := by group
      _ = x * n := by rw [h1, one_mul]
  have hnA := hcent n hcomm
  exact Subgroup.mem_bot.2 (eq_one_of_isPGroup_two hp hp2 hN2 hAp hn hnA)

theorem eq_one_of_fix {A : Subgroup K} {C : Set K} (hC : C ⊆ centSet A) {y f₀ f₁ f₀' f₁' : K}
    (hf₀ : f₀ ∈ Subgroup.closure C) (hf₁ : f₁ ∈ Subgroup.closure C) (hf₀' : f₀' ∈ Subgroup.closure C)
    (hf₁' : f₁' ∈ Subgroup.closure C) (hy₀ : y * f₀ = f₀' * y) (hy₁ : y * f₁ = f₁' * y)
    (hcen : ∀ k : K, k * f₀ = f₀ * k → k * f₁ = f₁ * k → k = 1)
    (hgen : Subgroup.closure (C ∪ {y}) = ⊤) {α : MulAut K}
    (hα : ∀ k ∈ Subgroup.closure (centSet A), α k = k) : α = 1 := by
  have hCH : Subgroup.closure C ≤ Subgroup.closure (centSet A) := Subgroup.closure_mono hC
  have hfix : ∀ k ∈ Subgroup.closure C, α k = k := fun k hk => hα k (hCH hk)
  have key : ∀ {f f' : K}, f ∈ Subgroup.closure C → f' ∈ Subgroup.closure C → y * f = f' * y →
      (y⁻¹ * α y) * f = f * (y⁻¹ * α y) := by
    intro f f' hf hf' hyf
    have h1 : α y * f = f' * α y := by
      have := congrArg α hyf
      rwa [map_mul, map_mul, hfix f hf, hfix f' hf'] at this
    have h2 : f' = y * f * y⁻¹ := by rw [hyf, mul_inv_cancel_right]
    calc (y⁻¹ * α y) * f = y⁻¹ * (α y * f) := by group
      _ = y⁻¹ * (f' * α y) := by rw [h1]
      _ = y⁻¹ * (y * f * y⁻¹ * α y) := by rw [h2]
      _ = f * (y⁻¹ * α y) := by group
  have hw := hcen _ (key hf₀ hf₀' hy₀) (key hf₁ hf₁' hy₁)
  have hαy : α y = y := by
    have := congrArg (y * ·) hw
    simpa using this
  have hle : Subgroup.closure (C ∪ {y}) ≤ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id K) := by
    rw [Subgroup.closure_le]
    rintro k (hk | hk)
    · exact hfix k (Subgroup.subset_closure hk)
    · rw [Set.mem_singleton_iff] at hk
      rw [hk]
      exact hαy
  rw [hgen] at hle
  ext k
  exact hle (Subgroup.mem_top k)

theorem planeOK_of_exc {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup K}
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAp : IsPGroup p A)
    (hnorm : ∀ k ∈ centSet A, ∀ x ∈ A, k * x * k⁻¹ ∈ A)
    (hcent : ∀ k : K, (∀ x ∈ A, k * x = x * k) → k ∈ A)
    {C : Set K} (hC : C ⊆ centSet A) {y f₀ f₁ f₀' f₁' : K}
    (hf₀ : f₀ ∈ Subgroup.closure C) (hf₁ : f₁ ∈ Subgroup.closure C) (hf₀' : f₀' ∈ Subgroup.closure C)
    (hf₁' : f₁' ∈ Subgroup.closure C) (hy₀ : y * f₀ = f₀' * y) (hy₁ : y * f₁ = f₁' * y)
    (hcen : ∀ k : K, k * f₀ = f₀ * k → k * f₁ = f₁ * k → k = 1)
    (hgen : Subgroup.closure (C ∪ {y}) = ⊤) : PlaneOK A := by
  right
  refine ⟨fun N hNH hN2 hHN => eq_bot_of_le_closure_centSet hp hp2 hAc hAp hnorm hcent hNH hN2 hHN,
    fun α hα => ?_⟩
  rw [eq_one_of_fix hC hf₀ hf₁ hf₀' hf₁' hy₀ hy₁ hcen hgen hα, orderOf_one]
  exact odd_one

end Spor

end CFSG.LocalAnalysis.UniquenessCase.UCK
