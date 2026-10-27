module

public import CFSG.GroupTheory.OddInversion

public section

namespace CFSG.Quasithin

open CFSG.OddInversion
open scoped commutatorElement Pointwise

variable {A : Type*} [Group A]

theorem eq_one_of_sq_eq_one_of_odd_card {H : Type*} [Group H] [Finite H] (hH : Odd (Nat.card H))
    {g : H} (hg : g ^ 2 = 1) : g = 1 := by
  have h1 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg
  have h2 : Odd (orderOf g) := Odd.of_dvd_nat hH (orderOf_dvd_natCard g)
  have : orderOf g = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at h2
      exact absurd h2 (by decide)
  exact orderOf_eq_one_iff.mp this

theorem eq_of_inverted_of_quot_mem {Y K : Subgroup A} (hY : Odd (Nat.card Y)) {r j₁ j₂ : A}
    (hj₁ : j₁ ∈ Y) (hj₂ : j₂ ∈ Y) (h₁ : r * j₁ * r⁻¹ = j₁⁻¹) (h₂ : r * j₂ * r⁻¹ = j₂⁻¹)
    (hK : ∀ k ∈ K, r * k * r⁻¹ = k) (hjK : j₁ * j₂⁻¹ ∈ K) : j₁ = j₂ := by
  have hk := hK _ hjK
  have e : r * (j₁ * j₂⁻¹) * r⁻¹ = j₁⁻¹ * j₂ := by
    calc r * (j₁ * j₂⁻¹) * r⁻¹ = (r * j₁ * r⁻¹) * (r * j₂ * r⁻¹)⁻¹ := by group
      _ = j₁⁻¹ * j₂ := by rw [h₁, h₂]; group
  rw [e] at hk
  have h3 : j₂ ^ 2 = j₁ ^ 2 := by
    calc j₂ ^ 2 = j₂ * j₂ := sq j₂
      _ = j₁ * (j₁⁻¹ * j₂) * j₂ := by group
      _ = j₁ * (j₁ * j₂⁻¹) * j₂ := by rw [hk]
      _ = j₁ * j₁ := by group
      _ = j₁ ^ 2 := (sq j₁).symm
  exact (sq_injOn hY hj₂ hj₁ h3).symm

theorem exists_fixed_mul_inverted {Y : Subgroup A} (hY : Odd (Nat.card Y)) {r : A}
    (hr : orderOf r = 2) (hrN : r ∈ Subgroup.normalizer (Y : Set A)) {y : A} (hy : y ∈ Y) :
    ∃ c ∈ Y, r * c * r⁻¹ = c ∧ ∃ j ∈ Y, r * j * r⁻¹ = j⁻¹ ∧ y = c * j := by
  obtain ⟨h1, -, -⟩ := odd_involution_product_decomposition hY hr hrN
  obtain ⟨⟨c, j⟩, ⟨hc, hj⟩, hcj⟩ := h1.surjOn hy
  obtain ⟨hcY, hcC⟩ := Subgroup.mem_inf.mp hc
  refine ⟨c, hcY, ?_, j, hj.1, hj.2, hcj.symm⟩
  have := Subgroup.mem_centralizer_singleton_iff.mp hcC
  rw [← this]
  group

theorem commutator_mul_left_eq {n y ρ : A} (hnρ : n * ρ = ρ * n) (hny : n * y = y * n)
    (hny' : n * (ρ * y⁻¹ * ρ⁻¹) = (ρ * y⁻¹ * ρ⁻¹) * n) : ⁅n * y, ρ⁆ = ⁅y, ρ⁆ := by
  have h1 : Commute n ρ := hnρ
  have h2 : Commute n y := hny
  have h3 : Commute n (ρ * y⁻¹ * ρ⁻¹) := hny'
  have hc : Commute n (y * (ρ * y⁻¹ * ρ⁻¹)) := h2.mul_right h3
  have e : ⁅n * y, ρ⁆ = n * (y * (ρ * y⁻¹ * ρ⁻¹)) * n⁻¹ := by
    simp only [commutatorElement_def]
    calc n * y * ρ * (n * y)⁻¹ * ρ⁻¹ = n * y * ρ * y⁻¹ * (n⁻¹ * ρ⁻¹) := by group
      _ = n * y * ρ * y⁻¹ * (ρ⁻¹ * n⁻¹) := by rw [h1.inv_inv.eq]
      _ = n * (y * (ρ * y⁻¹ * ρ⁻¹)) * n⁻¹ := by group
  rw [e, hc.eq]
  simp only [commutatorElement_def]
  group

variable {B : Type*} [Group B]

theorem commutator_le_closure_inverted (π : A →* B) {X R Y : Subgroup A} {r : A}
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hRcomm : ∀ ρ ∈ R, ρ * r = r * ρ)
    (hRN : ∀ ρ ∈ R, ∀ n ∈ X ⊓ π.ker, ρ * n = n * ρ)
    (hYX : Y ≤ X) (hRY : R ≤ Subgroup.normalizer (Y : Set A)) (hYodd : Odd (Nat.card Y))
    (hYC : ∀ y ∈ Y, ∀ n ∈ X ⊓ π.ker, n * y = y * n)
    (hDY : ∀ d ∈ X ⊓ Subgroup.centralizer ((X ⊓ π.ker : Subgroup A) : Set A),
      ∃ y ∈ Y, d * y⁻¹ ∈ π.ker)
    (hinv : ∀ y ∈ Y, π (r * y * r⁻¹ * y) = 1) (hπodd : Odd (Nat.card (Y.map π))) :
    ⁅X ⊓ Subgroup.centralizer ((X ⊓ π.ker : Subgroup A) : Set A), R⁆ ≤
      Subgroup.closure {j | j ∈ Y ∧ r * j * r⁻¹ = j⁻¹} := by
  set N : Subgroup A := X ⊓ π.ker with hN
  set J : Set A := {j | j ∈ Y ∧ r * j * r⁻¹ = j⁻¹} with hJ
  rw [Subgroup.commutator_le]
  intro d hd ρ hρ
  have hρN : ∀ n ∈ N, n * ρ = ρ * n := fun n hn => (hRN ρ hρ n hn).symm
  have key : ∀ n ∈ N, ∀ y ∈ Y, ⁅n * y, ρ⁆ = ⁅y, ρ⁆ := by
    intro n hn y hy
    refine commutator_mul_left_eq (hρN n hn) (hYC y hy n hn) ?_
    have hy' : ρ * y⁻¹ * ρ⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hRY hρ) y⁻¹).mp (Y.inv_mem hy)
    exact hYC _ hy' n hn
  obtain ⟨y, hyY, hdy⟩ := hDY d hd
  have hn : d * y⁻¹ ∈ N := ⟨X.mul_mem (Subgroup.mem_inf.mp hd).1 (X.inv_mem (hYX hyY)), hdy⟩
  have hd_eq : d = (d * y⁻¹) * y := by group
  obtain ⟨c, hcY, hcr, j, hjY, hjr, hyc⟩ := exists_fixed_mul_inverted hYodd hr2 (hRY hr) hyY
  have hcN : c ∈ N := by
    refine ⟨hYX hcY, ?_⟩
    have h1 := hinv c hcY
    rw [hcr, map_mul] at h1
    have hmem : π c ∈ Y.map π := Subgroup.mem_map_of_mem π hcY
    have h2 : (⟨π c, hmem⟩ : ↥(Y.map π)) ^ 2 = 1 := by
      apply Subtype.ext
      simpa [sq] using h1
    have : Finite ↥(Y.map π) :=
      Nat.finite_of_card_ne_zero (fun h => by rw [h] at hπodd; exact Nat.not_odd_zero hπodd)
    have := eq_one_of_sq_eq_one_of_odd_card hπodd h2
    exact congrArg Subtype.val this
  have hjρ : ρ * j * ρ⁻¹ ∈ J := by
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hRY hρ) j).mp hjY, ?_⟩
    have := hRcomm ρ hρ
    calc r * (ρ * j * ρ⁻¹) * r⁻¹ = (r * ρ) * j * (r * ρ)⁻¹ := by group
      _ = (ρ * r) * j * (ρ * r)⁻¹ := by rw [this]
      _ = ρ * (r * j * r⁻¹) * ρ⁻¹ := by group
      _ = (ρ * j * ρ⁻¹)⁻¹ := by rw [hjr]; group
  have hjJ : j ∈ J := ⟨hjY, hjr⟩
  rw [hd_eq, key _ hn y hyY, hyc, key c hcN j hjY]
  have e : ⁅j, ρ⁆ = j * (ρ * j * ρ⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure hjJ)
    (Subgroup.inv_mem _ (Subgroup.subset_closure hjρ))

end CFSG.Quasithin
