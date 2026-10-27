module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.H13.NQS13410C

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pow_conj_mem {A B : Subgroup G} {x a : G} (hAB : A ≤ normalizer (B : Set G))
    (hxB : x ∈ normalizer (B : Set G)) (hdA : x * a * x⁻¹ * a⁻¹ ∈ A)
    (he : x * (x * a * x⁻¹ * a⁻¹) * x⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ ∈ B) (n : ℕ) :
    x ^ n * a * (x ^ n)⁻¹ * a⁻¹ * ((x * a * x⁻¹ * a⁻¹) ^ n)⁻¹ ∈ B := by
  obtain ⟨d, hd⟩ : ∃ d, x * a * x⁻¹ * a⁻¹ = d := ⟨_, rfl⟩
  rw [hd] at hdA he ⊢
  have hsub : ∀ n : ℕ, (x * d * x⁻¹) ^ n * (d ^ n)⁻¹ ∈ B := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e1 : (x * d * x⁻¹) ^ (n + 1) * (d ^ (n + 1))⁻¹ =
          ((x * d * x⁻¹) ^ n * (d ^ n)⁻¹) * (d ^ n * (x * d * x⁻¹ * d⁻¹) * (d ^ n)⁻¹) := by
        rw [pow_succ, pow_succ]
        group
      rw [e1]
      exact mul_mem ih ((mem_normalizer_iff.mp (hAB (pow_mem hdA n)) _).mp he)
  induction n with
  | zero => simp
  | succ n ih =>
    have e1 : x ^ (n + 1) * a * (x ^ (n + 1))⁻¹ * a⁻¹ =
        x * (x ^ n * a * (x ^ n)⁻¹ * a⁻¹) * x⁻¹ * d := by
      rw [← hd, pow_succ]
      group
    have e2 : x * (x ^ n * a * (x ^ n)⁻¹ * a⁻¹) * x⁻¹ * d * (d ^ (n + 1))⁻¹ =
        (x * (x ^ n * a * (x ^ n)⁻¹ * a⁻¹ * (d ^ n)⁻¹) * x⁻¹) *
          ((x * d * x⁻¹) ^ n * (d ^ n)⁻¹) := by
      rw [conj_pow, pow_succ]
      group
    rw [e1, e2]
    exact mul_mem ((mem_normalizer_iff.mp hxB _).mp ih) (hsub n)

omit [Finite G] in
theorem mem_of_unipotent {A B C : Subgroup G} {x : G} {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1)
    (hA2 : IsPGroup 2 ↥A) (hCA : C ≤ A) (hAB : A ≤ normalizer (B : Set G))
    (hxB : x ∈ normalizer (B : Set G)) (h1 : ∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ C)
    (h2 : ∀ c ∈ C, x * c * x⁻¹ * c⁻¹ ∈ B) {a : G} (ha : a ∈ A) :
    x * a * x⁻¹ * a⁻¹ ∈ B := by
  have hdC := h1 a ha
  have hP := pow_conj_mem hAB hxB (hCA hdC) (h2 _ hdC) m
  rw [hxm, inv_one, mul_one, one_mul, mul_inv_cancel] at hP
  have hP' : (x * a * x⁻¹ * a⁻¹) ^ m ∈ B := by
    have := inv_mem hP
    rwa [one_mul, inv_inv] at this
  obtain ⟨s, hs⟩ := hA2 ⟨_, hCA hdC⟩
  exact mem_of_pow_odd_mem (by simpa using congrArg Subtype.val hs) hm hP'

theorem exists_noncentral_chief {X : Subgroup G} {x : G} {m : ℕ} (hxX : x ∈ X) (hm : Odd m)
    (hxm : x ^ m = 1) : ∀ (n : ℕ) (A B : Subgroup G), Nat.card ↥A - Nat.card ↥B ≤ n →
    IsPGroup 2 ↥A → A ≤ X → B ≤ A → X ≤ normalizer (A : Set G) →
    X ≤ normalizer (B : Set G) → (∃ a ∈ A, x * a * x⁻¹ * a⁻¹ ∉ B) →
    ∃ A' B' : Subgroup G, B ≤ B' ∧ A' ≤ A ∧ IsChiefFactorOf X A' B' ∧ ¬ ⁅A', X⁆ ≤ B' := by
  intro n
  induction n with
  | zero =>
    intro A B hn hA2 hAX hBA hXA hXB ⟨a, ha, hab⟩
    exfalso
    have hBA' : B = A := eq_of_le_of_card_ge hBA (by omega)
    apply hab
    rw [hBA']
    exact mul_mem ((mem_normalizer_iff.mp (hXA hxX) a).mp ha) (inv_mem ha)
  | succ n ih =>
    intro A B hn hA2 hAX hBA hXA hXB ⟨a, ha, hab⟩
    have hxa : x * a * x⁻¹ * a⁻¹ ∈ A :=
      mul_mem ((mem_normalizer_iff.mp (hXA hxX) a).mp ha) (inv_mem ha)
    have hnc : ∀ {A' B' : Subgroup G}, (∃ a ∈ A', x * a * x⁻¹ * a⁻¹ ∉ B') → ¬ ⁅A', X⁆ ≤ B' := by
      rintro A' B' ⟨a', ha', hab'⟩ h
      apply hab'
      have h1 : ⁅a', x⁆ ∈ ⁅A', X⁆ := commutator_mem_commutator ha' hxX
      have h2 := inv_mem (h h1)
      rw [commutatorElement_def] at h2
      have e : (a' * x * a'⁻¹ * x⁻¹)⁻¹ = x * a' * x⁻¹ * a'⁻¹ := by group
      rwa [e] at h2
    by_cases hch : IsChiefFactorOf X A B
    · exact ⟨A, B, le_rfl, le_rfl, hch, hnc ⟨a, ha, hab⟩⟩
    have hBA' : B < A := lt_of_le_of_ne hBA fun h => hab (h ▸ hxa)
    obtain ⟨C, hBC, hCA, hXC⟩ : ∃ C : Subgroup G, B < C ∧ C < A ∧
        X ≤ normalizer (C : Set G) := by
      by_contra hno
      push Not at hno
      exact hch ⟨hBA', hXA, hXB, fun C h1 h2 h3 => hno C h1 h2 h3⟩
    have hcBC : Nat.card ↥B < Nat.card ↥C := by
      by_contra h
      exact hBC.ne (eq_of_le_of_card_ge hBC.le (by omega))
    have hcCA : Nat.card ↥C < Nat.card ↥A := by
      by_contra h
      exact hCA.ne (eq_of_le_of_card_ge hCA.le (by omega))
    have hcA : Nat.card ↥C ≤ Nat.card ↥A := card_le_of_le hCA.le
    by_cases hC : ∃ c ∈ C, x * c * x⁻¹ * c⁻¹ ∉ B
    · obtain ⟨A', B', hBB', hA'C, h1, h2⟩ := ih C B (by omega) (hA2.to_le hCA.le)
        (hCA.le.trans hAX) hBC.le hXC hXB hC
      exact ⟨A', B', hBB', hA'C.trans hCA.le, h1, h2⟩
    · push Not at hC
      have hA : ∃ a ∈ A, x * a * x⁻¹ * a⁻¹ ∉ C := by
        by_contra hno
        push Not at hno
        exact hab (mem_of_unipotent hm hxm hA2 hCA.le (hAX.trans hXB) (hXB hxX) hno hC ha)
      obtain ⟨A', B', hCB', hA'A, h1, h2⟩ := ih A C (by omega) hA2 hAX hCA.le hXA hXC hA
      exact ⟨A', B', hBC.le.trans hCB', hA'A, h1, h2⟩

end CFSG.Quasithin.H13.NQS134
