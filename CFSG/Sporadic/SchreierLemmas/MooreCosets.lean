module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic.Group

public section

namespace CFSG.Sporadic.SchreierLemmas

structure IsMooreFamily {G : Type*} [Group G] (M : ℕ) (x : ℕ → G) : Prop where
  cube_one : x 1 ^ 3 = 1
  sq_eq_one : ∀ j, 2 ≤ j → j ≤ M → x j ^ 2 = 1
  cube_adjacent : ∀ j, 2 ≤ j → j ≤ M → (x (j - 1) * x j) ^ 3 = 1
  sq_distant : ∀ i j, 1 ≤ i → i + 2 ≤ j → j ≤ M → (x i * x j) ^ 2 = 1

variable {G : Type*} [Group G] {M : ℕ} {x : ℕ → G}

namespace IsMooreFamily

theorem mono (hx : IsMooreFamily M x) {M' : ℕ} (h : M' ≤ M) : IsMooreFamily M' x :=
  ⟨hx.cube_one, fun j h2 hj => hx.sq_eq_one j h2 (hj.trans h),
    fun j h2 hj => hx.cube_adjacent j h2 (hj.trans h),
    fun i j hi hij hj => hx.sq_distant i j hi hij (hj.trans h)⟩

theorem inv_eq (hx : IsMooreFamily M x) {j : ℕ} (h2 : 2 ≤ j) (hj : j ≤ M) : (x j)⁻¹ = x j :=
  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hx.sq_eq_one j h2 hj)

theorem mul_self_one (hx : IsMooreFamily M x) : x 1 * x 1 = (x 1)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← pow_three']; exact hx.cube_one)

theorem commute (hx : IsMooreFamily M x) {i j : ℕ} (h2 : 2 ≤ i) (hij : i + 2 ≤ j)
    (hj : j ≤ M) : x i * x j = x j * x i := by
  have h := hx.sq_distant i j (by omega) hij hj
  rw [sq] at h
  have e := eq_inv_of_mul_eq_one_left h
  rw [e, mul_inv_rev, hx.inv_eq (by omega) hj, hx.inv_eq h2 (by omega)]

theorem mul_one_eq (hx : IsMooreFamily M x) {j : ℕ} (h3 : 3 ≤ j) (hj : j ≤ M) :
    x j * x 1 = (x 1)⁻¹ * x j := by
  have h := hx.sq_distant 1 j le_rfl h3 hj
  rw [sq] at h
  calc x j * x 1 = (x 1)⁻¹ * ((x 1 * x j) * (x 1 * x j)) * (x j)⁻¹ := by group
    _ = (x 1)⁻¹ * x j := by rw [h, mul_one, hx.inv_eq (by omega) hj]

theorem mul_one_inv_eq (hx : IsMooreFamily M x) {j : ℕ} (h3 : 3 ≤ j) (hj : j ≤ M) :
    x j * (x 1)⁻¹ = x 1 * x j := by
  have e := hx.mul_one_eq h3 hj
  calc x j * (x 1)⁻¹ = x 1 * ((x 1)⁻¹ * x j) * (x 1)⁻¹ := by group
    _ = x 1 * (x j * x 1) * (x 1)⁻¹ := by rw [e]
    _ = x 1 * x j := by group

theorem braid (hx : IsMooreFamily M x) {j : ℕ} (h3 : 3 ≤ j) (hj : j ≤ M) :
    x (j - 1) * x j * x (j - 1) = x j * x (j - 1) * x j := by
  have h := hx.cube_adjacent j (by omega) hj
  have ha := hx.inv_eq (j := j - 1) (by omega) (by omega)
  have hb := hx.inv_eq (j := j) (by omega) hj
  rw [_root_.pow_three] at h
  calc x (j - 1) * x j * x (j - 1) =
      (x (j - 1) * x j * (x (j - 1) * x j * (x (j - 1) * x j))) *
        ((x j)⁻¹ * (x (j - 1))⁻¹ * (x j)⁻¹) := by group
    _ = x j * x (j - 1) * x j := by rw [h, one_mul, ha, hb]

theorem braid_one (hx : IsMooreFamily M x) (h2 : 2 ≤ M) :
    x 2 * x 1 * x 2 = (x 1)⁻¹ * x 2 * (x 1)⁻¹ := by
  have h := hx.cube_adjacent 2 le_rfl h2
  have hb := hx.inv_eq (j := 2) le_rfl h2
  rw [show (2 - 1 : ℕ) = 1 from rfl, _root_.pow_three] at h
  calc x 2 * x 1 * x 2 = (x 1)⁻¹ * (x 1 * x 2 * (x 1 * x 2 * (x 1 * x 2))) * (x 2)⁻¹ *
        (x 1)⁻¹ := by group
    _ = (x 1)⁻¹ * x 2 * (x 1)⁻¹ := by rw [h, mul_one, hb]

theorem braid_one_inv (hx : IsMooreFamily M x) (h2 : 2 ≤ M) :
    x 2 * (x 1)⁻¹ * x 2 = x 1 * x 2 * x 1 := by
  have e := hx.braid_one h2
  have hb := hx.inv_eq (j := 2) le_rfl h2
  have := congrArg (·⁻¹) e
  simp only [mul_inv_rev, inv_inv, hb] at this
  rw [mul_assoc, this, ← mul_assoc]

end IsMooreFamily

@[expose] def mooreProd (x : ℕ → G) (a b : ℕ) : G :=
  ((List.range' a (b + 1 - a)).map x).prod

theorem mooreProd_of_lt {a b : ℕ} (h : b < a) : mooreProd x a b = 1 := by
  rw [mooreProd, show b + 1 - a = 0 by omega]
  rfl

theorem mooreProd_cons {a b : ℕ} (h : a ≤ b) : mooreProd x a b = x a * mooreProd x (a + 1) b := by
  rw [mooreProd, mooreProd, show b + 1 - a = (b + 1 - (a + 1)) + 1 by omega, List.range'_succ,
    List.map_cons, List.prod_cons]

theorem IsMooreFamily.commute_mooreProd (hx : IsMooreFamily M x) {j : ℕ} (h2 : 2 ≤ j) :
    ∀ d a b, b + 1 - a = d → j + 2 ≤ a → b ≤ M →
      x j * mooreProd x a b = mooreProd x a b * x j := by
  intro d
  induction d with
  | zero =>
    intro a b hd _ _
    rw [mooreProd_of_lt (by omega), mul_one, one_mul]
  | succ d ih =>
    intro a b hd ha hb
    rw [mooreProd_cons (by omega), ← mul_assoc, hx.commute h2 ha (by omega), mul_assoc,
      ih (a + 1) b (by omega) (by omega) hb, mul_assoc]

theorem IsMooreFamily.one_mul_mooreProd (hx : IsMooreFamily M x) :
    ∀ d a b, b + 1 - a = d → 3 ≤ a → b ≤ M → ∀ s ∈ ({x 1, (x 1)⁻¹} : Set G),
      ∃ s' ∈ ({x 1, (x 1)⁻¹} : Set G), s * mooreProd x a b = mooreProd x a b * s' := by
  intro d
  induction d with
  | zero =>
    intro a b hd _ _ s hs
    exact ⟨s, hs, by rw [mooreProd_of_lt (by omega), mul_one, one_mul]⟩
  | succ d ih =>
    intro a b hd ha hb s hs
    obtain ⟨s₁, hs₁, e⟩ : ∃ s₁ ∈ ({x 1, (x 1)⁻¹} : Set G), s * x a = x a * s₁ := by
      rcases hs with rfl | rfl
      · exact ⟨(x 1)⁻¹, Or.inr rfl, (hx.mul_one_inv_eq ha (by omega)).symm⟩
      · exact ⟨x 1, Or.inl rfl, (hx.mul_one_eq ha (by omega)).symm⟩
    obtain ⟨s', hs', e'⟩ := ih (a + 1) b (by omega) (by omega) hb s₁ hs₁
    refine ⟨s', hs', ?_⟩
    rw [mooreProd_cons (by omega), ← mul_assoc, e, mul_assoc, e', mul_assoc]

theorem IsMooreFamily.mul_mooreProd_shift (hx : IsMooreFamily M x) {j b : ℕ} (hjb : j ≤ b)
    (hb : b ≤ M) : ∀ d a, j - 1 - a = d → 2 ≤ a → a + 1 ≤ j →
      x j * mooreProd x a b = mooreProd x a b * x (j - 1) := by
  intro d
  induction d with
  | zero =>
    intro a hd ha haj
    obtain rfl : a = j - 1 := by omega
    have e1 : mooreProd x (j - 1) b = x (j - 1) * x j * mooreProd x (j + 1) b := by
      rw [mooreProd_cons (by omega), show j - 1 + 1 = j by omega, mooreProd_cons hjb, mul_assoc]
    have hc := hx.commute_mooreProd (j := j - 1) (by omega) _ (j + 1) b rfl (by omega) hb
    rw [e1, ← mul_assoc, ← mul_assoc, ← hx.braid (by omega) (by omega), mul_assoc, hc,
      ← mul_assoc]
  | succ d ih =>
    intro a hd ha haj
    rw [mooreProd_cons (by omega), ← mul_assoc,
      ← hx.commute (i := a) (j := j) ha (by omega) (by omega), mul_assoc,
      ih (a + 1) (by omega) (by omega) (by omega), mul_assoc]

@[expose] def mooreRep (x : ℕ → G) (M : ℕ) : Bool ⊕ Fin M → G
  | .inl true => x 1 * mooreProd x 2 M
  | .inl false => (x 1)⁻¹ * mooreProd x 2 M
  | .inr i => mooreProd x (i + 2) M

theorem IsMooreFamily.exists_mul_mooreRep_eq (hx : IsMooreFamily M x) {j : ℕ} (hj1 : 1 ≤ j)
    (hjM : j ≤ M) (k : Bool ⊕ Fin M) :
    ∃ k', ∃ h ∈ Subgroup.closure (x '' Set.Icc 1 (M - 1)),
      x j * mooreRep x M k = mooreRep x M k' * h := by
  set H := Subgroup.closure (x '' Set.Icc 1 (M - 1))
  have hmem : ∀ i, 1 ≤ i → i ≤ M - 1 → x i ∈ H := fun i h1 h2 =>
    Subgroup.subset_closure ⟨i, ⟨h1, h2⟩, rfl⟩
  have hQ : 2 ≤ M → ∀ s ∈ ({x 1, (x 1)⁻¹} : Set G), s ∈ H := by
    intro hM s hs
    rcases hs with rfl | rfl
    · exact hmem 1 le_rfl (by omega)
    · exact inv_mem (hmem 1 le_rfl (by omega))
  have hP2 : 2 ≤ M → mooreProd x 2 M = x 2 * mooreProd x 3 M := fun hM => mooreProd_cons hM
  rcases k with (_ | _) | ⟨i, hi⟩
  ·
    simp only [mooreRep]
    rcases Nat.lt_trichotomy j 2 with hj | rfl | hj
    · obtain rfl : j = 1 := by omega
      exact ⟨.inr ⟨0, by omega⟩, 1, one_mem _, by simp⟩
    · obtain ⟨s', hs', e⟩ := hx.one_mul_mooreProd _ 3 M rfl le_rfl le_rfl (x 1) (Or.inl rfl)
      refine ⟨.inl true, s', hQ hjM s' hs', ?_⟩
      simp only
      rw [hP2 hjM, ← mul_assoc, ← mul_assoc, hx.braid_one_inv hjM, mul_assoc, mul_assoc, e,
        ← mul_assoc, ← mul_assoc, mul_assoc (x 1)]
    · refine ⟨.inl true, x (j - 1), hmem (j - 1) (by omega) (by omega), ?_⟩
      simp only
      rw [← mul_assoc, hx.mul_one_inv_eq hj hjM, mul_assoc,
        hx.mul_mooreProd_shift (j := j) (b := M) hjM le_rfl _ 2 rfl le_rfl (by omega),
        mul_assoc]
  ·
    simp only [mooreRep]
    rcases Nat.lt_trichotomy j 2 with hj | rfl | hj
    · obtain rfl : j = 1 := by omega
      exact ⟨.inl false, 1, one_mem _, by
        simp only [mul_one]
        rw [← mul_assoc, hx.mul_self_one]⟩
    · obtain ⟨s', hs', e⟩ := hx.one_mul_mooreProd _ 3 M rfl le_rfl le_rfl (x 1)⁻¹ (Or.inr rfl)
      refine ⟨.inl false, s', hQ hjM s' hs', ?_⟩
      simp only
      rw [hP2 hjM, ← mul_assoc, ← mul_assoc, hx.braid_one hjM, mul_assoc, mul_assoc, e,
        ← mul_assoc, ← mul_assoc, mul_assoc ((x 1)⁻¹)]
    · refine ⟨.inl false, x (j - 1), hmem (j - 1) (by omega) (by omega), ?_⟩
      simp only
      rw [← mul_assoc, hx.mul_one_eq hj hjM, mul_assoc,
        hx.mul_mooreProd_shift (j := j) (b := M) hjM le_rfl _ 2 rfl le_rfl (by omega),
        mul_assoc]
  ·
    simp only [mooreRep]
    rcases Nat.lt_or_ge j 2 with hj | hj
    · obtain rfl : j = 1 := by omega
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact ⟨.inl true, 1, one_mem _, by simp⟩
      · obtain ⟨s', hs', e⟩ := hx.one_mul_mooreProd _ (i + 2) M rfl (by omega) le_rfl (x 1)
          (Or.inl rfl)
        exact ⟨.inr ⟨i, hi⟩, s', hQ (by omega) s' hs', by simp only; exact e⟩
    · rcases Nat.lt_or_ge (j + 1) (i + 2) with hji | hji
      ·
        exact ⟨.inr ⟨i, hi⟩, x j, hmem j (by omega) (by omega), by
          simp only
          exact hx.commute_mooreProd hj _ (i + 2) M rfl (by omega) le_rfl⟩
      · rcases Nat.lt_or_ge j (i + 2) with hji' | hji'
        ·
          refine ⟨.inr ⟨i - 1, by omega⟩, 1, one_mem _, ?_⟩
          simp only [mul_one]
          rw [show i - 1 + 2 = j by omega, mooreProd_cons hjM, show j + 1 = i + 2 by omega]
        · rcases Nat.lt_or_ge (i + 2) j with hij | hij
          ·
            exact ⟨.inr ⟨i, hi⟩, x (j - 1), hmem (j - 1) (by omega) (by omega), by
              simp only
              exact hx.mul_mooreProd_shift hjM le_rfl _ (i + 2) rfl (by omega) (by omega)⟩
          ·
            obtain rfl : j = i + 2 := by omega
            refine ⟨.inr ⟨i + 1, by omega⟩, 1, one_mem _, ?_⟩
            simp only [mul_one]
            rw [mooreProd_cons hjM, ← mul_assoc, ← sq, hx.sq_eq_one _ hj hjM, one_mul]

theorem finite_closure_and_card_le_of_moore :
    ∀ (M : ℕ) (x : ℕ → G), IsMooreFamily M x →
      Finite (Subgroup.closure (x '' Set.Icc 1 M)) ∧
        Nat.card (Subgroup.closure (x '' Set.Icc 1 M)) ≤ (M + 2).factorial / 2 := by
  intro M
  induction M with
  | zero =>
    intro x _
    rw [Set.Icc_eq_empty (by omega), Set.image_empty, Subgroup.closure_empty, Subgroup.card_bot]
    exact ⟨inferInstance, by simp⟩
  | succ M ih =>
    intro x hx
    set H := Subgroup.closure (x '' Set.Icc 1 M)
    obtain ⟨hHfin, hH⟩ := ih x (hx.mono (Nat.le_succ M))
    set K := Subgroup.closure (x '' Set.Icc 1 (M + 1))
    have hHK : H ≤ K := Subgroup.closure_mono (Set.image_mono (Set.Icc_subset_Icc le_rfl
      (Nat.le_succ M)))
    have hgen : ∀ i, 1 ≤ i → i ≤ M + 1 → x i ∈ K := fun i h1 h2 =>
      Subgroup.subset_closure ⟨i, ⟨h1, h2⟩, rfl⟩
    have hprod : ∀ d a, M + 1 + 1 - a = d → 1 ≤ a → mooreProd x a (M + 1) ∈ K := by
      intro d
      induction d with
      | zero => intro a hd _; rw [mooreProd_of_lt (by omega)]; exact one_mem _
      | succ d ihd =>
        intro a hd ha
        rw [mooreProd_cons (by omega)]
        exact mul_mem (hgen a ha (by omega)) (ihd (a + 1) (by omega) (by omega))
    have hrep : ∀ k, mooreRep x (M + 1) k ∈ K := by
      rintro ((_ | _) | ⟨i, hi⟩)
      · exact mul_mem (inv_mem (hgen 1 le_rfl (by omega))) (hprod _ 2 rfl (by omega))
      · exact mul_mem (hgen 1 le_rfl (by omega)) (hprod _ 2 rfl (by omega))
      · exact hprod _ (i + 2) rfl (by omega)
    have hcov : ∀ g ∈ K, ∃ k, ∃ h ∈ H, g = mooreRep x (M + 1) k * h := by
      have hstep : ∀ y ∈ x '' Set.Icc 1 (M + 1), ∀ g,
          (∃ k, ∃ h ∈ H, g = mooreRep x (M + 1) k * h) →
            ∃ k, ∃ h ∈ H, y * g = mooreRep x (M + 1) k * h := by
        rintro y ⟨j, ⟨hj1, hjM⟩, rfl⟩ g ⟨k, h, hh, rfl⟩
        obtain ⟨k', h', hh', e⟩ := hx.exists_mul_mooreRep_eq hj1 hjM k
        refine ⟨k', h' * h, H.mul_mem (by simpa using hh') hh, ?_⟩
        rw [← mul_assoc, e, mul_assoc]
      intro g hg
      induction hg using Subgroup.closure_induction_left with
      | one => exact ⟨.inr ⟨M, by omega⟩, 1, H.one_mem, by
          simp [mooreRep, mooreProd_of_lt (show M + 1 < M + 2 by omega)]⟩
      | mul_left y hy g _ ih => exact hstep y hy g ih
      | inv_mul_cancel y hy g _ ih =>
        obtain ⟨j, ⟨hj1, hjM⟩, rfl⟩ := hy
        rcases Nat.lt_or_ge j 2 with hj | hj
        · obtain rfl : j = 1 := by omega
          rw [← hx.mul_self_one, mul_assoc]
          exact hstep _ ⟨1, ⟨le_rfl, hjM⟩, rfl⟩ _ (hstep _ ⟨1, ⟨le_rfl, hjM⟩, rfl⟩ g ih)
        · rw [hx.inv_eq hj hjM]
          exact hstep _ ⟨j, ⟨hj1, hjM⟩, rfl⟩ g ih
    let f : (Bool ⊕ Fin (M + 1)) × H → K := fun p =>
      ⟨mooreRep x (M + 1) p.1 * p.2, K.mul_mem (hrep _) (hHK p.2.2)⟩
    have hf : Function.Surjective f := by
      rintro ⟨g, hg⟩
      obtain ⟨k, h, hh, rfl⟩ := hcov g hg
      exact ⟨(k, ⟨h, hh⟩), rfl⟩
    have hcard := Nat.card_le_card_of_surjective f hf
    refine ⟨Finite.of_surjective f hf, ?_⟩
    rw [Nat.card_prod, Nat.card_sum, Nat.card_eq_fintype_card (α := Bool),
      Nat.card_eq_fintype_card (α := Fin (M + 1)), Fintype.card_bool, Fintype.card_fin] at hcard
    have h2 : 2 ∣ (M + 2).factorial := Nat.dvd_factorial two_pos (by omega)
    calc Nat.card K ≤ (2 + (M + 1)) * Nat.card H := hcard
      _ ≤ (2 + (M + 1)) * ((M + 2).factorial / 2) := Nat.mul_le_mul_left _ hH
      _ = (M + 1 + 2).factorial / 2 := by
        have : (M + 1 + 2).factorial = (M + 3) * (M + 2).factorial := Nat.factorial_succ (M + 2)
        rw [this, Nat.mul_div_assoc _ h2, show 2 + (M + 1) = M + 3 by omega]

end CFSG.Sporadic.SchreierLemmas
