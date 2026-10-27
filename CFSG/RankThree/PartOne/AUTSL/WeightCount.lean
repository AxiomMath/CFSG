module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartOne.AUTSL

open scoped _root_.Classical

section FixedPoints

variable {B : Type*} [CommGroup B] [Finite B]

theorem norm_eq_one_of_order_three (hB : Nat.card B = 25) (g : MulAut B) (hg3 : g ^ 3 = 1)
    (hg1 : g ≠ 1) (b : B) : b * g b * g (g b) = 1 := by
  have : Fintype B := Fintype.ofFinite B
  have h3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let f : Function.End B := fun x => g x
  have hf : f ^ 3 ^ 1 = 1 := by
    rw [pow_one]
    funext x
    have h3x : g (g (g x)) = x := by
      have h := congrArg (fun φ : MulAut B => φ x) hg3
      simpa [pow_succ] using h
    exact h3x
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf
  let F : Subgroup B := (g : B →* B).eqLocus (MonoidHom.id B)
  have hFcard : Fintype.card f.fixedPoints = Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    apply Fintype.card_congr
    exact Equiv.refl _
  rw [hFcard, ← Nat.card_eq_fintype_card, hB] at hmod
  have hdvd : Nat.card F ∣ 25 := hB ▸ Subgroup.card_subgroup_dvd_card F
  have h25 : Nat.card F = 1 := by
    have hd : Nat.card F ∣ 5 ^ 2 := by simpa using hdvd
    obtain ⟨k, hk, hkF⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp hd
    interval_cases k
    · simpa using hkF
    · exfalso
      rw [hkF] at hmod
      simp [Nat.ModEq] at hmod
    · exfalso
      have hFtop : F = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [hkF, hB]
        norm_num
      apply hg1
      ext x
      have hx : x ∈ F := by rw [hFtop]; trivial
      exact hx
  have hFbot : F = ⊥ := Subgroup.card_eq_one.mp h25
  have hn : b * g b * g (g b) ∈ F := by
    show g (b * g b * g (g b)) = b * g b * g (g b)
    have h3b : g (g (g b)) = b := by
      have h := congrArg (fun φ : MulAut B => φ b) hg3
      simpa [pow_succ] using h
    rw [map_mul, map_mul, h3b]
    calc g b * g (g b) * b = b * (g b * g (g b)) := mul_comm _ _
      _ = b * g b * g (g b) := (mul_assoc _ _ _).symm
  rw [hFbot] at hn
  exact hn

end FixedPoints

section Twist

variable {B X : Type*} [CommGroup B] [CommGroup X]

@[expose] def twist (θ : B ≃* B) (m : ℕ) (χ : B →* X) : B →* X :=
  (χ.comp (θ.toMonoidHom.comp θ.toMonoidHom)) ^ m

theorem twist_apply (θ : B ≃* B) (m : ℕ) (χ : B →* X) (b : B) :
    twist θ m χ b = χ (θ (θ b)) ^ m := by
  simp [twist, MonoidHom.pow_apply]

theorem theta_cube (θ : B ≃* B) (hθ : ∀ b, b * θ b * θ (θ b) = 1) (b : B) :
    θ (θ (θ b)) = b := by
  have h2 := congrArg θ (hθ b)
  rw [map_mul, map_mul, map_one] at h2
  have h1 := hθ b
  have h3 : θ b * θ (θ b) * b = 1 := by
    calc θ b * θ (θ b) * b = b * θ b * θ (θ b) := by ac_rfl
      _ = 1 := h1
  have h4 : θ b * θ (θ b) * θ (θ (θ b)) = 1 := h2
  have h5 : θ b * θ (θ b) * θ (θ (θ b)) = θ b * θ (θ b) * b := h4.trans h3.symm
  exact mul_left_cancel h5

theorem twist_twist_apply (θ : B ≃* B) (hθ : ∀ b, b * θ b * θ (θ b) = 1) (m : ℕ)
    (χ : B →* X) (b : B) : twist θ m (twist θ m χ) b = χ (θ b) ^ (m * m) := by
  have h4 : θ (θ (θ (θ b))) = θ b := theta_cube θ hθ (θ b)
  rw [twist_apply, twist_apply, h4, ← pow_mul]

theorem twist_three (θ : B ≃* B) (hθ : ∀ b, b * θ b * θ (θ b) = 1) (m : ℕ) (χ : B →* X) :
    twist θ m (twist θ m (twist θ m χ)) = χ ^ (m * m * m) := by
  ext b
  rw [twist_apply, twist_twist_apply θ hθ, theta_cube θ hθ, MonoidHom.pow_apply, ← pow_mul]

theorem twist_pow (θ : B ≃* B) (m a : ℕ) (χ : B →* X) :
    twist θ m (χ ^ a) = twist θ m χ ^ a := by
  ext b
  simp only [twist_apply, MonoidHom.pow_apply]
  rw [← pow_mul, ← pow_mul, mul_comm]

theorem twist_one (θ : B ≃* B) (m : ℕ) : twist θ m (1 : B →* X) = 1 := by
  ext b
  simp [twist_apply]

theorem pow_fourth_eq_self {x : X} (hx : x ^ 5 = 1) {m : ℕ} (hm : ¬ 5 ∣ m) : x ^ (m ^ 4) = x := by
  have h : m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by omega
  have h1 : m ^ 4 % 5 = 1 := by
    rcases h with h | h | h | h <;> simp [Nat.pow_mod, h]
  rw [pow_eq_pow_mod (m ^ 4) hx, h1, pow_one]

theorem chi_pow_five (hB5 : ∀ b : B, b ^ 5 = 1) (χ : B →* X) (b : B) : χ b ^ 5 = 1 := by
  rw [← map_pow, hB5, map_one]

theorem eq_one_of_comp_eq_pow (hB5 : ∀ b : B, b ^ 5 = 1) (ψ : B ≃* B)
    (hψ : ∀ b, b * ψ b * ψ (ψ b) = 1) (l : ℕ) (χ : B →* X)
    (h : ∀ b, χ (ψ b) = χ b ^ l) : χ = 1 := by
  ext b
  have h1 : χ b * χ (ψ b) * χ (ψ (ψ b)) = 1 := by
    rw [← map_mul, ← map_mul, hψ, map_one]
  have h2 : χ (ψ (ψ b)) = χ b ^ (l * l) := by
    rw [h, h, ← pow_mul]
  rw [h, h2] at h1
  have h3 : χ b ^ (1 + l + l * l) = 1 := by
    rw [pow_add, pow_add, pow_one]
    exact h1
  have h5 : χ b ^ 5 = 1 := chi_pow_five hB5 χ b
  have hcop : Nat.Coprime 5 (1 + l + l * l) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_five]
    have hl : l % 5 = 0 ∨ l % 5 = 1 ∨ l % 5 = 2 ∨ l % 5 = 3 ∨ l % 5 = 4 := by omega
    rcases hl with hl | hl | hl | hl | hl <;>
      simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, hl]
  have := pow_gcd_eq_one.mpr ⟨h5, h3⟩
  rw [hcop.gcd_eq_one, pow_one] at this
  rw [MonoidHom.one_apply]
  exact this

theorem char_pow_inj (hB5 : ∀ b : B, b ^ 5 = 1) {n : ℕ} (hn : ¬ 5 ∣ n) {χ χ' : B →* X}
    (h : χ ^ n = χ' ^ n) : χ = χ' := by
  ext b
  have h1 : χ b ^ n = χ' b ^ n := by
    simpa [MonoidHom.pow_apply] using congrArg (fun φ : B →* X => φ b) h
  have h2 : χ b ^ (n * n ^ 3) = χ' b ^ (n * n ^ 3) := by
    rw [pow_mul, pow_mul, h1]
  have h4 : n * n ^ 3 = n ^ 4 := by ring
  rw [h4, pow_fourth_eq_self (chi_pow_five hB5 χ b) hn,
    pow_fourth_eq_self (chi_pow_five hB5 χ' b) hn] at h2
  exact h2

theorem pow_ne_self (hB5 : ∀ b : B, b ^ 5 = 1) {χ : B →* X} (hχ : χ ≠ 1) {n : ℕ}
    (hn : n % 5 ≠ 1) : χ ^ n ≠ χ := by
  intro h
  apply hχ
  by_contra hne
  have hne' : ∃ b, χ b ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hne (by ext b; simpa using hall b)
  obtain ⟨b, hb⟩ := hne'
  have hb5 := chi_pow_five hB5 χ b
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hord : orderOf (χ b) = 5 := orderOf_eq_prime hb5 hb
  have h1 : χ b ^ n = χ b ^ 1 := by
    rw [pow_one]
    simpa [MonoidHom.pow_apply] using congrArg (fun φ : B →* X => φ b) h
  rw [pow_eq_pow_iff_modEq, hord] at h1
  exact hn (by simpa [Nat.ModEq] using h1)

section Eigen

variable (hB5 : ∀ b : B, b ^ 5 = 1) (θ : B ≃* B) (hθ : ∀ b, b * θ b * θ (θ b) = 1) (m : ℕ)
  (hm : ¬ 5 ∣ m)
include hB5 hθ hm

theorem twist_ne_pow {χ : B →* X} (hχ : χ ≠ 1) (l : ℕ) : twist θ m χ ≠ χ ^ l := by
  intro h
  apply hχ
  let ψ : B ≃* B := θ.trans θ
  have hψ : ∀ b, b * ψ b * ψ (ψ b) = 1 := by
    intro b
    have h4 : θ (θ (θ (θ b))) = θ b := theta_cube θ hθ (θ b)
    show b * θ (θ b) * θ (θ (θ (θ b))) = 1
    rw [h4]
    calc b * θ (θ b) * θ b = b * θ b * θ (θ b) := by ac_rfl
      _ = 1 := hθ b
  refine eq_one_of_comp_eq_pow hB5 ψ hψ (l * (m * m * m)) χ fun b => ?_
  have h1 : χ (θ (θ b)) ^ m = χ b ^ l := by
    simpa [twist_apply, MonoidHom.pow_apply] using congrArg (fun φ : B →* X => φ b) h
  have h2 : χ (θ (θ b)) = (χ (θ (θ b)) ^ m) ^ (m * m * m) := by
    rw [← pow_mul]
    have : m * (m * m * m) = m ^ 4 := by ring
    rw [this, pow_fourth_eq_self (chi_pow_five hB5 χ _) hm]
  show χ (θ (θ b)) = χ b ^ (l * (m * m * m))
  rw [h2, h1, ← pow_mul]

theorem twist_twist_ne_pow {χ : B →* X} (hχ : χ ≠ 1) (l : ℕ) :
    twist θ m (twist θ m χ) ≠ χ ^ l := by
  intro h
  apply hχ
  refine eq_one_of_comp_eq_pow hB5 θ hθ (l * (m * m) ^ 3) χ fun b => ?_
  have h1 : χ (θ b) ^ (m * m) = χ b ^ l := by
    simpa [twist_twist_apply θ hθ, MonoidHom.pow_apply] using
      congrArg (fun φ : B →* X => φ b) h
  have h2 : χ (θ b) = (χ (θ b) ^ (m * m)) ^ ((m * m) ^ 3) := by
    rw [← pow_mul]
    have : m * m * (m * m) ^ 3 = m ^ 4 * m ^ 4 := by ring
    rw [this, pow_mul, pow_fourth_eq_self (chi_pow_five hB5 χ _) hm,
      pow_fourth_eq_self (chi_pow_five hB5 χ _) hm]
  rw [h2, h1, ← pow_mul]

theorem twist_injective {χ χ' : B →* X} (h : twist θ m χ = twist θ m χ') : χ = χ' := by
  have h1 : χ ^ m = χ' ^ m := by
    ext b
    have := congrArg (fun φ : B →* X => φ (θ b)) h
    simpa [twist_apply, theta_cube θ hθ, MonoidHom.pow_apply] using this
  exact char_pow_inj hB5 hm h1

theorem twist_eq_one {χ : B →* X} (h : twist θ m χ = 1) : χ = 1 :=
  twist_injective hB5 θ hθ m hm (h.trans (twist_one θ m).symm)

end Eigen

end Twist

section Weights

variable {B X ι : Type*} [CommGroup B] [CommGroup X] [Fintype ι]

@[expose] noncomputable def mult (f : ι → (B →* X)) (χ : B →* X) : ℕ :=
  (Finset.univ.filter fun i => f i = χ).card

theorem mult_pos_iff (f : ι → (B →* X)) (χ : B →* X) : 0 < mult f χ ↔ χ ∈ Set.range f := by
  unfold mult
  rw [Finset.card_pos]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, by simp⟩

theorem sum_mult_le (f : ι → (B →* X)) (s : Finset (B →* X)) :
    ∑ χ ∈ s, mult f χ ≤ Fintype.card ι := by
  unfold mult
  have h := Finset.card_eq_sum_card_fiberwise (f := f)
    (s := Finset.univ.filter fun i => f i ∈ s) (t := s)
    (fun i hi => (Finset.mem_filter.mp hi).2)
  calc ∑ χ ∈ s, (Finset.univ.filter fun i => f i = χ).card
      = ∑ χ ∈ s, ((Finset.univ.filter fun i => f i ∈ s).filter fun i => f i = χ).card := by
        refine Finset.sum_congr rfl fun χ hχ => ?_
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          exact ⟨h ▸ hχ, h⟩
        · intro h
          exact h.2
    _ = (Finset.univ.filter fun i => f i ∈ s).card := h.symm
    _ ≤ Fintype.card ι := Finset.card_le_univ _

theorem two_le_mult_of_ne (f : ι → (B →* X)) {i j : ι} (hij : i ≠ j) (h : f i = f j) :
    2 ≤ mult f (f i) := by
  unfold mult
  have : 1 < (Finset.univ.filter fun k => f k = f i).card := by
    rw [Finset.one_lt_card_iff]
    exact ⟨i, j, by simp, by simp [h], hij⟩
  omega

theorem card_five {α : Type*} [DecidableEq α] {a b c d e : α} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d)
    (hce : c ≠ e) (hde : d ≠ e) : ({a, b, c, d, e} : Finset α).card = 5 := by
  simp [Finset.card_insert_of_notMem, hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde]

theorem five_le_card_range (f : ι → (B →* X)) {a b c d e : B →* X} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d)
    (hce : c ≠ e) (hde : d ≠ e) (ha : a ∈ Set.range f) (hb : b ∈ Set.range f)
    (hc : c ∈ Set.range f) (hd : d ∈ Set.range f) (he : e ∈ Set.range f) :
    5 ≤ Fintype.card ι := by
  have h1 : ({a, b, c, d, e} : Finset (B →* X)) ⊆ Finset.univ.image f := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨i, rfl⟩ := ha; simp
    · obtain ⟨i, rfl⟩ := hb; simp
    · obtain ⟨i, rfl⟩ := hc; simp
    · obtain ⟨i, rfl⟩ := hd; simp
    · obtain ⟨i, rfl⟩ := he; simp
  have h2 := Finset.card_le_card h1
  rw [card_five hab hac had hae hbc hbd hbe hcd hce hde] at h2
  exact h2.trans (Finset.card_image_le.trans (by simp))

theorem sum_three_le (f : ι → (B →* X)) {a b c : B →* X} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : mult f a + mult f b + mult f c ≤ Fintype.card ι := by
  have h := sum_mult_le f {a, b, c}
  rwa [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc, ← add_assoc] at h

theorem sum_four_le (f : ι → (B →* X)) {a b c d : B →* X} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    mult f a + mult f b + mult f c + mult f d ≤ Fintype.card ι := by
  have h := sum_mult_le f {a, b, c, d}
  rwa [Finset.sum_insert (by simp [hab, hac, had]), Finset.sum_insert (by simp [hbc, hbd]),
    Finset.sum_pair hcd, ← add_assoc, ← add_assoc] at h

theorem chars_pow_five (hB5 : ∀ b : B, b ^ 5 = 1) (χ : B →* X) : χ ^ 5 = 1 := by
  ext b
  rw [MonoidHom.pow_apply, chi_pow_five hB5 χ b, MonoidHom.one_apply]

theorem weight_lemma (hB5 : ∀ b : B, b ^ 5 = 1) (θ : B ≃* B)
    (hθ : ∀ b, b * θ b * θ (θ b) = 1) (f : ι → (B →* X)) (hcard : Fintype.card ι = 4) (m : ℕ)
    (hm : ¬ 5 ∣ m) (hf1 : ∃ i, f i ≠ 1) (H : ∀ χ, mult f χ ≤ mult f (twist θ m χ)) :
    m % 5 = 1 ∧ Function.Injective f ∧
      ∃ χ₀ : B →* X, χ₀ ≠ 1 ∧ χ₀ ∈ Set.range f ∧ twist θ m χ₀ ∈ Set.range f ∧
        twist θ m (twist θ m χ₀) ∈ Set.range f := by
  classical
  obtain ⟨i₀, hi₀⟩ := hf1
  have hrange : ∀ χ, χ ∈ Set.range f → twist θ m χ ∈ Set.range f := fun χ hχ =>
    (mult_pos_iff f _).1 (lt_of_lt_of_le ((mult_pos_iff f χ).2 hχ) (H χ))
  have hne1 : ∀ χ : B →* X, χ ≠ 1 → twist θ m χ ≠ 1 := fun χ hχ h =>
    hχ (twist_eq_one hB5 θ hθ m hm h)
  have hχ₀r : f i₀ ∈ Set.range f := ⟨i₀, rfl⟩
  have hv1r := hrange _ hχ₀r
  have hv2r := hrange _ hv1r
  have hv1ne : twist θ m (f i₀) ≠ 1 := hne1 _ hi₀
  have h01 : f i₀ ≠ twist θ m (f i₀) := fun h =>
    twist_ne_pow hB5 θ hθ m hm hi₀ 1 (by rw [pow_one]; exact h.symm)
  have h02 : f i₀ ≠ twist θ m (twist θ m (f i₀)) := fun h =>
    twist_twist_ne_pow hB5 θ hθ m hm hi₀ 1 (by rw [pow_one]; exact h.symm)
  have h12 : twist θ m (f i₀) ≠ twist θ m (twist θ m (f i₀)) := fun h =>
    twist_ne_pow hB5 θ hθ m hm hv1ne 1 (by rw [pow_one]; exact h.symm)
  have hm1 : m % 5 = 1 := by
    by_contra hmne
    have hmod : (m * m * m) % 5 ≠ 1 ∧ ¬ 5 ∣ m * m * m := by
      have h : m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by omega
      rcases h with h | h | h | h
      · exact absurd h hmne
      all_goals
        refine ⟨by simp [Nat.mul_mod, h], ?_⟩
        intro hd
        have := Nat.mod_eq_zero_of_dvd hd
        simp [Nat.mul_mod, h] at this
    obtain ⟨hn1, hm3'⟩ := hmod
    have hm4 : m * m * m * m = m ^ 4 := by ring
    have hv1five : twist θ m (f i₀) ^ 5 = 1 := chars_pow_five hB5 _
    have hv3 : twist θ m (twist θ m (twist θ m (f i₀))) = f i₀ ^ (m * m * m) :=
      twist_three θ hθ m (f i₀)
    have hv3r : f i₀ ^ (m * m * m) ∈ Set.range f := hv3 ▸ hrange _ hv2r
    have hv4 : twist θ m (f i₀ ^ (m * m * m)) = twist θ m (f i₀) ^ (m * m * m) :=
      twist_pow θ m _ (f i₀)
    have hv4r : twist θ m (f i₀) ^ (m * m * m) ∈ Set.range f := hv4 ▸ hrange _ hv3r
    have hc5 : Fintype.card ι ≥ 5 := by
      refine five_le_card_range f (a := f i₀) (b := twist θ m (f i₀))
        (c := twist θ m (twist θ m (f i₀))) (d := f i₀ ^ (m * m * m))
        (e := twist θ m (f i₀) ^ (m * m * m)) h01 h02 ?_ ?_ h12 ?_ ?_ ?_ ?_ ?_ hχ₀r hv1r hv2r hv3r
        hv4r
      · exact (pow_ne_self hB5 hi₀ hn1).symm
      · intro h
        apply twist_ne_pow hB5 θ hθ m hm hi₀ m
        have h' : (twist θ m (f i₀) ^ (m * m * m)) ^ m = f i₀ ^ m := by rw [← h]
        rw [← pow_mul, show m * m * m * m = m ^ 4 by ring,
          pow_fourth_eq_self hv1five hm] at h'
        exact h'
      · intro h
        exact twist_ne_pow hB5 θ hθ m hm hi₀ (m * m * m) h
      · intro h
        exact (pow_ne_self hB5 hv1ne hn1) h.symm
      · intro h
        exact twist_twist_ne_pow hB5 θ hθ m hm hi₀ (m * m * m) h
      · intro h
        exact twist_ne_pow hB5 θ hθ m hm hv1ne (m * m * m) h
      · intro h
        exact h01 (char_pow_inj hB5 hm3' h)
    omega
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have h2 : 2 ≤ mult f (f i) := two_le_mult_of_ne f hne hij
    by_cases hχ : f i = 1
    · rw [hχ] at h2
      have hm0 : 1 ≤ mult f (f i₀) := (mult_pos_iff _ _).2 hχ₀r
      have hm1' : mult f (f i₀) ≤ mult f (twist θ m (f i₀)) := H _
      have hm2' : mult f (twist θ m (f i₀)) ≤ mult f (twist θ m (twist θ m (f i₀))) := H _
      have hs := sum_four_le f (a := (1 : B →* X)) (b := f i₀) (c := twist θ m (f i₀))
        (d := twist θ m (twist θ m (f i₀))) hi₀.symm hv1ne.symm (hne1 _ hv1ne).symm h01 h02 h12
      omega
    · have hbne : twist θ m (f i) ≠ 1 := hne1 _ hχ
      have hH1 : mult f (f i) ≤ mult f (twist θ m (f i)) := H _
      have hH2 : mult f (twist θ m (f i)) ≤ mult f (twist θ m (twist θ m (f i))) := H _
      have hs := sum_three_le f (a := f i) (b := twist θ m (f i))
        (c := twist θ m (twist θ m (f i)))
        (fun h => twist_ne_pow hB5 θ hθ m hm hχ 1 (by rw [pow_one]; exact h.symm))
        (fun h => twist_twist_ne_pow hB5 θ hθ m hm hχ 1 (by rw [pow_one]; exact h.symm))
        (fun h => twist_ne_pow hB5 θ hθ m hm hbne 1 (by rw [pow_one]; exact h.symm))
      omega
  exact ⟨hm1, hinj, f i₀, hi₀, hχ₀r, hv1r, hv2r⟩

theorem scalar_lemma (hB5 : ∀ b : B, b ^ 5 = 1) (θ : B ≃* B)
    (hθ : ∀ b, b * θ b * θ (θ b) = 1) (f : ι → (B →* X)) (hcard : Fintype.card ι = 4) (m : ℕ)
    (hm : ¬ 5 ∣ m) {χ₀ : B →* X} (hχ₀ : χ₀ ≠ 1) (h0 : χ₀ ∈ Set.range f)
    (h1 : twist θ m χ₀ ∈ Set.range f) (h2 : twist θ m (twist θ m χ₀) ∈ Set.range f) (m' : ℕ)
    (hm' : ¬ 5 ∣ m') (H' : ∀ χ, mult f χ ≤ mult f (χ ^ m')) : m' % 5 = 1 := by
  classical
  by_contra hne
  have hrange : ∀ χ, χ ∈ Set.range f → χ ^ m' ∈ Set.range f := fun χ hχ =>
    (mult_pos_iff f _).1 (lt_of_lt_of_le ((mult_pos_iff f χ).2 hχ) (H' χ))
  have hv1ne : twist θ m χ₀ ≠ 1 := fun h => hχ₀ (twist_eq_one hB5 θ hθ m hm h)
  have hv1five : twist θ m χ₀ ^ 5 = 1 := chars_pow_five hB5 _
  have hχ₀five : χ₀ ^ 5 = 1 := chars_pow_five hB5 _
  have h01 : χ₀ ≠ twist θ m χ₀ := fun h =>
    twist_ne_pow hB5 θ hθ m hm hχ₀ 1 (by rw [pow_one]; exact h.symm)
  have h02 : χ₀ ≠ twist θ m (twist θ m χ₀) := fun h =>
    twist_twist_ne_pow hB5 θ hθ m hm hχ₀ 1 (by rw [pow_one]; exact h.symm)
  have h12 : twist θ m χ₀ ≠ twist θ m (twist θ m χ₀) := fun h =>
    twist_ne_pow hB5 θ hθ m hm hv1ne 1 (by rw [pow_one]; exact h.symm)
  have hc5 : 5 ≤ Fintype.card ι := by
    refine five_le_card_range f (a := χ₀) (b := twist θ m χ₀) (c := twist θ m (twist θ m χ₀))
      (d := χ₀ ^ m') (e := twist θ m χ₀ ^ m') h01 h02 ?_ ?_ h12 ?_ ?_ ?_ ?_ ?_ h0 h1 h2
      (hrange _ h0) (hrange _ h1)
    · exact (pow_ne_self hB5 hχ₀ hne).symm
    · intro h
      apply twist_ne_pow hB5 θ hθ m hm hχ₀ (m' ^ 3)
      have h' : (twist θ m χ₀ ^ m') ^ (m' ^ 3) = χ₀ ^ (m' ^ 3) := by rw [← h]
      rw [← pow_mul, show m' * m' ^ 3 = m' ^ 4 by ring, pow_fourth_eq_self hv1five hm'] at h'
      exact h'
    · intro h
      exact twist_ne_pow hB5 θ hθ m hm hχ₀ m' h
    · intro h
      exact (pow_ne_self hB5 hv1ne hne) h.symm
    · intro h
      exact twist_twist_ne_pow hB5 θ hθ m hm hχ₀ m' h
    · intro h
      exact twist_ne_pow hB5 θ hθ m hm hv1ne m' h
    · intro h
      exact h01 (char_pow_inj hB5 hm' h)
  omega

end Weights


end CFSG.RankThree.PartOne.AUTSL
