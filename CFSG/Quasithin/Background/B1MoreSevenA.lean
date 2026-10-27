module

public import CFSG.Quasithin.Background.B1MoreChief
public import CFSG.Assembly.QuasithinDefs

public section

namespace CFSG.Quasithin

open CFSG.Open

macro "cgroup" : tactic =>
  `(tactic| (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one]; abel))

variable {G : Type*} [Group G]

theorem le_normalizer_of_conj {X Y : Subgroup G} (h : ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y) :
    X ≤ Subgroup.normalizer (Y : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h x hx y hy, fun hy => ?_⟩
  have := h x⁻¹ (X.inv_mem hx) _ hy
  simpa [mul_assoc] using this

theorem conj_mem_commutator {H A : Subgroup G} {b : G} (hb : b ∈ A) {x : G} (hx : x ∈ ⁅H, A⁆) :
    b * x * b⁻¹ ∈ ⁅H, A⁆ := by
  rw [Subgroup.commutator_def] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨h, hh, c, hc, rfl⟩ := hg
    have e : b * (h * c * h⁻¹ * c⁻¹) * b⁻¹ =
        (h * b * h⁻¹ * b⁻¹)⁻¹ * (h * (b * c) * h⁻¹ * (b * c)⁻¹) := by group
    rw [commutatorElement_def, e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨h, hh, b, hb, rfl⟩))
      (Subgroup.subset_closure ⟨h, hh, b * c, A.mul_mem hb hc, rfl⟩)
  | one => simp
  | mul x y _ _ hx hy => simpa [mul_assoc] using Subgroup.mul_mem _ hx hy
  | inv x _ hx => simpa [mul_assoc] using Subgroup.inv_mem _ hx

theorem conj_mem_of_commutator_eq {H A : Subgroup G} (h : ⁅H, A⁆ = H) {b : G} (hb : b ∈ A)
    {y : G} (hy : y ∈ H) : b * y * b⁻¹ ∈ H := by
  have hy' : y ∈ ⁅H, A⁆ := by rw [h]; exact hy
  have := conj_mem_commutator (H := H) hb hy'
  rwa [h] at this

theorem le_normalizer_of_commutator_eq {H A : Subgroup G} (h : ⁅H, A⁆ = H) :
    A ≤ Subgroup.normalizer (H : Set G) :=
  le_normalizer_of_conj fun _ hx _ hy => conj_mem_of_commutator_eq h hx hy

theorem commutator_pow_mem {H K N : Subgroup G} {b : G} (hNH : N ≤ H)
    (hKn : ∀ g ∈ H, ∀ k ∈ K, g * k * g⁻¹ ∈ K) (hcent : ⁅N, H⁆ ≤ K)
    (hbN : ∀ h ∈ H, h * b * h⁻¹ * b⁻¹ ∈ N) {x : G} (hx : x ∈ H) (j : ℕ) :
    ∃ κ ∈ K, x ^ j * b * (x ^ j)⁻¹ * b⁻¹ = (x * b * x⁻¹ * b⁻¹) ^ j * κ := by
  induction j with
  | zero => exact ⟨1, K.one_mem, by simp⟩
  | succ j ih =>
    obtain ⟨κ, hκ, hκeq⟩ := ih
    set d := x * b * x⁻¹ * b⁻¹ with hd
    have hdN : d ∈ N := hbN x hx
    have hdH : d ∈ H := hNH hdN
    have hxj : x ^ j ∈ H := H.pow_mem hx j
    have hκ₁ : (d)⁻¹ * (x ^ j * d * (x ^ j)⁻¹) ∈ K := by
      have := hcent (Subgroup.commutator_mem_commutator (N.inv_mem hdN) hxj)
      have e : (d)⁻¹ * (x ^ j * d * (x ^ j)⁻¹) = d⁻¹ * x ^ j * d⁻¹⁻¹ * (x ^ j)⁻¹ := by group
      rw [e]
      exact this
    set κ₁ := d⁻¹ * (x ^ j * d * (x ^ j)⁻¹) with hκ₁def
    have hdj : (d ^ j)⁻¹ * κ₁ * (d ^ j)⁻¹⁻¹ ∈ K :=
      hKn _ (H.inv_mem (H.pow_mem hdH j)) _ hκ₁
    refine ⟨(d ^ j)⁻¹ * κ₁ * d ^ j * κ, K.mul_mem (by simpa using hdj) hκ, ?_⟩
    have e1 : x ^ (j + 1) * b * (x ^ (j + 1))⁻¹ * b⁻¹ =
        (x ^ j * d * (x ^ j)⁻¹) * (x ^ j * b * (x ^ j)⁻¹ * b⁻¹) := by
      rw [hd, pow_succ]
      group
    rw [e1, hκeq, pow_succ']
    have e2 : x ^ j * d * (x ^ j)⁻¹ = d * κ₁ := by rw [hκ₁def]; group
    rw [e2]
    group

theorem commutator_mem_of_central_section {H K N : Subgroup G} {b : G}
    (hH : oTwoUpper H = H) (hNH : N ≤ H) (hKn : ∀ g ∈ H, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hN2 : ∀ x ∈ N, ∃ k : ℕ, x ^ 2 ^ k ∈ K) (hcent : ⁅N, H⁆ ≤ K)
    (hbN : ∀ h ∈ H, h * b * h⁻¹ * b⁻¹ ∈ N) : ∀ h ∈ H, h * b * h⁻¹ * b⁻¹ ∈ K := by
  let S : Subgroup G :=
    { carrier := {h | h ∈ H ∧ h * b * h⁻¹ * b⁻¹ ∈ K}
      one_mem' := ⟨H.one_mem, by simp⟩
      mul_mem' := fun {x y} hx hy => by
        refine ⟨H.mul_mem hx.1 hy.1, ?_⟩
        have e : x * y * b * (x * y)⁻¹ * b⁻¹ =
            (x * (y * b * y⁻¹ * b⁻¹) * x⁻¹) * (x * b * x⁻¹ * b⁻¹) := by group
        rw [e]
        exact K.mul_mem (hKn x hx.1 _ hy.2) hx.2
      inv_mem' := fun {x} hx => by
        refine ⟨H.inv_mem hx.1, ?_⟩
        have e : x⁻¹ * b * x⁻¹⁻¹ * b⁻¹ = x⁻¹ * (x * b * x⁻¹ * b⁻¹)⁻¹ * x⁻¹⁻¹ := by group
        rw [e]
        exact hKn x⁻¹ (H.inv_mem hx.1) _ (K.inv_mem hx.2) }
  have hHS : H ≤ S := by
    calc H = oTwoUpper H := hH.symm
      _ ≤ S := by
        refine (Subgroup.closure_le S).mpr fun x hx => ?_
        refine ⟨hx.1, ?_⟩
        obtain ⟨κ, hκ, hκeq⟩ := commutator_pow_mem hNH hKn hcent hbN hx.1 (orderOf x)
        rw [pow_orderOf_eq_one] at hκeq
        have h1 : (x * b * x⁻¹ * b⁻¹) ^ orderOf x ∈ K := by
          have : (x * b * x⁻¹ * b⁻¹) ^ orderOf x = κ⁻¹ := by
            rw [eq_inv_iff_mul_eq_one]
            simpa using hκeq.symm
          rw [this]
          exact K.inv_mem hκ
        obtain ⟨k, hk⟩ := hN2 _ (hbN x hx.1)
        have hcop : IsCoprime ((orderOf x : ℕ) : ℤ) ((2 ^ k : ℕ) : ℤ) :=
          Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hx.2))
        obtain ⟨a, c, hac⟩ := hcop
        set g := x * b * x⁻¹ * b⁻¹ with hg
        have h2 : g = (g ^ orderOf x) ^ a * (g ^ 2 ^ k) ^ c := by
          rw [← zpow_natCast, ← zpow_natCast g (2 ^ k), ← zpow_mul, ← zpow_mul, ← zpow_add]
          have : (orderOf x : ℤ) * a + ((2 ^ k : ℕ) : ℤ) * c = 1 := by
            rw [mul_comm (orderOf x : ℤ), mul_comm (((2 ^ k : ℕ)) : ℤ)]; exact hac
          rw [this, zpow_one]
        rw [h2]
        exact K.mul_mem (K.zpow_mem h1 a) (K.zpow_mem hk c)
  intro h hh
  exact (hHS hh).2

end CFSG.Quasithin
