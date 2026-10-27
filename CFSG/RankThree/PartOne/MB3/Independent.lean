module

public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionRank

public section

namespace CFSG.RankThree.PartOne.MB3

open Subgroup CFSG CFSG.Assembly.RankThreeEven

variable {G : Type} [Group G]

@[expose] def powHom (q : ℕ) [NeZero q] (g : G) (hg : g ^ q = 1) :
    Multiplicative (ZMod q) →* G where
  toFun x := g ^ (Multiplicative.toAdd x).val
  map_one' := by rw [toAdd_one, ZMod.val_zero, pow_zero]
  map_mul' x y := by rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ hg, pow_add]

theorem four_le_localRank_of_independent [Finite G] {q : ℕ} (hq : q.Prime) {g₀ g₁ g₂ g₃ : G}
    (h₀ : g₀ ^ q = 1) (h₁ : g₁ ^ q = 1) (h₂ : g₂ ^ q = 1) (h₃ : g₃ ^ q = 1)
    (c₀₁ : Commute g₀ g₁) (c₀₂ : Commute g₀ g₂) (c₀₃ : Commute g₀ g₃) (c₁₂ : Commute g₁ g₂)
    (c₁₃ : Commute g₁ g₃) (c₂₃ : Commute g₂ g₃)
    (hind : ∀ a b c d : ℕ, g₀ ^ a * g₁ ^ b * g₂ ^ c * g₃ ^ d = 1 →
      q ∣ a ∧ q ∣ b ∧ q ∣ c ∧ q ∣ d)
    {U : Subgroup G} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (n₀ : g₀ ∈ normalizer (U : Set G)) (n₁ : g₁ ∈ normalizer (U : Set G))
    (n₂ : g₂ ∈ normalizer (U : Set G)) (n₃ : g₃ ∈ normalizer (U : Set G)) :
    4 ≤ localRank q G := by
  have : NeZero q := ⟨hq.ne_zero⟩
  set M := Multiplicative (ZMod q) with hM
  let f₀ := powHom q g₀ h₀
  let f₁ := powHom q g₁ h₁
  let f₂ := powHom q g₂ h₂
  let f₃ := powHom q g₃ h₃
  have c23 : ∀ x y : M, Commute (f₂ x) (f₃ y) := fun x y => c₂₃.pow_pow _ _
  let f₂₃ := f₂.noncommCoprod f₃ c23
  have c1_23 : ∀ (x : M) (y : M × M), Commute (f₁ x) (f₂₃ y) := fun x y => by
    simp only [f₂₃, MonoidHom.noncommCoprod_apply]
    exact (c₁₂.pow_pow _ _).mul_right (c₁₃.pow_pow _ _)
  let f₁₂₃ := f₁.noncommCoprod f₂₃ c1_23
  have c0_123 : ∀ (x : M) (y : M × M × M), Commute (f₀ x) (f₁₂₃ y) := fun x y => by
    simp only [f₁₂₃, f₂₃, MonoidHom.noncommCoprod_apply]
    exact (c₀₁.pow_pow _ _).mul_right ((c₀₂.pow_pow _ _).mul_right (c₀₃.pow_pow _ _))
  let Φ := f₀.noncommCoprod f₁₂₃ c0_123
  have hΦ : ∀ y : M × M × M × M, Φ y =
      g₀ ^ (Multiplicative.toAdd y.1).val * (g₁ ^ (Multiplicative.toAdd y.2.1).val *
        (g₂ ^ (Multiplicative.toAdd y.2.2.1).val * g₃ ^ (Multiplicative.toAdd y.2.2.2).val)) :=
    fun y => rfl
  have hinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker, hΦ] at hy
    have hy' : g₀ ^ (Multiplicative.toAdd y.1).val * g₁ ^ (Multiplicative.toAdd y.2.1).val *
        g₂ ^ (Multiplicative.toAdd y.2.2.1).val * g₃ ^ (Multiplicative.toAdd y.2.2.2).val = 1 := by
      rw [← hy]
      simp only [mul_assoc]
    obtain ⟨d₀, d₁, d₂, d₃⟩ := hind _ _ _ _ hy'
    have key : ∀ z : M, q ∣ (Multiplicative.toAdd z).val → z = 1 := fun z hz => by
      have h0 : (Multiplicative.toAdd z).val = 0 :=
        Nat.eq_zero_of_dvd_of_lt hz (ZMod.val_lt _)
      rw [ZMod.val_eq_zero] at h0
      exact Multiplicative.toAdd.injective (by simpa using h0)
    obtain ⟨y₀, y₁, y₂, y₃⟩ := y
    simp only [Subgroup.mem_bot, Prod.mk_eq_one]
    exact ⟨key _ d₀, key _ d₁, key _ d₂, key _ d₃⟩
  refine Sec9Excl.le_localRank_of_normalizes hq.one_lt (U := U) (X := Φ.range) hU hU2
    inferInstance ?_ ?_ ?_
  · rintro _ ⟨y, rfl⟩
    have hy : y ^ q = 1 := by
      have : ∀ z : M, z ^ q = 1 := fun z => by
        have h := pow_card_eq_one' (G := M) (x := z)
        rwa [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h
      ext <;> simp [this]
    rw [← map_pow, hy, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, Nat.card_prod,
      Nat.card_prod]
    have hc : Nat.card M = q := by rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rw [hc]
    ring
  · rintro _ ⟨y, rfl⟩
    rw [hΦ]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ n₀ _) (Subgroup.mul_mem _ (Subgroup.pow_mem _ n₁ _)
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ n₂ _) (Subgroup.pow_mem _ n₃ _)))

end CFSG.RankThree.PartOne.MB3
